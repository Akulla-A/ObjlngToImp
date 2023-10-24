let tr_op: Objlng.binop -> Imp.binop = function
  | Add -> Add
  | Mul -> Mul
  | Lt -> Lt;;

(* Need two additional parameters:
    environment: variable names -> types
  user-defined structs: struct names -> contents types     
*)

let rec getIndex fBool l =
  let rec sub l fBool index =
    match l with
      | hd::tl -> 
        if fBool hd then
          index
        else
          sub tl fBool (index + 1)
      | [] -> failwith "Coulnd't find a index" in

  sub l fBool 0;;

let rec printType: Objlng.typ -> string = function
  | TClass n -> "Struct: " ^ n
  | TInt -> "Integer"
  | TBool -> "Boolean"
  | TVoid -> "Void"
  | TArray(e) -> "Array: " ^ (printType e);;

let translate_program (p: Objlng.program) =
  (* Pré-traitement, ajout des classes *)
  let tr_cdef (cdef: Objlng.class_def) (prog: Objlng.program): Objlng.program =
    {
      Objlng.globals = ((cdef.name ^ "_descr"), TInt) :: prog.globals;
      Objlng.functions = List.fold_left (fun acc (fdef: Objlng.function_def): Objlng.function_def list -> 
        {
          name = (cdef.name ^ "_" ^ fdef.name);
          params = ("this", TClass(cdef.name)) :: fdef.params;
          locals = fdef.locals;
          code = fdef.code;
          return = fdef.return;
        } :: acc
      ) prog.functions (cdef.methods);
      Objlng.classes = prog.classes;
    } in

  let p = List.fold_left (fun prog c -> tr_cdef c prog) p p.classes in

  (* 
    Ajout de la variable global pour le instanceof
     On doit stocker l'addresse et faire une boucle dessus, pour éviter un code horrible
     L'autre option était des if dans des if
  *)

  let (p: Objlng.program) = {
    classes = p.classes;
    functions = p.functions;
    globals = ("_instanceof_ptr", TInt) :: p.globals
  } in

  let getClassByName n =
    let findStruct = List.find_opt (fun (blob: Objlng.class_def) -> blob.name = n) p.classes in
    if(Option.is_none findStruct) then 
      failwith ("Class " ^ n ^ " does not exists");
    Option.get findStruct in

  let rec sizeOfStruct (s: Objlng.typ) =
    match s with
      | TClass s -> 
        let findStruct = getClassByName s in
  
        (*
        List.fold_left (fun field acc -> (sizeOfStruct field) + acc ) (Option.get findStruct).fields 0*)
        let sizeStruct = (List.length findStruct.fields) in
        let parent = findStruct.parent in
        let parentSize = (match parent with
          | None -> 0
          | Some n -> (sizeOfStruct (TClass n)) - 4) in
  
          sizeStruct * 4 + 4 + parentSize
        | _ -> 4 in

  let rec getClassAttrOffsetByName attrName className =
    let c = List.find (fun (blob: Objlng.class_def) -> blob.name = className) p.classes in
    try
      let index = getIndex (fun (argN, typ) -> attrName = argN) c.fields in

      index * 4 + (match c.parent with
        | None -> 0
        | Some n -> sizeOfStruct (TClass n)
      ) + 4
    with
      | _ -> (match c.parent with 
        | None -> failwith ("Class " ^ className ^ " and his parents does not have a attribute " ^ attrName)
        | Some n -> getClassAttrOffsetByName attrName n
      ) in

  let rec getClassAttrPairByName attrName className =
    let c = List.find (fun (blob: Objlng.class_def) -> blob.name = className) p.classes in
    let attr = List.find_opt (fun var -> 
      fst var = attrName  
    ) c.fields in

    if Option.is_some attr then
      Option.get attr
    else
      (match c.parent with
        | None -> failwith ("Class " ^ className ^ " and his parents does not have a attribute " ^ attrName)
        | Some n -> getClassAttrPairByName attrName n
      ) in

  let rec findMethodIndex (c: string) fName =
    let functionTbl = Hashtbl.create 20 in

    let rec findIndex (cName: string) fName =
      let c = getClassByName cName in

      let res = (match c.parent with
        | Some n -> findIndex n fName
        | None -> 0
      ) in

      if res = -1 then
        let flag = ref false in
        List.iter (fun (fDef: Objlng.function_def) ->
          if fDef.name = fName then
            flag := true
          else if (!flag = false) && fDef.name != "constructor" then
            Hashtbl.add functionTbl fDef.name true;
        ) c.methods;

        if !flag = true then
          Hashtbl.length functionTbl
        else
          -1 
      else
        res
      
      in

    findIndex c fName in

  let rec getAllClassMethodsIndex (c: string) =
    let functionTbl = Hashtbl.create 20 in

    let rec loop (cName: string) =
      let c = getClassByName cName in

      if Option.is_some c.parent then
        loop (Option.get c.parent);

      List.iter(fun (a: Objlng.function_def) ->
        if Option.is_none (Hashtbl.find_opt functionTbl a.name) && not (a.name = "constructor") then
          Hashtbl.add functionTbl a.name (Hashtbl.length functionTbl)
      ) c.methods in

    loop c;
    functionTbl in
    
  let rec type_expr env: Objlng.expression -> Objlng.typ = function
    | Cst n -> TInt
    | Bool b -> TBool
    | InstanceOf _ -> TBool
    | Var v -> 
      let var = Hashtbl.find_opt env v in
      if Option.is_none var then
        failwith ("Variable " ^ v ^ " is not declared in the env");

      Option.get var
    | Binop(op, e1, e2) -> if (op <> Lt) then TInt else TBool
    | Call(s, eList) ->
      let getFunc = List.find_opt (fun (f: Objlng.function_def) -> f.name = s) p.functions in

      if Option.is_none getFunc then
        failwith ("The function " ^ s ^ " does not exist");

      let getFunc = Option.get getFunc in

      List.iter2 (fun fParam expr ->
        if (type_expr env expr <> snd fParam) then
          failwith ("Calling a function with missmatching argument type. The missmatching argument is " ^ (fst fParam) ^ " of type " ^ (printType (snd fParam)) ^ ". The type of the given variable is " ^ (printType (type_expr env expr)))
      ) getFunc.params eList;

      getFunc.return
    | MCall(exp, s, eList) -> 
      let r = type_expr env exp in
      let structName = (match r with
        | TClass n -> n
        | _ -> failwith ("A Non-class expression is trying to call the function object " ^ s)) in
      let c = getClassByName structName in
      let f = List.find_opt (fun (f: Objlng.function_def) -> f.name = s) c.methods in

      if Option.is_none f then
        failwith ("Class " ^ structName ^ " does not exist");

      (*  Hashtbl.add cache l'ancienne valeur, ce qui est parfait pour nous, pas besoin de recréer une hashtbl*)
      Hashtbl.add env "this" r;

      List.iter2 (fun fParam expr ->
        if (type_expr env expr <> snd fParam) then
          failwith ("Calling a class function with missmatching argument type. The missmatching argument is " ^ (fst fParam) ^ " of type " ^ (printType (snd fParam)) ^ ". The type of the given variable is " ^ (printType (type_expr env expr)))
      ) (Option.get f).params eList;

      Hashtbl.remove env "this";

      (*? Vérifier appels pour parent si fonction manque ?*)

      (Option.get f).return
    | New(n, eList)->
      let c = getClassByName n in
      let constructor = List.find_opt (fun (f: Objlng.function_def) -> f.name = "constructor") c.methods in

      if Option.is_some constructor then
        List.iter2 (fun fParam expr ->
          if (type_expr env expr <> snd fParam) then
            failwith ("Calling the constructor of " ^ n ^ " with missmatching argument type. The missmatching argument is " ^ (fst fParam) ^ " of type " ^ (printType (snd fParam)) ^ ". The type of the given variable is " ^ (printType (type_expr env expr)))
        ) (Option.get constructor).params eList;

      TClass n
    | NewTab(typ, expr) ->
      let t = type_expr env expr in
      if(type_expr env expr <> TInt) then 
        failwith ("Creating a array with a size that is not a integer, type of the value used for the size: " ^ (printType t));

      TArray typ
    | This -> 
      let v = Hashtbl.find_opt env "this" in

      (match v with
        | None -> failwith ("Missing 'this' in env")
        | Some n -> n)
    | Read(n) -> type_mem env n
    and type_mem env = function
      | Atr(exp, argName) ->
        let eLeft = type_expr env exp in

        let n = (match eLeft with
          | TClass n -> n
          | _ -> ("Trying to read a class attribute on a variable that is not a class instance. Attribute Name: " ^ argName ^ ". Type of the variable: " ^ (printType eLeft))) in

        let foundArg = getClassAttrPairByName argName n in
        snd foundArg
      | Arr (e1, e2) -> 
        let eLeft = type_expr env e1 in

        if(type_expr env e2 <> TInt) then
          failwith ("Reading a array with a index that is not a int. Type of the value: " ^ (printType(type_expr env e2)));

        (match eLeft with
          | TArray(t) -> t
          | _ -> failwith ("Trying to read as an array a value that is not a array. Type of the value: " ^ (printType eLeft))) in

  let rec type_seq env s = List.iter (type_instr env) s
  and type_instr env: Objlng.instruction -> unit = function
    | Putchar e -> 
      if (type_expr env e <> TInt) then
        failwith ("Putchar argument is not a TInt. Type of the value : " ^ (printType (type_expr env e)));
    | Set (s, e2) -> 
      let varType = Hashtbl.find_opt env s in

      if Option.is_none varType then
        failwith ("Trying to set a variable " ^ s ^ " that does not exist");

      if (type_expr env e2 <> Option.get varType) then
        failwith ("Missmatch left and right part of Set. The left part is " ^ s ^ ", of type " ^ (printType (Option.get varType)) ^ ". Right part is a " ^ (printType (type_expr env e2)));
    | If (cond, sT, sF) -> 
      if (type_expr env cond <> TBool) then
        failwith ("The if condition is not a boolean. Type of the condition: " ^ (printType (type_expr env cond)));
    | While (e, seq) -> 
      if (type_expr env e <> TBool) then
        failwith ("While condition is not a boolean. Type of the condition: " ^ (printType (type_expr env e)));

    | Return (e) -> ();
    | Expr(e) -> ()
    | Write(e1, e2) -> 
      let tLeft = type_mem env e1 in
      let tRight = type_expr env e2 in
      if(tLeft <> tRight) then
        failwith ("Write on different types variables. Left type is " ^ (printType tLeft) ^ ". Right type is " ^ (printType tRight)) in

  (* Appeler type_expr avant *)
  let rec tr_expr env: Objlng.expression -> Imp.expression = function
    | Cst n -> Cst n
    | Bool b -> Bool b
    | Var v -> Var v
    | Binop(op, e1, e2) -> Binop(tr_op op, tr_expr env e1 , tr_expr env e2)
    (*| InstanceOf(e1, e2) ->
      Imp.Seq([
        Set(Var(("_instanceof_ptr", TInt)), Deref(tr_expr env e1));
        While(Binop(Lt, Var(("_instanceof_ptr", TInt)),
          [Expr (Var(e2 ^ "_descr"))]));
      ])*)
    | Call(s, eList) -> 
      let impCall = List.map (fun e -> tr_expr env e) eList in
      Call(s, impCall)
    | New(n, e) -> (* a changer *)
      Alloc(Cst (sizeOfStruct (TClass n)))
    | This -> 
      let v = Hashtbl.find_opt env "this" in

      if Option.is_none v then
        failwith ("Missing 'this' in env");

      Var("this")
    | NewTab(typ, e1) -> 
      Alloc(Binop(Mul, Cst (sizeOfStruct typ), tr_expr env e1))
    | Read(e) -> Deref(tr_mem env e)
    | MCall(exp, s, eList) ->
      let structName = (match type_expr env exp with
      | TClass n -> n
      | _ -> failwith "Calling a object function (" ^ s ^ ") on a expression that is not a class. Type of the exp: " ^ (printType (type_expr env exp))) in

      (*? Vérifier appels pour parent si fonction manque ?*)
      Hashtbl.add env "this" (type_expr env exp);
      let impCall = List.map (fun e -> tr_expr env e) (exp :: eList) in
      let classDescriptorAddr = Imp.Deref (tr_expr env exp) in
      Hashtbl.remove env "this";

      DCall(
        Deref(Binop(Add, classDescriptorAddr, Cst((findMethodIndex structName s + 1) * 4))), 
        impCall
      )
  and tr_mem env: Objlng.mem -> Imp.expression = function
    | Atr(e1, attrName) -> 
      let e1expr = type_expr env e1 in
      let structName = (match e1expr with
        | TClass n -> n
        | _ -> failwith "Trying to get the attribute " ^ attrName ^ " on a value that is not a class (This is a " ^ (printType e1expr) ^ ").") in

      Binop(Add, tr_expr env e1, Cst(getClassAttrOffsetByName attrName structName))
    | Arr(e1, e2) -> Binop(Add, tr_expr env e1, Binop(Mul, tr_expr env e2, Cst 4))
  in

  let rec tr_seq env s = List.map (
    tr_instr env
  ) s

  and tr_instr env: Objlng.instruction -> Imp.instruction = function
    | Putchar e     ->      Putchar(tr_expr env e) 
    | Set (s, e2) ->
      let expr = Imp.Set (s, tr_expr env e2) in

      (match e2 with
        | New(n, e) -> 
          let impCall = List.map (fun e -> tr_expr env e) e in
          let funClass = getAllClassMethodsIndex n in

          Seq([
            expr;
            Write(Var(s), Var(n ^ "_descr"));

            Expr(Imp.DCall(
              Deref(Binop(Add, Var(n ^ "_descr"), Cst((1 + Hashtbl.length funClass) * 4))),
              ((Var s) :: impCall)
            ))
          ])
        | _ -> expr)
    | If (cond, sT, sF) ->  If (tr_expr env cond, tr_seq env sT, tr_seq env sF)
    | While (e, seq) ->     While (tr_expr env e, tr_seq env seq)
    | Return (e) ->         Return (tr_expr env e)
    | Expr(e) ->            Expr(tr_expr env e)
    | Write(e1, e2) ->      Write (tr_mem env e1, tr_expr env e2)
  in
    
  let tr_fdef (fdef: Objlng.function_def): Imp.function_def =
    (* modifier: get function type return *)
    let env = Hashtbl.create 16 in
    List.iter (fun (x, t) -> Hashtbl.add env x t ) p.globals;
    List.iter (fun (x, t) -> Hashtbl.add env x t ) fdef.params;
    List.iter (fun (x, t) -> Hashtbl.add env x t ) fdef.locals;

    (match fdef.params with
      | [e] ->
        if (fst e == "this") then
          Hashtbl.add env "this" (snd e);
      | _ -> ());

    type_seq env fdef.code;

    {
      name = fdef.name;
      params = List.map fst fdef.params;
      locals = List.map fst fdef.locals;
      code = tr_seq env fdef.code;
    } in


  (* Pré-traitement, modification de la fonction main *)
  let formatMainToClasses (main: Objlng.function_def) (cList: Objlng.class_def list): Imp.function_def =
    let formatted = tr_fdef main in
  
    let newCode = List.fold_left (fun (code: Imp.sequence) (c: Objlng.class_def) ->
      let funClass = getAllClassMethodsIndex c.name in

      (* On prends le constructeur, pour le bouger ensuite à la fin de la liste *)
      let newFuncList = List.fold_right (fun (f: Objlng.function_def) acc ->
        if not (f.name = "constructor") then
          f :: acc
        else
          acc
        ) c.methods [] in
      let newFuncList = newFuncList in

      (* Les instructions *)
      Imp.Set(c.name ^ "_descr", Alloc (Cst(((Hashtbl.length funClass) + 1 + 1)*4))) 
      ::
      Imp.Write(Binop(Add, Var(c.name ^ "_descr"), Cst 0), 
        if Option.is_none c.parent then 
          Cst 0
        else
          Var ((Option.get c.parent) ^ "_descr")) 
      ::
      Imp.Write(
        (Binop(Add, Var(c.name ^ "_descr"), Cst(((Hashtbl.length funClass) + 1) * 4))),
        (Addr (c.name ^ "_constructor")))
      ::
      List.fold_left(fun (codeAcc: Imp.sequence) (f: Objlng.function_def) ->
        let funcIndex = Hashtbl.find funClass f.name in

        let funName = c.name ^ "_" ^ f.name in
        let writeFun = Imp.Write(
        (Binop(Add, Var(c.name ^ "_descr"), Cst((funcIndex + 1) * 4))),
        (Addr funName)) in
  
        writeFun :: codeAcc
      ) code newFuncList
    ) formatted.code cList in
  
    {
      code = newCode;
      name = formatted.name;
      params = formatted.params;
      locals = formatted.locals;
    } in

  {
    Imp.globals = List.map fst p.globals;
    functions = List.map (fun (f: Objlng.function_def) ->

      if not (f.name = "main") then 
        tr_fdef f
      else 
        (formatMainToClasses f p.classes)
    ) p.functions;
  };;