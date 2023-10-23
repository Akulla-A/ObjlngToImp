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

  let getClassByName n =
    let findStruct = List.find_opt (fun (blob: Objlng.class_def) -> blob.name = n) p.classes in
    if(Option.is_none findStruct) then failwith "Struct does not exists";
    Option.get findStruct in
    
  let rec type_expr env: Objlng.expression -> Objlng.typ = function
    | Cst n -> TInt
    | Bool b -> TBool
    | Var v -> 
      let var = Hashtbl.find_opt env v in
      if Option.is_none var then
        failwith ("Couldn't find the variable" ^ v);

      Option.get var
    | Binop(op, e1, e2) -> if (op <> Lt) then TInt else TBool
    | Call(s, eList) ->
      let getFunc = List.find_opt (fun (f: Objlng.function_def) -> f.name = s) p.functions in

      if Option.is_none getFunc then
        failwith ("Couldn't find the function: " ^ s);

      let getFunc = Option.get getFunc in

      List.iter2 (fun fParam expr ->
        if (type_expr env expr <> snd fParam) then
          failwith "Calling a function with missmatching argument type"
      ) getFunc.params eList;

      getFunc.return
    | MCall(exp, s, eList) -> 
      let r = type_expr env exp in
      let structName = (match r with
        | TClass n -> n
        | _ -> failwith "Calling a object function on a expression that is not a class") in
      let c = getClassByName structName in
      let f = List.find_opt (fun (f: Objlng.function_def) -> f.name = s) c.methods in

      if Option.is_none f then
        failwith ("Couldn't find the object function: " ^ s);

      (*  Hashtbl.add cache l'ancienne valeur, ce qui est parfait pour nous, pas besoin de recréer une hashtbl*)
      Hashtbl.add env "this" r;

      List.iter2 (fun fParam expr ->
        if (type_expr env expr <> snd fParam) then
          failwith "Calling a function with missmatching argument type"
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
            failwith "Calling a function with missmatching argument type"
        ) (Option.get constructor).params eList;

      TClass n
    | NewTab(typ, expr) ->
      let t = type_expr env expr in
      if(type_expr env expr <> TInt) then 
        failwith ("Creating a array with a size that is not a integer, the size is a " ^ (printType t));

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
          | _ -> "Trying to read as a TStruct a variable that is not a TStruct") in

        let findStruct = List.find_opt (fun (blob: Objlng.class_def) -> blob.name = n) p.classes in

        if(Option.is_none findStruct) then
          failwith "Struct does not exists";
        
        let fields = (Option.get findStruct).fields in
        let foundArg = List.find_opt (fun (argN, _) -> 
          argName = argN
          ) fields in

        if Option.is_none foundArg then
          failwith ("Couldn't find the value " ^ argName ^ " in the struct " ^ n);
        snd (Option.get foundArg)
      | Arr (e1, e2) -> 
        let eLeft = type_expr env e1 in

        if(type_expr env e2 <> TInt) then
          failwith "Reading a TArray with a index that is not a TInt";

        (match eLeft with
          | TArray(t) -> t
          | _ -> failwith "Trying to read Array(e1, argName), is not a TArray") in

  let rec type_seq env s = List.iter (type_instr env) s
  and type_instr env: Objlng.instruction -> unit = function
    | Putchar e -> 
      if (type_expr env e <> TInt) then
        failwith "Putchar argument is not a TInt";
    | Set (s, e2) -> 
      let varType = Hashtbl.find_opt env s in

      if Option.is_none varType then
        failwith ("Trying to set a variable that does not exist " ^ s);

      if (type_expr env e2 <> Option.get varType) then
        failwith "Type error on Set";
    | If (cond, sT, sF) -> 
      if (type_expr env cond <> TBool) then
        failwith ("If condition is not a TBool. Is a " ^ (printType (type_expr env cond)));
    | While (e, seq) -> 
      if (type_expr env e <> TBool) then
        failwith ("While condition is not a TBool. Is a " ^ (printType (type_expr env e)));

    | Return (e) -> ();
    | Expr(e) -> ()
    | Write(e1, e2) -> 
      let tLeft = type_mem env e1 in
      let tRight = type_expr env e2 in
      if(tLeft <> tRight) then
        failwith ("Write on different types variables. Left is " ^ (printType tLeft) ^ ". Right is " ^ (printType tRight)) in

  let rec sizeOfStruct (s: Objlng.typ) =
    match s with
      | TClass s -> 
        let findStruct = List.find_opt (fun (blob: Objlng.class_def) -> blob.name = s) p.classes in

        if(Option.is_none findStruct) then
          failwith "Struct does not exists";

        (*
        List.fold_left (fun field acc -> (sizeOfStruct field) + acc ) (Option.get findStruct).fields 0*)
        (List.length (Option.get findStruct).fields) * 4 + 4
      | _ -> 4 in

  (* Appeler type_expr avant *)
  let rec tr_expr env: Objlng.expression -> Imp.expression = function
    | Cst n -> Cst n
    | Bool b -> Bool b
    | Var v -> Var v
    | Binop(op, e1, e2) -> Binop(tr_op op, tr_expr env e1 , tr_expr env e2)
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
      | _ -> failwith "Calling a object function on a expression that is not a class") in

      let c = getClassByName structName in

      (*? Vérifier appels pour parent si fonction manque ?*)
      Hashtbl.add env "this" (type_expr env exp);
      let impCall = List.map (fun e -> tr_expr env e) (exp :: eList) in
      let classDescriptorAddr = Imp.Deref (tr_expr env exp) in
      Hashtbl.remove env "this";

      let funcIndex = (getIndex(fun (f: Objlng.function_def) -> f.name = s) c.methods + 1) in

      DCall(
        Deref(Binop(Add, classDescriptorAddr, Cst(funcIndex * 4))), 
        impCall
      )
  and tr_mem env: Objlng.mem -> Imp.expression = function
    | Atr(e1, attrName) -> 
      let e1expr = type_expr env e1 in
      let structName = (match e1expr with
        | TClass n -> n
        | _ -> failwith "Using Atr on something else than TClass") in
      let findStruct = List.find_opt (fun (blob: Objlng.class_def) -> blob.name = structName) p.classes in

      if Option.is_none findStruct then
        failwith ("Couldn't find the class " ^ structName);

      let paramIndex = getIndex (fun (argN, typ) -> attrName = argN) (Option.get findStruct).fields in
  
      Binop(Add, tr_expr env e1, Binop(Mul, Cst (paramIndex + 1), Cst 4))
    | Arr(e1, e2) -> Binop(Add, tr_expr env e1, Binop(Mul, tr_expr env e2, Cst 4))
  in

  let rec tr_seq env s = List.map (tr_instr env) s
  and tr_instr env: Objlng.instruction -> Imp.instruction = function
    | Putchar e     ->      Putchar(tr_expr env e) 
    | Set (s, e2) ->
      let expr = Set (s, tr_expr env e2) in
    
      (match(type_expr env e2) with
        | TClass n ->
          let c = List.find (fun (blob: Objlng.class_def) -> blob.name = n) p.classes in
          let impCall = List.map (fun e -> tr_expr env e) e in
          let funcIndex = (getIndex(fun (f: Objlng.function_def) -> f.name = "constructor") c.methods + 1) in

          expr @@ Imp.DCall(
            Deref(Binop(Add, Addr(n ^ "_descr"), Cst(funcIndex * 4))),
            (Var s) :: impCall)
        | (_) -> expr)
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
      let accFun = ref 0 in
  
      Imp.Set(c.name ^ "_descr", Alloc (Cst((List.length c.methods + 1)*4))) 
      ::
      Imp.Write(Binop(Add, Addr(c.name ^ "_descr"), Cst 0), 
        if Option.is_none c.parent then 
          Cst 0
        else
          Var ((Option.get c.parent) ^ "_descr")) 
      ::
      List.fold_left(fun (codeAcc: Imp.sequence) (f: Objlng.function_def) ->
        accFun := (!accFun + 4);
        let funName = c.name ^ "_" ^ f.name in
        let writeFun = Imp.Write(
        (Binop(Add, Addr(c.name ^ "_descr"), Cst(!accFun))),
        (Addr funName)) in
  
        writeFun :: codeAcc
      ) code c.methods
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
      if f.name != "main" then 
        tr_fdef f
      else 
        (formatMainToClasses f p.classes)
    ) p.functions;
  };;