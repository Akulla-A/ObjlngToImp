(**
   Annotated abstract syntax for the OBJEling language.
 *)

(* Types of SIMP values *)
type typ =
  | TInt 
  | TBool
  | TClass of string (* class type, identified by its name *)
  | TArray of typ    (* array containing elements of the specified type *)
  | TVoid (* not an actual type in the source language, but having it in
             the AST makes the code more uniform *)

type binop = Add | Mul | Lt

type expression =
  | Cst   of int
  | Bool  of bool
  | Var   of string
  | Binop of binop * expression * expression
  | Call  of string * expression list
  | MCall of expression * string * expression list
  | New   of string * expression list (* create an instance and call the constructor *)
  | NewTab of typ * expression (* create an array of the given type and size *)
  | Read  of mem               (* read in memory *)
  | This (* current object *)
and mem =
  | Arr of expression * expression (* array access     e1[e2]  *)
  | Atr of expression * string     (* attribute access  o.x    *)

type instruction =
  | Putchar of expression
  | Set     of string * expression
  | If      of expression * sequence * sequence
  | While   of expression * sequence
  | Return  of expression
  | Expr    of expression
  | Write   of mem * expression (*   m = e;   *)
and sequence = instruction list

(* Function definition *)
type function_def = {
  name:   string;
  params: (string * typ) list;
  locals: (string * typ) list;
  code:   sequence;
  return: typ;
}

(* Class definition *)
type class_def = {
  name:   string;
  fields: (string * typ) list;
  methods: function_def list;
  parent: string option;
}

(* Program as in SIMP with "structs" upgraded to "classes"  *)
type program = {
  globals:   (string * typ) list;
  functions: function_def list;
  classes:   class_def list;
}
