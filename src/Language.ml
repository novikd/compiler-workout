(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

let default value = function
  | Some x -> x
  | _      -> value;;

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let rec eval st expr =
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      parse:
	  !(Ostap.Util.expr
             (fun x -> x)
	     (Array.map (fun (a, s) -> a,
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        )
              [|
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |]
	     )
	     primary);

      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (s, _in, _out) stmt =
      match stmt with
        | Read x               -> (State.update x (hd _in) s, tl _in, _out)
        | Write e              -> (s, _in, _out @ [Expr.eval s e])
        | Assign (x, e)        -> (State.update x (Expr.eval s e) s, _in, _out)
        | Seq (op1, op2)       -> eval env (eval env (s, _in, _out) op1) op2
        | Skip                 -> (s, _in, _out)
        | If (e, stmt1, stmt2) -> if (Expr.eval s e) != 0
                                  then eval env (s, _in, _out) stmt1
                                  else eval env (s, _in, _out) stmt2
        | While (e, body)      -> if (Expr.eval s e) != 0
                                  then eval env (eval env (s, _in, _out) body) stmt
                                  else (s, _in, _out)
        | Repeat (body, e)     -> let s, _in, _out = eval env (s, _in, _out) body in
                                    if (Expr.eval s e) = 0
                                    then eval env (s, _in, _out) stmt
                                    else (s, _in, _out)
        | Call (func, args)    -> let params, locals, body = env#definition func in
                                  let args_value = List.map (Expr.eval s) args in
                                  let args_binding = List.combine params args_value in
                                  let function_state = State.push_scope s (params @ locals) in
                                  let function_scope = List.fold_left (fun st (name, value) -> State.update name value st)
                                                       function_state
                                                       args_binding in
                                  let new_s, _in, _out = eval env (function_scope, _in, _out) body in
                                    State.drop_scope new_s s, _in, _out
        | _ -> failwith "Unsupported operation";;

    (* Statement parser *)
    ostap (
      call_statement:
        func_id:IDENT "(" args:(!(Expr.parse))* ")" { Call (func_id, args) }
      ;

      statement:
          "read" "(" name:IDENT ")" { Read name }
        | "write" "(" exp:!(Expr.parse) ")" { Write exp }
        | name:IDENT ":=" exp:!(Expr.parse) { Assign (name, exp)}
        | "skip" { Skip }
        | "if" exp:!(Expr.parse) "then" stmt1:parse stmt2:else_stmt { If (exp, stmt1, stmt2) }
        | "while" exp:!(Expr.parse) "do" stmt:parse "od" { While (exp, stmt) }
        | "repeat" stmt:parse "until" exp:!(Expr.parse) { Repeat (stmt, exp) }
        | "for" s1:statement "," exp:!(Expr.parse) "," s2:parse "do" s3:parse "od" { Seq (s1, While (exp, Seq (s3, s2))) }
        | call:call_statement { call }
      ;

      else_stmt:
          "fi" { Skip }
        | "else" stmt:parse "fi" { stmt }
        | "elif" exp:!(Expr.parse) "then" stmt1:parse stmt2:else_stmt { If (exp, stmt1, stmt2) }
      ;

      parse: line:statement ";" tail:parse { Seq (line, tail) } | statement
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse:
        "fun" func_id:IDENT "(" params:(IDENT)* ")"
        locals:(%"local" (IDENT)*)?
        "{" body:!(Stmt.parse) "}"
        { func_id, (params, default [] locals, body) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
