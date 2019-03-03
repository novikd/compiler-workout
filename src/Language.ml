(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

let ($) f x = f x

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

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let to_bool x             = x != 0;;
    let to_int  x             = if x then 1 else 0;;
    let result_to_int op x y  = to_int $ op x y;;
    let args_to_bool op x y   = op (to_bool x) (to_bool y);;
    let apply_to_snd oper     = List.map @@ fun (op, f) -> (op, oper f);;
    let bool_operators        = apply_to_snd result_to_int @@ apply_to_snd args_to_bool [ "!!", ( || );
                                                                                          "&&", ( && );];;
    let relation_operators    = apply_to_snd result_to_int  [ ("==", ( == ));
                                                              ("!=", ( != ));
                                                              ("<=", ( <= ));
                                                              (">=", ( >= ));
                                                              ("<" , ( <  ));
                                                              (">" , ( >  ))];;
    let arithmetic_operators  = [ ("+" , ( +   ));
                                  ("-" , ( -   ));
                                  ("*" , ( *   ));
                                  ("/" , ( /   ));
                                  ("%" , ( mod ))];;
    let operators             = bool_operators @ relation_operators @ arithmetic_operators;;
    let operatorByName op     = snd $ find (fun x -> op = (fst x)) operators;;

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval s e =
      match e with
        | Const (value)        -> value
        | Var   (name)         -> s name
        | Binop (op, lhs, rhs) -> (operatorByName op) (eval s lhs) (eval s rhs);;

    let makeParserNodes xs = List.map (fun x -> ostap (- $(x)), (fun lhs rhs -> Binop (x, lhs, rhs))) xs;;

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      (* parse: empty {failwith "Not implemented yet"} *)
      expr:
        !(Ostap.Util.expr
            (fun x -> x)
            [|
                `Lefta, makeParserNodes ["!!"];
                `Lefta, makeParserNodes ["&&"];
                `Nona , makeParserNodes ["<="; "<"; ">="; ">"; "=="; "!="];
                `Lefta, makeParserNodes ["+"; "-"];
                `Lefta, makeParserNodes ["*"; "/"; "%"];
            |]
            primary
        );
      primary: x:IDENT { Var x } | n:DECIMAL { Const n } | -"(" expr -")"
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, _in, _out) stmt =
      match stmt with
        | Read x -> (Expr.update x (hd _in) s, tl _in, _out)
        | Write e -> (s, _in, _out @ [Expr.eval s e])
        | Assign (x, e) -> (Expr.update x (Expr.eval s e) s, _in, _out)
        | Seq (op1, op2) -> eval (eval (s, _in, _out) op1) op2;;

    (* Statement parser *)
    ostap (
      statement:
          "read" "(" name:IDENT ")" { Read name }
        | "write" "(" exp:!(Expr.expr) ")" { Write exp }
        | name:IDENT ":=" exp:!(Expr.expr) { Assign (name, exp)}
      ;

      parse: statement | line:statement ";" tail:parse { Seq (line, tail) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
