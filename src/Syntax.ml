(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Simple expressions: syntax and semantics *)
let ($) f x = f x
let (%) f g = fun x -> f $ g x

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
    let apply_to_snd oper     = map $ fun (op, f) -> (op, oper f);;
    let bool_operators        = apply_to_snd result_to_int $ apply_to_snd args_to_bool  [ ("!!", ( || ));
                                                                                          ("&&", ( && ))];;
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
        | Write e -> (s, _in, Expr.eval s e :: _out)
        | Assign (x, e) -> (Expr.update x (Expr.eval s e) s, _in, _out)
        | Seq (op1, op2) -> eval (eval (s, _in, _out) op1) op2;;

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
