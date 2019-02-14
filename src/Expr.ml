(* Simple expressions: syntax and semantics *)

(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* The type for the expression. Note, in regular OCaml there is no "@type..."
   notation, it came from GT.
*)
@type expr =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * expr * expr with show

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

(* An example of a non-trivial state: *)
let s = update "x" 1 @@ update "y" 2 @@ update "z" 3 @@ update "t" 4 empty

(* Some testing; comment this definition out when submitting the solution. *)
let _ =
  List.iter
    (fun x ->
       try  Printf.printf "%s=%d\n" x @@ s x
       with Failure s -> Printf.printf "%s\n" s
    ) ["x"; "a"; "y"; "z"; "t"; "b"]

let to_bool x =
  match x with
    | 0 -> false
    | _ -> true;;

let from_bool x =
  match x with
    | true  -> 1
    | false -> 0;;

let params_to_bool f = fun x y -> f (to_bool x) (to_bool y);;
let return_int     f = fun x y -> from_bool @@ f x y;;

let apply_to_snd operation = map @@ fun (op, f) -> (op, operation f)

(* List of available operators *)
let bool_operators        = apply_to_snd return_int @@ apply_to_snd params_to_bool @@ [ ("!!", ( || ));
                                                                                        ("&&", ( && ))];;

let relation_operators    = apply_to_snd return_int [ ("==", ( == ));
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

let available_operators   = bool_operators @ relation_operators @ arithmetic_operators;;

(* Returns specific operator function by it's name *)
let operatorByName op = snd @@ find (fun x -> op == (fst x)) available_operators;;

(* Expression evaluator

     val eval : state -> expr -> int

   Takes a state and an expression, and returns the value of the expression in
   the given state.
*)
let rec eval s e =
  match e with
    | Const (value)        -> value
    | Var   (name)         -> s name
    | Binop (op, lhs, rhs) -> (operatorByName op) (eval s lhs) (eval s rhs);;
