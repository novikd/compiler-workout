open GT
open Language
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval cnfg p =
  let eval_step (stack, (s, i, o)) instr =
    match instr with
      | BINOP op -> ((Language.Expr.operatorByName op) (hd @@ tl stack) (hd stack) :: (tl @@ tl stack), (s, i, o))
      | CONST n  -> (n :: stack, (s, i, o))
      | READ     -> (hd i :: stack, (s, tl i, o))
      | WRITE    -> (tl stack, (s, i, o @ [hd stack]))
      | LD name  -> (s name :: stack, (s, i, o))
      | ST name  -> (tl stack, (Language.Expr.update name (hd stack) s, i, o)) in
  match p with
  | [] -> cnfg
  | x :: xs -> eval (eval_step cnfg x) xs;;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
  let rec compile_expr expr =
    match expr with
      | Language.Expr.Const n              -> [ CONST n ]
      | Language.Expr.Var name             -> [ LD name ]
      | Language.Expr.Binop (op, lhs, rhs) -> compile_expr lhs @ compile_expr rhs @ [ BINOP op ] in
  match stmt with
    | Language.Stmt.Read name        -> [ READ; ST name ]
    | Language.Stmt.Write expr       -> compile_expr expr @ [ WRITE ]
    | Language.Stmt.Assign (name, e) -> compile_expr e @ [ ST name ]
    | Language.Stmt.Seq (op1, op2)   -> compile op1 @ compile op2;;