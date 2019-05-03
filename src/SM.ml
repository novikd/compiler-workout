open GT
open Language
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((cstack, stack, ((s, i, o) as c)) as conf) prg =
  let eval_jmp cfg label = eval env cfg @@ env#labeled label in
  match prg with
  | [] -> conf
  | instr :: code ->
    let eval_code c = eval env c code in
    match instr with
      | BINOP op         -> eval_code (cstack,
                                      (Language.Expr.to_func op) (hd @@ tl stack) (hd stack) :: (tl @@ tl stack),
                                      c)
      | CONST n          -> eval_code (cstack, n :: stack, c)
      | READ             -> eval_code (cstack, hd i :: stack, (s, tl i, o))
      | WRITE            -> eval_code (cstack, tl stack, (s, i, o @ [hd stack]))
      | LD name          -> eval_code (cstack, Language.State.eval s name :: stack, c)
      | ST name          -> eval_code (cstack, tl stack, (Language.State.update name (hd stack) s, i, o))
      | LABEL _          -> eval_code conf
      | JMP label        -> eval_jmp conf label
      | CJMP (cond, label) -> let value, tail = hd stack, tl stack in
                                 if cond = "z" && value = 0 || cond = "nz" && value != 0
                                 then eval_jmp (cstack, tail, (s, i, o)) label
                                 else eval_code (cstack, tail, (s, i, o))
      | BEGIN (_, params, locals) -> let func_scope = Language.State.enter s (params @ locals) in
                                  let func_state, stack = List.fold_left
                                                          (fun (state, value::tail) name -> (Language.State.update name value state, tail))
                                                          (func_scope, stack)
                                                          params in
                                    eval_code (cstack, stack, (func_state, i, o))
      | RET _ | END                    -> (match cstack with
                                    | (pr_before_call, state_before_call)::tail -> eval env
                                                                                        (tail,
                                                                                         stack,
                                                                                         (Language.State.leave s state_before_call, i, o))
                                                                                        pr_before_call
                                    | _                                         -> ([], stack, (s, i, o)))
      | CALL (id, _, _)        -> let func = env#labeled id in
                                    eval env ((code, s)::cstack, stack, (s, i, o)) func
      | _                      -> failwith "Unsupported stack operation";;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

class compilation_env =
  object (self)
    val label_number = 0

    method generate_label = ".L" ^ string_of_int label_number, {< label_number = label_number + 1 >}
  end

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec compile_expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
    | Expr.Call (id, args)  -> let compiled_args = List.concat @@ List.map compile_expr @@ List.rev args in
                                compiled_args @ [CALL (id, List.length args, true)] in
  let rec compile_stmt env =
    let rec compile_if_stmt env exit_label = function
      | Stmt.Seq (s1, s2)   -> let env, code'  = compile_stmt env s1 in
                               let env, code'' = compile_if_stmt env exit_label s2 in
                                env, code' @ code''
      | Stmt.If (e, s1, s2) -> let else_label, env  = env#generate_label in
                               let env, then_branch = compile_if_stmt env exit_label s1 in
                               let env, else_branch = compile_stmt env s2 in
                                env, compile_expr e
                                     @ [CJMP ("z", else_label)]
                                     @ then_branch
                                     @ [JMP (exit_label)]
                                     @ [LABEL else_label]
                                     @ else_branch
      | stmt                -> compile_stmt env stmt in
    function
    | Stmt.Seq (s1, s2)  -> let env, code'  = compile_stmt env s1 in
                            let env, code'' = compile_stmt env s2 in
                              env, code' @ code''
    | Stmt.Read x        -> env, [READ; ST x]
    | Stmt.Write e       -> env, compile_expr e @ [WRITE]
    | Stmt.Assign (x, e) -> env, compile_expr e @ [ST x]
    | Stmt.Skip          -> env, []
    | Stmt.If (e, s1, s2) -> let exit_label, env = env#generate_label in
                             let env, code = compile_if_stmt env exit_label @@ Stmt.If (e, s1, s2) in
                              env, code @ [LABEL exit_label]
    | Stmt.While (e, s)  -> let loop_label, env = env#generate_label in
                            let cond_label, env = env#generate_label in
                            let env, loop_body  = compile_stmt env s in
                              env, [ JMP (cond_label);
                                     LABEL (loop_label)]
                                     @ loop_body
                                     @ [LABEL cond_label]
                                     @ compile_expr e
                                     @ [CJMP ("nz", loop_label)]
    | Stmt.Repeat (s, e) -> let loop_label, env = env#generate_label in
                            let env, loop_body  = compile_stmt env s in
                              env, [ LABEL loop_label]
                                     @ loop_body
                                     @ compile_expr e
                                     @ [CJMP ("z", loop_label)]
    | Stmt.Return e      -> (match e with
                              | Some e -> env,  compile_expr e
                                                @ [RET true]
                              | _      -> env, [RET false])
    | Stmt.Call (id, args) -> env, List.concat (List.map compile_expr @@ List.rev args) @ [CALL (id, List.length args, false)] in
  let compile_definition env (id, (params, locals, body)) = let env, code = compile_stmt env body in
                                                             env, [LABEL id]
                                                                @ [BEGIN (id, params, locals)]
                                                                @ code
                                                                @ [END] in
  let rec compile_all_definitions env = function
    | [] -> env, []
    | def :: tail -> let env, code  = compile_definition env def in
                     let env, code' = compile_all_definitions env tail in
                      env, code @ code' in
  function (defs, stmt) -> let env, code = compile_all_definitions (new compilation_env) defs in
                           let env, code' = compile_stmt env stmt in
                            code' @ [END] @ code
