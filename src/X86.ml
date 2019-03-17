(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd =
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl"
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | op    -> failwith "unknown binary operator: " ^ op
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

let set_zero operand = Binop ("^", operand, operand)

let ensure_mem_mem_op op lhs rhs =
  match lhs, rhs with
  | (R _, _) | (L _, _) -> rhs, [op lhs rhs]
  | (_, R _)            -> rhs, [op lhs rhs]
  | _                   -> edx, [ Mov (rhs, edx);
                                  op lhs edx]

let create_binop op x y = Binop (op, x, y)

let generate_comparing cmp_op output lhs rhs =
  let op_suffix = match cmp_op with
    | "<"  -> "l"
    | "<=" -> "le"
    | ">"  -> "g"
    | ">=" -> "ge"
    | "==" -> "e"
    | "!=" -> "ne"
    | _    -> failwith (Printf.sprintf "Unknown operator %s" cmp_op) in
  let _, asm = ensure_mem_mem_op (create_binop "cmp") lhs rhs in
      [set_zero eax;]
      @ asm
      @ [ Set (op_suffix, "%al");
          Mov (eax, output)]

let compile_binop env instuction =
  let rhs, lhs, env = env#pop2 in
  let s, env = env#allocate in
  let asm = match instuction with
    | "+" | "-" | "*" -> let output, asm = ensure_mem_mem_op (create_binop instuction) rhs lhs in
                          asm @ [Mov (output, s)]
    | "&&" -> [set_zero eax;
               set_zero edx;
               Binop ("cmp", L 0, rhs);
               Set ("ne", "%al");
               Binop ("cmp", L 0, lhs);
               Set ("ne", "%dl");
               Binop ("&&", eax, edx);
               Mov (edx, s)]
    | "!!" -> [set_zero edx;
               Mov (lhs, eax);
               Binop ("!!", rhs, eax);
               Binop ("cmp", L 0, eax);
               Set ("ne", "%dl");
               Mov (edx, s)]
    | "<" | ">" | "<=" | ">=" | "==" | "!=" -> generate_comparing instuction s rhs lhs
    | "/" | "%" -> let output = if instuction = "/" then eax else edx in
                                  [Mov (lhs, eax);
                                   set_zero edx;
                                   Cltd;
                                   IDiv rhs;
                                   Mov (output, s)]
    | _ -> failwith ("Unsupported binary operation" ^ instuction)
  in env, asm

let ensure_mem_mem_mov source destination =
    match source with
      | R _ | L _ -> [Mov (source, destination)]
      | _         -> match destination with
                      | R _ -> [Mov (source, destination)]
                      | _   -> [Mov (source, eax);
                                Mov (eax, destination)]

let list_init n =
  let rec create = function
    | 0 -> []
    | n -> (n - 1) :: (create @@ n - 1) in
  List.rev @@ create n

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec compile env code =
  let suffix = function
  | "<"  -> "l"
  | "<=" -> "le"
  | "==" -> "e"
  | "!=" -> "ne"
  | ">=" -> "ge"
  | ">"  -> "g"
  | _    -> failwith "unknown operator"
  in
  function
| [] -> env, []
| instr :: code ->
  let push_all_regs = List.map (fun x -> Push (R x)) @@ list_init num_of_regs in
  let pop_all_reg   = List.map (fun x -> Pop (R x)) @@ List.rev @@ list_init num_of_regs in
  let rec pop_symbolic_args env n = if n = 0
                                    then env, []
                                    else let s, env = env#pop in
                                         let env, args = pop_symbolic_args env (n - 1) in
                                          env, args @ [s] in
  let env, asm = match instr with
    | CONST n     -> let s, env =  env#allocate in
                      env, [Mov (L n, s)]
    | BINOP op    -> compile_binop env op
    | WRITE       -> let s, env = env#pop in
                      env, [Push s; Call "Lwrite"; Pop eax]
    | READ        -> let s, env = env#allocate in
                      env, [Call "Lread"; Mov (eax, s)]
    | LD name     -> let s, env = (env#global name)#allocate in
                      env, (ensure_mem_mem_mov (env#loc name) s)
    | ST name     -> let s, env = (env#global name)#pop in
                      env, (ensure_mem_mem_mov s (env#loc name))
    | LABEL l     -> env, [Label l]
    | JMP l       -> env, [Jmp l]
    | CJMP (c, l) -> let s, env = env#pop in
                      env, [Binop ("cmp", L 0, s);
                            CJmp (c, l)]
    | BEGIN (id, params, locals) -> let prolog    = [ Push ebp;
                                                      Mov (esp, ebp)] in
                                    let env       = env#enter id params locals in
                                      env,  prolog
                                            @ push_all_regs
                                            @ [Binop ("-", M ("$" ^ env#lsize), esp)]
    | END                        -> let epilogue  = [  Mov (ebp, esp);
                                                      Pop ebp;
                                                      Ret] in
                                    let meta = [Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))] in
                                      env, [Label env#epilogue]
                                            @ pop_all_reg
                                            @ epilogue
                                            @ meta
    | CALL  (id, n, returns)     -> let env, args          = pop_symbolic_args env n in
                                    let push_args          = List.map (fun x -> Push x) args in
                                    let env, gather_result = if returns
                                                             then let s, env = env#allocate in
                                                                    env, [Mov (eax, s)]
                                                             else env, [] in
                                      env,  push_args
                                            @ [ Call id;
                                                Binop ("+", L (n * word_size), esp)]
                                            @ gather_result
    | RET   returns              -> if returns
                                    then let s, env = env#pop in
                                          env, [Mov (s, eax);
                                                Jmp env#epilogue]
                                    else env, [Jmp env#epilogue]
    | _ -> failwith "Not supported yet" in
  let env, asm' = compile env code in
    env, asm @ asm'

(* A set of strings *)
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (list_init (List.length l))

class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)

    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)

    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
        let rec allocate' = function
        | []                            -> R 0     , 0
        | (S n)::_                      -> S (n+1) , n+2
        | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
        | _                             -> let n = List.length locals in S n, n+1
        in
        allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots

    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname

    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
  end

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
