(* 
  Mini-OCaml Interpreter 
*)

(* Expressions, Types, Environments *)

type ty = Bool | Int | Arrow of ty * ty
type con = Bcon of bool | Icon of int
type var = string
type op = Add | Sub | Mul | Leq
type exp = Var of var | Con of con
          | Oapp of op * exp * exp
          | Fapp of exp * exp
          | If of exp * exp * exp
          | Lam of var * exp
          | Lamty of var * ty * exp
          | Let of var * exp * exp
          | Letrec of var * var * exp * exp
          | Letrecty of var * var * ty * ty * exp * exp

let expFact = 
  Letrec("fact","x"
      ,If(Oapp(Leq,Var "x",Con (Icon 1))
          ,Con (Icon 1)
          ,Oapp(Mul,Var "x",Fapp(Var "fact",Oapp(Sub,Var "x",Con (Icon 1)))))
      ,Fapp(Var "fact",Con(Icon 10)))


type ('a,'b) env = ('a * 'b) list
let empty : ('a,'b) env = []
let update (env : ('a,'b) env) a b : ('a,'b) env = (a,b) :: env
let rec lookup (env : ('a,'b) env) a = match env with
  | (a',b) :: env -> if a' = a then Some b else lookup env a
  | [] -> None


(* type checker *) 
let rec check env exp : ty = 
  let check_op_app o t1 t2 : ty = match o, t1, t2 with
    | Add, Int, Int -> Int
    | Sub, Int, Int -> Int
    | Mul, Int, Int -> Int
    | Leq, Int, Int -> Bool
    | _, _, _ -> failwith "check_op_app: arguments ill-typed" in

  let check_fun_app t1 t2 : ty = match t1 with
    | Arrow (t2',t1') -> if t2' = t2 then t1'
      else failwith "check_fun_app: wrong argument type"
    | _ -> failwith "check_fun_app: function expected" in

  match exp with
    | Var x -> begin match lookup env x with
      | Some t -> t
      | None -> failwith ("typechecker: unbound variable" ^ x)
      end
    | Con (Bcon b) -> Bool
    | Con (Icon n) -> Int
    | Oapp (op,e1,e2) -> check_op_app op (check env e1) (check env e2)
    | Fapp (e1,e2) -> check_fun_app (check env e1) (check env e2)
    | If (e1,e2,e3) -> begin match check env e1, check env e2, check env e3 with
      | Bool, t1, t2 -> if t1 = t2 then t1 else failwith "typechecker: conditional types not the same"
      | _, _, _ -> failwith "typechecker: if expects bool as condition"
        end
    | Lam (_,_) -> failwith "typecker: fun missing type specification" (* typing rules need type specs *)
    | Lamty (x,t1,e) -> Arrow (t1, check (update env x t1) e)
    | Let (x,e1,e2) -> check (update env x (check env e1)) e2
    | Letrec (f,x,e1,e2) -> failwith "check: let rec missing type specifications" (* typing rules need type specs *)
    | Letrecty (f,x,t1,t2,e1,e2) -> let e' = update env f (Arrow(t1,t2)) in   (* ?? *)
      if check (update e' x t1) e1 = t2 then check e' e2
      else failwith "typechecker: let rec: declared type not matched"


(* Evaluator *)

type value = Bval of bool | Ival of int
  | Closure of var * exp * (var, value) env
  | Rclosure of var * var * exp * (var, value) env

let rec eval env exp : value = 
  let eval_op_app o v1 v2 : value = match o, v1, v2 with
    | Add, Ival v1, Ival v2 -> Ival (v1 + v2)
    | Sub, Ival v1, Ival v2 -> Ival (v1 - v2)
    | Mul, Ival v1, Ival v2 -> Ival (v1 * v2)
    | Leq, Ival v1, Ival v2 -> Bval (v1 <= v2)
    | _, _, _ -> failwith "eval_op_app: ill-typed arguments cannot be evaluated" in

  let eval_fun_app v1 v2 : value = match v1 with
    | Closure (x,e,env) -> eval (update env x v2) e
    | Rclosure (f,x,e,env) -> eval (update (update env f v1) x v2) e 
    | _ -> failwith "eval_fun_app: function expected" in
    
  match exp with
    | Var x -> begin match lookup env x with
      | Some v -> v
      | None -> failwith ("evaluator: unbound variable" ^ x)
      end
    | Con (Bcon b) -> Bval b
    | Con (Icon n) -> Ival n
    | Oapp (op,e1,e2) -> eval_op_app op (eval env e1) (eval env e2)
    | If (e1,e2,e3) -> begin match eval env e1 with
      | Bval b -> if b then eval env e2 else eval env e3
      | _ -> failwith "evaluator: if expects bool as condition"
      end
    | Let (x,e1,e2) -> eval (update env x (eval env e1)) e2
    | Lam (x,e) | Lamty (x,_,e) -> Closure (x,e,env)
    | Fapp (e1,e2) -> eval_fun_app (eval env e1) (eval env e2)
    | Letrec (f,x,e1,e2) | Letrecty (f,x,_,_,e1,e2) -> eval (update env f (Rclosure (f,x,e1,env))) e2

(* Lexer *)

type const = BCON of bool | ICON of int
type token = LP | RP | EQ | COL | ARR | ADD | SUB | MUL | LEQ 
| IF | THEN | ELSE | LAM | LET | IN | REC 
| CON of const | VAR of string | BOOL | INT

let is_digit c = 48 <= Char.code c && Char.code c <= 57 

let char_to_int c = match c with 
  | '0' -> 0 | '1' -> 1 | '2' -> 2 | '3' -> 3 | '4' -> 4 | '5' -> 5 | '6' -> 6 | '7' -> 7 | '8' -> 8 | '9' -> 9
  | _ -> failwith "char_to_num: not a char"

let is_lcletter c = 97 <= Char.code c && Char.code c <= 122 
let is_ucletter c = 65 <= Char.code c && Char.code c <= 90
let is_idletter c = is_lcletter c || is_ucletter c || is_digit c || c = '_' || c = '\''
(* Following OCaml, an identifier must start with a lower case letter and can then continue with digits, 
lower and upper case letters, and the special characters ’_’ (underline) and ’’’ (quote). *)

let lex s : token list = 
  let get i = String.get s i in
  let get_string i n = String.sub s (i-n) n in (* gets a substring von s  with start index i-n and end index i*)
  let exhausted i = i >= String.length s in
  let verify i c = not (exhausted i) && get i = c in
  let rec lex' i l =
    if exhausted i then List.rev l
    else match get i with
    | '(' -> if verify (i+1) '*' then skip_comment (i+2) 1 l else lex' (i+1) (LP::l)
    | ')' -> lex' (i+1) (RP::l)
    | '=' -> lex' (i+1) (EQ::l)
    | '<' -> if verify (i+1) '=' then lex' (i+2) (LEQ::l) else failwith "lex: only <= ist allowed"
    | ':' -> lex' (i+1) (COL::l)
    | '-' -> if verify (i+1) '>' then lex' (i+2) (ARR::l) else lex' (i+1) (SUB::l)
    | '+' -> lex' (i+1) (ADD::l)
    | '*' -> lex' (i+1) (MUL::l)
    | c when is_digit c -> lex_num i 0 l
    | c when is_lcletter c -> lex_id (i+1) 1 l
    | ' ' | '\n' | '\t' -> lex' (i+1) l
    | c -> failwith "lex: illegal character"

    and skip_comment i n l = 
    if n > 0 then 
      if verify i '(' && verify (i+1) '*' then skip_comment (i+2) (n+1) l else
      if verify i '*' && verify (i+1) ')' then skip_comment (i+2) (n-1) l else 
        skip_comment (i+1) n l
    else lex' i l 

    and lex_num i n l = if not (exhausted i) && is_digit (get (i)) then lex_num (i+1) (n*10 + char_to_int (get i)) l else lex_num' i n l
    and lex_num' i n l = lex' i (CON (ICON n)::l)

    and lex_id i n l = if (not (exhausted i)) && is_idletter (get i) then lex_id (i+1) (n+1) l else lex_id' i n l
    and lex_id' i n l = match get_string i n with
    | "if" -> lex' i (IF::l)
    | "then" -> lex' i (THEN::l)
    | "else" -> lex' i (ELSE::l)
    | "fun" -> lex' i (LAM::l)
    | "let" -> lex' i (LET::l)
    | "in" -> lex' i (IN::l)
    | "rec" -> lex' i (REC::l)
    | "false" -> lex' i (CON (BCON false)::l)
    | "true" -> lex' i (CON (BCON true)::l)
    | s -> lex' i (VAR s::l)

  in lex' 0 []


(* Parser *)
let parse l = 
  let verify c l = match l with 
    | [] -> []
    | c'::l -> if c = c' then l else failwith "verify: wrong token" in
  let rec exp l : exp * token list = match l with (* top level *)
    | IF::l -> 
      let (e1,l) = exp l in
      let (e2,l) = exp (verify THEN l) in
      let (e3,l) = exp (verify ELSE l) in
      (If(e1,e2,e3),l)
    | LAM::VAR x::ARR::l -> 
      let(e,l) = exp l in 
      (Lam(x,e),l)
    (*| LAM::LP::VAR x::COL::l -> 
      let(ty,l) = type l in 
      let(e,l) = exp l in Lamty(x, ty, e)*)
    | LET::VAR x::EQ::l -> 
      let(e1,l) = exp l in
      let(e2,l) = exp (verify IN l) in
      (Let(x,e1,e2),l)
    | LET::REC::VAR f::VAR x::EQ::l -> 
      let(e1,l) = exp l in
      let(e2,l) = exp (verify IN l) in
      (Letrec(f,x,e1,e2),l)
    (*| LET::REC::VAR f::LP::VAR x::COL::l -> *) 
    | l -> cexp l

  and cexp l = let (e1,l) = sexp l in cexp' e1 l (* comparisons, infix *)
  and cexp' e1 l = match l with
    | LEQ::l -> let(e2,l) = sexp l in (Oapp(Leq,e1,e2),l)
    | l -> (e1,l)

  and sexp l = let (e1,l) = mexp l in sexp' e1 l (* additive operators, infix *)
  and sexp' e1 l = match l with (* auxilary categorie to realize left-associativity *)
    | ADD::l -> let (e2,l) = mexp l in sexp' (Oapp(Add,e1,e2)) l 
    | SUB::l -> let (e2,l) = mexp l in sexp' (Oapp(Sub,e1,e2)) l
    | l -> (e1,l)

  and mexp l = let (e1,l) = aexp l in mexp' e1 l (* multiplicative operators, infix *)
  and mexp' e1 l = match l with (* auxilary categorie to realize left-associativity *)
    | MUL::l -> let(e2,l) = aexp l in aexp' (Oapp(Mul,e1,e2)) l (* why aexp' here?? *)
    | l -> (e1,l)

  and aexp l = let (e1,l) = pexp l in aexp' e1 l (* function applications, infix *)
  and aexp' e1 l = match l with (* auxilary categorie to realize left-associativity *)
    | VAR _ :: _ | CON _ :: _ | LP :: _ -> let(e2,l) = pexp l in aexp' (Fapp(e1,e2)) l
    | l -> (e1,l)

  and pexp l = match l with (* bottom level, takes care of variables, constants, and parenthesized expressions *)
    | VAR x::l -> (Var x,l)
    | CON (BCON b)::l -> (Con (Bcon b), l)
    | CON (ICON n)::l -> (Con (Icon n), l)
    | LP::l -> let (e,l) = exp l in (e, verify RP l)
    | _ -> failwith ("parsing: pexp")

  (*and ty l = let (t1,l) = pty t in ty' t1 l (* parsing types *)
  and ty' t1 l = match l with 
      | ARR::l -> let (t2,l) = ty in
  and pty l = match l with
      | BCon::l -> Bool 
      | ICon::l -> Bool*)

  in exp l


(* testing with sample solutions, must all be return true *)
let test_string =
  "let rec fac a = fun n ->
    if n <= 1 then a else fac (n*a) (n-1) 
    in fac 1 5"
let lex_test = lex test_string = [LET; REC; VAR "fac"; VAR "a"; EQ; LAM; VAR "n"; ARR; IF; VAR "n"; LEQ;
CON (ICON 1); THEN; VAR "a"; ELSE; VAR "fac"; LP; VAR "n"; MUL; VAR "a"; RP;
LP; VAR "n"; SUB; CON (ICON 1); RP; IN; VAR "fac"; CON (ICON 1);
CON (ICON 5)]
let parse_test = parse (lex test_string) = (Letrec ("fac", "a",
Lam ("n",
If (Oapp (Leq, Var "n", Con (Icon 1)), Var "a",
Fapp (Fapp (Var "fac", Oapp (Mul, Var "n", Var "a")),
Oapp (Sub, Var "n", Con (Icon 1))))),
Fapp (Fapp (Var "fac", Con (Icon 1)), Con (Icon 5))),
[])

let typecheck_test = check empty
(Letrecty ("fac", "a", Int, Arrow(Int,Int), 
           Lamty ("n", Int,
                  If (Oapp (Leq, Var "n", Con (Icon 1)), Var "a",
                      Fapp (Fapp (Var "fac", Oapp (Mul, Var "n", Var "a")),
                            Oapp (Sub, Var "n", Con (Icon 1))))),
           Fapp (Fapp (Var "fac", Con (Icon 1)), Con (Icon 4)))) = Int

let eval_test = eval empty (fst(parse(lex test_string))) = Ival 120;;