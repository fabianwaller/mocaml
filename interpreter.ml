(* 
  Mini-OCaml Interpreter 
  Fabian Waller
*)

(* Expressions, Types, Environments *)

type ty = Bool | Int | Arrow of ty * ty
type con = Bcon of bool | Icon of int
type op = Add | Sub | Mul | Leq
type var = string
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




(* Lexer *)

type const = BCON of bool | ICON of int
type token = LP | RP | EQ | COL | ARR | ADD | SUB | MUL | LEQ 
| IF | THEN | ELSE | LAM | LET | IN | REC 
| CON of const | VAR of string | BOOL | INT

let is_digit c = 48 <= Char.code c && Char.code c <= 57 

let char_to_num c = match c with 
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5 
  | '6' -> 6 
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | _ -> failwith "char_to_num: not a char"

let is_lcletter c = 97 <= Char.code c && Char.code c <= 122 
let is_ucletter c = 65 <= Char.code c && Char.code c <= 90

let lex s : token list = 
  let get i = String.get s i in
  let get_string i n = String.sub s (i-n) n in (* gets a substring von s  with start index i-n and end index i*)
  let exhausted i = i >= String.length s in
  let verify i c = not (exhausted i) && get i = c in
  let rec lex' i l =
    if exhausted i then List.rev l
    else match get i with
    | '(' -> lex' (i+1) (LP::l)
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

    and lex_num i n l = if not (exhausted i) && is_digit (get (i)) then lex_num (i+1) (n*10 + char_to_num (get i)) l else lex_num' i n l
    and lex_num' i n l = lex' i (CON (ICON n)::l)

    and lex_id i n l = lex_id' i n l
    and lex_id' i n l = match get_string i n with
    | "if" -> lex' i (IF::l)
      (* ... *)
    | s -> lex' i (VAR s::l)

    (* Following OCaml, an identifier must start with a lower case letter and can then continue with digits, lower and upper case letters, and the special characters ’ ’ (underline) and ’’’ (quote). *)

  in lex' 0 []
