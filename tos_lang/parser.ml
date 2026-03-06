(* ================================================================= *)
(*  ToS-Lang Parser                                                   *)
(*                                                                    *)
(*  Hand-written recursive descent parser for ToS-Lang syntax.        *)
(*  Converts string source to ExprAnn (annotated expressions).        *)
(*                                                                    *)
(*  Parser is NOT verified — correctness guaranteed by the verified    *)
(*  type checker: if parser produces garbage, typecheck rejects it.   *)
(*                                                                    *)
(*  Syntax:                                                           *)
(*    e ::= n | \(x : T). e | e1 e2 | (e1, e2)                      *)
(*        | fst e | snd e | observe e n | resolve e                   *)
(*        | system L | project e through l                            *)
(*    T ::= Nat | T1 -> T2 | T1 * T2 | Process T | Layer T           *)
(*        | System L                                                  *)
(*                                                                    *)
(*  Author: Horsocrates | 2026-03-06                                  *)
(* ================================================================= *)

open UniversePolymorphism
open Typing_Expr
open TypeChecker

(* ================================================================= *)
(* 1. Token Types                                                     *)
(* ================================================================= *)

type token =
  | TkNum of int        (* natural number literal *)
  | TkIdent of string   (* identifier *)
  | TkLambda            (* \ *)
  | TkLParen            (* ( *)
  | TkRParen            (* ) *)
  | TkColon             (* : *)
  | TkDot               (* . *)
  | TkComma             (* , *)
  | TkArrow             (* -> *)
  | TkStar              (* * *)
  | TkEOF               (* end of input *)

(* ================================================================= *)
(* 2. Lexer                                                           *)
(* ================================================================= *)

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_alnum c = is_digit c || is_alpha c

let tokenize (src : string) : token list =
  let len = String.length src in
  let pos = ref 0 in
  let tokens = ref [] in
  while !pos < len do
    let c = src.[!pos] in
    if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
      incr pos
    else if c = '-' && !pos + 1 < len && src.[!pos + 1] = '-' then begin
      (* line comment *)
      while !pos < len && src.[!pos] <> '\n' do incr pos done
    end
    else if is_digit c then begin
      let start = !pos in
      while !pos < len && is_digit src.[!pos] do incr pos done;
      tokens := TkNum (int_of_string (String.sub src start (!pos - start))) :: !tokens
    end
    else if is_alpha c then begin
      let start = !pos in
      while !pos < len && is_alnum src.[!pos] do incr pos done;
      tokens := TkIdent (String.sub src start (!pos - start)) :: !tokens
    end
    else begin
      (match c with
       | '\\' -> tokens := TkLambda :: !tokens
       | '('  -> tokens := TkLParen :: !tokens
       | ')'  -> tokens := TkRParen :: !tokens
       | ':'  -> tokens := TkColon :: !tokens
       | '.'  -> tokens := TkDot :: !tokens
       | ','  -> tokens := TkComma :: !tokens
       | '*'  -> tokens := TkStar :: !tokens
       | '-'  ->
         if !pos + 1 < len && src.[!pos + 1] = '>' then begin
           tokens := TkArrow :: !tokens;
           incr pos
         end else
           failwith ("Unexpected character: " ^ String.make 1 c)
       | _    -> failwith ("Unexpected character: " ^ String.make 1 c));
      incr pos
    end
  done;
  List.rev (TkEOF :: !tokens)

(* ================================================================= *)
(* 3. Parser State                                                    *)
(* ================================================================= *)

type parser_state = {
  mutable tokens : token list;
  mutable env    : string list;  (* variable name stack *)
}

let peek ps =
  match ps.tokens with
  | t :: _ -> t
  | []     -> TkEOF

let advance ps =
  match ps.tokens with
  | _ :: rest -> ps.tokens <- rest
  | []        -> ()

let expect ps tok =
  if peek ps = tok then advance ps
  else failwith ("Expected token")

let lookup_var ps name =
  let rec find i = function
    | []     -> None
    | x :: rest -> if x = name then Some i else find (i + 1) rest
  in
  find 0 ps.env

(* ================================================================= *)
(* 4. Level Parser                                                    *)
(* ================================================================= *)

let rec parse_level ps : level =
  match peek ps with
  | TkIdent s when String.length s >= 2 && s.[0] = 'L' ->
    let n = int_of_string (String.sub s 1 (String.length s - 1)) in
    advance ps;
    nat_to_level n
  | _ -> failwith "Expected level (L1, L2, ...)"

and nat_to_level = function
  | 1 -> L1
  | n when n > 1 -> LS (nat_to_level (n - 1))
  | _ -> failwith "Level must be >= 1"

(* ================================================================= *)
(* 5. Type Parser                                                     *)
(* ================================================================= *)

let rec parse_ty ps : ty =
  let t = parse_ty_product ps in
  match peek ps with
  | TkArrow -> advance ps; TyArrow (t, parse_ty ps)
  | _       -> t

and parse_ty_product ps : ty =
  let t = parse_ty_atom ps in
  match peek ps with
  | TkStar -> advance ps; TyPair (t, parse_ty_product ps)
  | _      -> t

and parse_ty_atom ps : ty =
  match peek ps with
  | TkIdent "Nat"     -> advance ps; TyNat
  | TkIdent "Process" -> advance ps; TyProcess (parse_ty_atom ps)
  | TkIdent "Layer"   -> advance ps; TyLayer (parse_ty_atom ps)
  | TkIdent "System"  -> advance ps; TySystem (parse_level ps)
  | TkLParen ->
    advance ps;
    let t = parse_ty ps in
    expect ps TkRParen;
    t
  | _ -> failwith "Expected type"

(* ================================================================= *)
(* 6. Expression Parser                                               *)
(* ================================================================= *)

(** Parse a complete expression *)
let rec parse_expr ps : expr_ann =
  parse_app ps

(** Parse application (left-associative) *)
and parse_app ps : expr_ann =
  let f = parse_atom ps in
  parse_app_rest ps f

and parse_app_rest ps f : expr_ann =
  match peek ps with
  | TkNum _ | TkIdent _ | TkLParen | TkLambda ->
    let a = parse_atom ps in
    parse_app_rest ps (EAApp (f, a))
  | _ -> f

(** Parse atomic expression *)
and parse_atom ps : expr_ann =
  match peek ps with
  | TkNum n ->
    advance ps; EAConst n

  | TkIdent "fst" ->
    advance ps; EAFst (parse_atom ps)

  | TkIdent "snd" ->
    advance ps; EASnd (parse_atom ps)

  | TkIdent "observe" ->
    advance ps;
    let e = parse_atom ps in
    (match peek ps with
     | TkNum n -> advance ps; EAObserve (e, n)
     | _       -> failwith "observe expects expression and number")

  | TkIdent "resolve" ->
    advance ps; EAResolve (parse_atom ps)

  | TkIdent "system" ->
    advance ps; EASystem (parse_level ps)

  | TkIdent name ->
    advance ps;
    (match lookup_var ps name with
     | Some i -> EAVar i
     | None   -> failwith ("Unbound variable: " ^ name))

  | TkLambda ->
    advance ps;
    expect ps TkLParen;
    let var_name = match peek ps with
      | TkIdent s -> advance ps; s
      | _         -> failwith "Expected variable name after \\("
    in
    expect ps TkColon;
    let ty = parse_ty ps in
    expect ps TkRParen;
    expect ps TkDot;
    ps.env <- var_name :: ps.env;
    let body = parse_expr ps in
    ps.env <- List.tl ps.env;
    EALamAnn (ty, body)

  | TkLParen ->
    advance ps;
    let e1 = parse_expr ps in
    (match peek ps with
     | TkComma ->
       advance ps;
       let e2 = parse_expr ps in
       expect ps TkRParen;
       EAPair (e1, e2)
     | TkRParen ->
       advance ps; e1
     | _ -> failwith "Expected ',' or ')' after expression")

  | _ -> failwith "Unexpected token"

(* ================================================================= *)
(* 7. Public API                                                      *)
(* ================================================================= *)

(** Parse a string into an annotated expression *)
let parse (source : string) : expr_ann option =
  try
    let toks = tokenize source in
    let ps = { tokens = toks; env = [] } in
    let e = parse_expr ps in
    (match peek ps with
     | TkEOF -> Some e
     | _     -> None)  (* trailing tokens = error *)
  with _ -> None

(** Parse and immediately erase annotations (for plain Expr) *)
let parse_and_erase (source : string) : Expressions.expr option =
  match parse source with
  | Some ea -> Some (erase_ann ea)
  | None    -> None
