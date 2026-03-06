(* ================================================================= *)
(*  ToS-Lang CLI — Verified Expression Checker + Evaluator            *)
(*                                                                    *)
(*  Usage: tos_check <file.tos> [--fuel N] [--stdin]                  *)
(*                                                                    *)
(*  Pipeline:                                                         *)
(*    1. Parse source      (parser.ml — unverified)                   *)
(*    2. Type check        (TypeChecker.ml — VERIFIED, extracted Coq) *)
(*    3. Evaluate          (Evaluator.ml — VERIFIED, extracted Coq)   *)
(*    4. Output result     (printer.ml — unverified)                  *)
(*                                                                    *)
(*  Steps 2+3 are PROVEN CORRECT by Coq:                             *)
(*    typecheck_sound, type_safety, verified_pipeline                  *)
(*                                                                    *)
(*  Author: Horsocrates | 2026-03-06                                  *)
(* ================================================================= *)

open Typing_Expr
open TypeChecker
open Evaluator
open Parser
open Printer

(* ================================================================= *)
(* 1. File I/O                                                        *)
(* ================================================================= *)

let read_file filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

let read_stdin () =
  let buf = Buffer.create 1024 in
  (try while true do
    Buffer.add_string buf (input_line stdin);
    Buffer.add_char buf '\n'
  done with End_of_file -> ());
  Buffer.contents buf

(* ================================================================= *)
(* 2. CLI Argument Parsing                                            *)
(* ================================================================= *)

type config = {
  source_file : string option;
  use_stdin   : bool;
  fuel        : int;
  show_ast    : bool;
}

let default_config = {
  source_file = None;
  use_stdin   = false;
  fuel        = 1000;
  show_ast    = false;
}

let parse_args () =
  let cfg = ref default_config in
  let args = Array.to_list Sys.argv |> List.tl in
  let rec loop = function
    | [] -> ()
    | "--stdin" :: rest ->
      cfg := { !cfg with use_stdin = true }; loop rest
    | "--fuel" :: n :: rest ->
      cfg := { !cfg with fuel = int_of_string n }; loop rest
    | "--ast" :: rest ->
      cfg := { !cfg with show_ast = true }; loop rest
    | "--help" :: _ | "-h" :: _ ->
      Printf.printf "Usage: tos_check <file.tos> [--fuel N] [--stdin] [--ast]\n";
      Printf.printf "\n";
      Printf.printf "  <file.tos>   ToS-Lang source file\n";
      Printf.printf "  --stdin      Read from stdin instead of file\n";
      Printf.printf "  --fuel N     Maximum evaluation steps (default: 1000)\n";
      Printf.printf "  --ast        Show parsed AST\n";
      Printf.printf "\n";
      Printf.printf "Pipeline: parse -> typecheck (VERIFIED) -> eval (VERIFIED) -> output\n";
      Printf.printf "Type checker and evaluator extracted from Coq proofs.\n";
      Printf.printf "Backing theorems: typecheck_sound, type_safety, verified_pipeline\n";
      exit 0
    | f :: rest ->
      cfg := { !cfg with source_file = Some f }; loop rest
  in
  loop args; !cfg

(* ================================================================= *)
(* 3. Main Pipeline                                                   *)
(* ================================================================= *)

let () =
  let cfg = parse_args () in

  (* Read source *)
  let source =
    if cfg.use_stdin then read_stdin ()
    else match cfg.source_file with
      | Some f -> read_file f
      | None   ->
        Printf.eprintf "Error: no input file. Use --help for usage.\n";
        exit 1
  in

  (* Step 1: Parse (unverified) *)
  let expr_ann = match Parser.parse source with
    | Some ea -> ea
    | None    ->
      Printf.eprintf "Parse error: could not parse input\n";
      exit 1
  in

  if cfg.show_ast then
    Printf.printf "AST: %s\n" (print_expr_ann expr_ann);

  (* Erase annotations for the verified pipeline *)
  let expr = erase_ann expr_ann in

  (* Step 2: Type check (VERIFIED — extracted from Coq, proven sound) *)
  (* Theorem: typecheck_sound — typecheck G e = Some T -> expr_has_type G e T *)
  let ty = match typecheck_ann [] expr_ann with
    | Some t -> t
    | None   ->
      Printf.eprintf "Type error: expression is ill-typed\n";
      Printf.eprintf "Expression: %s\n" (print_expr expr);
      exit 1
  in

  Printf.printf "Type: %s\n" (print_ty ty);

  (* Step 3: Evaluate (VERIFIED — extracted from Coq, type-preserving) *)
  (* Theorem: verified_pipeline — typecheck OK -> eval preserves type + progress *)
  let result = classify_eval cfg.fuel expr in
  (match result with
   | ER_Value (v, _) ->
     Printf.printf "Value: %s\n" (print_expr v);
     Printf.printf "Certificate: well-typed, E/R/R well-formed, no paradox (Coq-proven)\n";
     Printf.printf "Backing: typecheck_sound + type_safety + verified_pipeline\n"
   | ER_Partial (e', _) ->
     Printf.printf "Partial (fuel=%d exhausted): %s\n" cfg.fuel (print_expr e');
     Printf.printf "Type preserved: %s (Coq-proven)\n" (print_ty ty)
   | ER_TypeError ->
     (* This should be unreachable: we already checked types above *)
     Printf.eprintf "Internal error: passed typecheck_ann but classify_eval failed\n";
     Printf.eprintf "This indicates a bug in annotation erasure or type checker.\n";
     exit 2)
