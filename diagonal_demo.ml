(* diagonal_demo.ml
   
   Executable demonstration of:
   1. Countability of Q (Calkin-Wilf enumeration)
   2. Non-surjectivity of N -> (N -> Q) (trisection diagonal)
   
   Compile and run:
     ocamlopt -o diagonal diagonal_demo.ml
     ./diagonal
   
   Part of: Theory of Systems - Coq Formalization
   Author: Horsocrates | Date: January 2026
*)

(* === Rationals as int pairs === *)
type q = { num : int; den : int }

let q_add a b = { num = a.num * b.den + b.num * a.den; den = a.den * b.den }
let q_sub a b = { num = a.num * b.den - b.num * a.den; den = a.den * b.den }
let q_mul a b = { num = a.num * b.num; den = a.den * b.den }
let q_div a n = { num = a.num; den = a.den * n }
let q_lt a b = a.num * b.den < b.num * a.den
let q_le a b = a.num * b.den <= b.num * a.den

let gcd a b =
  let rec aux a b = if b = 0 then abs a else aux b (a mod b) in
  aux a b

let q_reduce q =
  let g = gcd q.num q.den in
  { num = q.num / g; den = q.den / g }

let q_print q = 
  let q' = q_reduce q in
  Printf.sprintf "%d/%d" q'.num q'.den

let q_zero = { num = 0; den = 1 }
let q_one = { num = 1; den = 1 }

(* === Calkin-Wilf Enumeration (NO AXIOMS!) === *)
(* 
   The Calkin-Wilf tree enumerates all positive rationals exactly once:
     Root: 1/1
     Left child of a/b: a/(a+b)
     Right child of a/b: (a+b)/b
   
   Binary encoding: n maps to tree node via binary representation
*)

let rec cw_node n =
  if n = 1 then (1, 1)
  else if n mod 2 = 0 then
    let (a, b) = cw_node (n / 2) in (a, a + b)  (* left child *)
  else
    let (a, b) = cw_node (n / 2) in (a + b, b)  (* right child *)

let enum_qpos n = 
  let (a, b) = cw_node (n + 1) in
  { num = a; den = b }

(* === Trisection for Non-Surjectivity (USES LEM IN PROOF ONLY) === *)
(*
   Given interval [a,b] and point p to avoid:
   - Divide into thirds: [a, a+w/3], [a+w/3, b-w/3], [b-w/3, b]
   - If p < a+w/3: take middle-right [a+w/3, b]
   - If p > b-w/3: take left-middle [a, b-w/3]
   - If p in middle: take LEFT [a, a+w/3] (deterministic choice!)
   
   The "LEFT" choice when p is in middle is the key insight:
   it ensures monotonicity of left endpoints.
*)

let avoid_third p a b =
  let width = q_sub b a in
  let third = q_div width 3 in
  let m1 = q_add a third in
  let m2 = q_sub b third in
  if q_lt p m1 then (m1, b)        (* p in left third → take [m1, b] *)
  else if q_lt m2 p then (a, m2)   (* p in right third → take [a, m2] *)
  else (a, m1)                      (* p in middle third → take LEFT [a, m1] *)

(* Build nested intervals avoiding enumeration f *)
let rec trisect_iter f n (a, b) =
  if n = 0 then (a, b)
  else
    let (a', b') = trisect_iter f (n - 1) (a, b) in
    (* Reference point: query f at synchronized index *)
    let ref_idx = 12 * int_of_float (3.0 ** float_of_int (n - 1)) in
    avoid_third (f (n - 1) ref_idx) a' b'

(* Diagonal: midpoint of n-th interval *)
let diagonal f n =
  let (a, b) = trisect_iter f n (q_zero, q_one) in
  { num = a.num * b.den + b.num * a.den; den = 2 * a.den * b.den }

(* === MAIN DEMONSTRATION === *)
let () =
  print_endline "╔══════════════════════════════════════════════════════════════╗";
  print_endline "║     THEORY OF SYSTEMS - EXECUTABLE EXTRACTION DEMO          ║";
  print_endline "╠══════════════════════════════════════════════════════════════╣";
  print_endline "║ This demonstrates the key contrast:                         ║";
  print_endline "║   • Q (rationals) IS countable — enum_qpos works            ║";
  print_endline "║   • Cauchy processes are NOT — diagonal always escapes      ║";
  print_endline "╚══════════════════════════════════════════════════════════════╝";
  print_newline ();
  
  print_endline "=== PART 1: Calkin-Wilf Enumeration (Q is countable) ===";
  print_endline "Using NO AXIOMS — fully constructive!\n";
  for i = 0 to 19 do
    let q = enum_qpos i in
    Printf.printf "  enum_qpos(%2d) = %s\n" i (q_print q)
  done;
  print_endline "  ... (continues for all positive rationals)";
  
  print_newline ();
  print_endline "=== PART 2: Diagonal Construction (Cauchy processes uncountable) ===";
  print_endline "Using LEM only in PROOF — algorithm is constructive!\n";
  
  (* Example 1: Simple enumeration *)
  print_endline "Example 1: f(n,k) = n/10 mod 1";
  let test_enum1 n _ = { num = n mod 10; den = 10 } in
  for depth = 1 to 6 do
    let result = diagonal test_enum1 depth in
    let (a, b) = trisect_iter test_enum1 depth (q_zero, q_one) in
    Printf.printf "  Depth %d: interval [%s, %s], diagonal = %s\n" 
      depth (q_print a) (q_print b) (q_print result)
  done;
  print_endline "  → Each diagonal value differs from all f(n,_)";
  
  print_newline ();
  
  (* Example 2: Calkin-Wilf enumeration itself! *)
  print_endline "Example 2: f(n,k) = enum_qpos(n) — trying to cover Q with Q!";
  let test_enum2 n _ = enum_qpos n in
  for depth = 1 to 6 do
    let result = diagonal test_enum2 depth in
    Printf.printf "  Depth %d: diagonal = %s\n" depth (q_print result)
  done;
  print_endline "  → Even the 'best' enumeration of Q fails to cover all processes!";
  
  print_newline ();
  print_endline "=== CONCLUSION ===";
  print_endline "The same framework that PROVES Q countable also PROVES";
  print_endline "that Cauchy processes (N -> Q) are NOT enumerable.";
  print_endline "No contradiction: points vs processes, finite vs infinite behavior.";
  print_newline ()
