
Require Import Constants.
Require Import generation.
Require Import monoid.
Require Import machine.
Require Import strategies.
Require Import spec.
Require Import log2_spec.
Require Import log2_implementation.
Require Import Compare_dec.

Require Import while.
Require Import imperative.
Require Import develop.
Require Import dicho_strat.
Require Import binary_strat.
Require Import trivial.
Require Import standard.
Require Import monofun.
Require Import matrix.
Require Import ZArith.
Require Import main.

(*******************************)
(* generation of an ML File    *)
(*******************************)

Axiom int : Set. 
Axiom big_int : Set.
Axiom i2n : int -> nat. 
Axiom z2b : Z -> big_int. 

Extract Inlined Constant int => "int". 
Extract Constant big_int => "Big_int.big_int".

Extract Constant i2n =>
 "  
  let rec i2n = function 0 -> O | n -> (S (i2n (n-1)))
  in i2n
".


[
  Extract Constant z2b =>
   "
  let rec p2b = function 
     XH -> Big_int.unit_big_int
   | XO p -> Big_int.mult_int_big_int 2 (p2b p)
   | XI p -> Big_int.succ_big_int (Big_int.mult_int_big_int 2 (p2b p))
  in 
  function 
     Z0 -> Big_int.zero_big_int
   | Zpos p -> (p2b p)
   | Zneg p -> (Big_int.minus_big_int (p2b p))       
"
  .
   ].

Extraction Inline Wf_nat.gt_wf_rec Wf_nat.lt_wf_rec.

Extraction NoInline u o top pop.

Extraction NoInline M11 M12 M21 M22 Mat_mult.

Extraction "fibo" fibonacci int big_int i2n z2b.
