(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ----                      binary_strat.v                           ----- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(*
  This file proves that (euclidean) division by 2 is a correct
 strategy (in the sens of or chain generation algorithm); this
 is the worst strategy (wrt. the number of multiplications used
 to compute x^n.

*)

Require Import strategies.
Require Import Arith.
Require Import euclid.
Require Import shift.
Require Import Euclid.
Require Import Le_lt_compl.
Require Import Mult_compl.
Require Import Constants.


Lemma binary : strategy.  
(********************)
Proof. 
 refine
  (mkstrat
     (fun n h => match quotient two _ n with
                 | exist n0 _ => exist _ n0 _
                 end)).
(*
 Realizer [n:nat](quotient two n) .
 Program_all.
*)
 auto with arith.
 elim e; simple induction 1; intros H1 H2.
  (* H1: n=(plus (mult n0 two) x)
     H2: (gt two x)
  *)
 case (enum1 x H2); intro H3.

 (* case of a null rest (x) *)

 cut (n = n0 * two); [ intro eg | idtac ].
 cut (two <= n0); [ intro H'1 | idtac ].
 split; auto.
 rewrite eg; apply mult_p_lt_pq.
 apply lt_le_trans with 2; auto with arith.
 auto with arith.
   (* goal: le two n0 *)
 apply not_lt_le; unfold not in |- *; intro.
 absurd (n < four); [ apply lt_asym; auto with arith | idtac ].
 rewrite eg; replace four with (two * two).
 apply mult_lt_r.
 auto with arith.
 auto with arith.
 simpl in |- *; auto with arith.
 rewrite (plus_n_O (n0 * two)); elim H3; auto with arith.

(* case of a rest = 1 *)
 cut (two <= n0); [ intro H'1 | idtac ].
 split; [ idtac | auto with arith ].
 rewrite H1; rewrite mult_comm; apply lt_b_qbr.
 rewrite H3; auto with arith.
 auto with arith.
 apply lt_le_trans with two; [ idtac | auto with arith ].
 rewrite H3; auto with arith.
 apply not_lt_le; unfold not in |- *; intro.
 cut (n <= three).
 intro; absurd (four < three);
  [ unfold four, three in |- *; auto with arith | idtac ].
 apply lt_le_trans with n; auto with arith.
 replace three with (one * two + x).
 rewrite H1; auto with arith.
 rewrite H3; simpl in |- *; auto with arith.
Qed.




