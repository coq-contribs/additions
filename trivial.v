(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(*                       trivial.v                                          *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* the trivial monoid *)
Require Import monoid.
Require Import Plus.

Lemma trivial : monoid nat.
refine (mkmonoid nat 0 plus _ _ _); auto with arith.
(*
 Realizer (mkmonoid nat O plus).
 Program_all.
*)
Defined.

Lemma obsolete_debug : forall n : nat, power nat trivial n 1 = n.
 simpl in |- *; auto with arith.
Qed.

