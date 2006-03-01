(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(*                              monofun.v                                   *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(* the monoid of functions from A to A *)
(***************************************)
Require Import monoid.

Section fun_.
 Variable A : Set.
 Hypothesis eta_A : forall f g : A -> A, (forall x : A, f x = g x) -> f = g.

 Let comp (f g : A -> A) (x : A) := g (f x).
 Let Id (a : A) := a.

 Lemma funmono : monoid (A -> A).
  Proof.
  refine (mkmonoid (A -> A) Id comp _ _ _); auto.
 Defined.
End fun_.



