(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ----                          standard.v                           ----*)

(* Author: Pierre Casteran.                                               *)
(*    LABRI, URA CNRS 1304,                                               *)
(*    Departement d'Informatique, Universite Bordeaux I,                  *)
(*    33405 Talence CEDEX,                                                *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                               *)





(* standard monoid *)
Require Import monoid.
Require Import Mult.

Lemma standard : monoid nat.
refine (mkmonoid nat 1 mult _ _ _); auto with arith.
(*
 Realizer (mkmonoid nat (S O) mult).
 Program_all.
*)
Defined.

