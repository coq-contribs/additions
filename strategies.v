(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                            strategies.v                          --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(*  
   We define here what is a strategy; We have a little restriction
   w.r.t. the paper included herein: "On Addition Schemes", in the sense
   that the strategies we consider are "deterministic", i.e.
   gamma(n) is an integer p such that 2<p<n  if  n>4, and not a 
   set of integers.

   For exemple of strategies, see the files "binary_strat.v", and
   "dicho_strat.v".

*)
Require Import Constants.

Inductive strategy : Set :=
    mkstrat :
      (forall n : nat, four < n -> {p : nat | p < n /\ two <= p}) -> strategy.






















