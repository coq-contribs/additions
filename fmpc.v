(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(*   ---                fmpc.v           --- *)

(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(*
     This is just a little tool we used at the first steps of our development;
    "FMPC" is just a macro for "Axiom", but we used it to express facts
     that we wanted to prove later; that explains why this module is not
     used in the proof we present now; The first versions of 
     "Addition Chains: the proof" were full of FMPCs.
*)


(* Proof by intimidation *)
(***************************)

(* Not supported after V7.3 (must be moved on the ML side)
Grammar vernac vernac :=
rule1 ["FMPC" identarg($a) ":" constr:constr($term) "."] ->
[Axiom $a : $term.].

Grammar vernac vernac :=
rule2 ["Well_Known" identarg($a) ":" constr:constr($term) "."] ->
[Axiom $a : $term.].
*)

(* Examples:
   FMPC square_mono:(n,p:nat)(le n p)->(le (square n) (square p)).
   Well_Known square_mono:
       (n,p:nat)(le n p)->(le (square n) (square p)).
*)
