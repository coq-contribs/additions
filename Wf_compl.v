(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ----                          Wf_compl.v                           ----*)

(* Author: Pierre Casteran.                                               *)
(*    LABRI, URA CNRS 1304,                                               *)
(*    Departement d'Informatique, Universite Bordeaux I,                  *)
(*    33405 Talence CEDEX,                                                *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                               *)

(* 
   Complements on well_founded Sets 
*)

Section Prop_induction.

 Variable A : Set.
 Variable R : A -> A -> Prop.
 Hypothesis W : well_founded R.
 Hint Resolve W: arith.

 Lemma Prop_wfi :
  forall P : A -> Prop,
  (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall a : A, P a.
 (****************************************************)
 Proof.
  intros; apply (Acc_ind (R:=R) P); auto.
 Qed.

End Prop_induction.


Definition coarser (A : Set) (R S : A -> A -> Prop) :=
  forall x y : A, R x y -> S x y.

Lemma wf_coarser :
 forall (A : Set) (R S : A -> A -> Prop),
 coarser A R S -> well_founded S -> well_founded R.
(***************************)
Proof.
 unfold well_founded in |- *; intros A R S H H0 a.
 apply Acc_intro; intros y H1.
 pattern y in |- *; apply Prop_wfi with A S.
 exact H0.
 intros; apply Acc_intro; auto.
Qed.


