(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                        matrix.v                                  --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(*          2-2 matrices with natural coefficients                          *)

(* Ported to ZArith by P.Letouzey (nov 2001)                                *)

Require Import monoid.
Require Import Arith.
Require Import ZArith.
Require Import Compare_dec.
Require Import fmpc.

Record Mat2 : Set := mat2 {M11 : Z; M12 : Z; M21 : Z; M22 : Z}.

Definition Id2 := mat2 1 0 0 1.   

Definition Mat_mult (M M' : Mat2) :=
  mat2 (M11 M * M11 M' + M12 M * M21 M') (M11 M * M12 M' + M12 M * M22 M')
    (M21 M * M11 M' + M22 M * M21 M') (M21 M * M12 M' + M22 M * M22 M').


Axiom
  Mat_assoc :
    forall M M' M'' : Mat2,
    Mat_mult M (Mat_mult M' M'') = Mat_mult (Mat_mult M M') M''.


Lemma matrix : monoid Mat2.
 refine (mkmonoid Mat2 Id2 Mat_mult _ _ _).
(*
 Realizer (mkmonoid Mat2 Id2 Mat_mult).
 Program_all.
*)
 exact Mat_assoc.
 simple induction a. 
  intros.
  unfold Id2, Mat_mult in |- *; simpl in |- *.
  repeat elim Zplus_0_r_reverse.
  case M13; case M14; case M23; case M24; auto.
  simple induction a. 
  intros.
  unfold Id2, Mat_mult in |- *; simpl in |- *.
  repeat elim Zmult_0_r_reverse.
  repeat rewrite Zmult_1_r. 
  simpl in |- *; repeat elim Zplus_0_r_reverse.
  auto with arith.
Defined.

(* Fibonacci numbers *)

(* definition *)

Fixpoint Fib (n : nat) : nat :=
  match n return nat with
  | O => (* O *)  1
      (* (S p ) *) 
  | S p =>
      match p return nat with
      | O => (* O *)  1
          (* S q *)
      | S q => Fib q + Fib p
      end
  end.

Lemma Unfold_FibO : Fib 0 = 1.
Proof.
 unfold Fib in |- *; simpl in |- *; auto with arith.
Qed.

Lemma Unfold_Fib1 : Fib 1 = 1.
Proof.
 unfold Fib in |- *; simpl in |- *; auto with arith.
Qed.

Lemma Unfold_FibSSn : forall n : nat, Fib (S (S n)) = Fib (S n) + Fib n.
Proof.
 intro n; unfold Fib at 1 in |- *.
 simpl in |- *; auto with arith.
Qed.


(* A "Decaled" Fibonnacci function *)

Definition shift_Fib (n : nat) :=
  match n return nat with
  | O => 0
  | S p => Fib p
  end.

Lemma Unfold_shift_Fib : forall n : nat, shift_Fib (S n) = Fib n.
Proof.
 intro n; unfold shift_Fib in |- *; auto with arith.
Qed.

Lemma Simpl_shift_Fib :
 forall n : nat, shift_Fib (S (S n)) = shift_Fib (S n) + shift_Fib n.
Proof.
 simple induction n.
 unfold shift_Fib, Fib in |- *; simpl in |- *; auto with arith.
 intros.
 unfold shift_Fib in |- *.
 rewrite Unfold_FibSSn; auto with arith.
Qed.


Definition fib_mat := mat2 1 1 1 0.


Lemma fib_mat_n :
 forall (n : nat) (a b d : Z),
 power Mat2 matrix fib_mat n = mat2 a b b d ->
 power Mat2 matrix fib_mat (S n) = mat2 (a + b) (b + d) a b.
Proof.
 intros; simpl in |- *.
 rewrite H.
 unfold Mat_mult in |- *.
 simpl in |- *.
 repeat elim Zplus_0_r_reverse.
 case a; case b; case d; auto.
Qed.

Lemma fib_n :
 forall n : nat,
 power Mat2 matrix fib_mat (S n) =
 mat2 (Z_of_nat (shift_Fib (S (S n)))) (Z_of_nat (shift_Fib (S n)))
   (Z_of_nat (shift_Fib (S n))) (Z_of_nat (shift_Fib n)).
Proof.
 simple induction n.
 unfold power, shift_Fib, o, u in |- *; simpl in |- *.
 unfold fib_mat in |- *; simpl in |- *.
 unfold Mat_mult, Id2 in |- *; simpl in |- *; auto with arith.
 intros.
 rewrite (fib_mat_n (S n0) _ _ _ H).
 repeat rewrite <- Znat.inj_plus.
 rewrite (Simpl_shift_Fib (S n0)).
 pattern (shift_Fib (S (S n0))) at 4 in |- *.
 rewrite (Simpl_shift_Fib n0).
 auto with arith.
Qed.


Lemma fib_computation :
 forall n : nat,
 0 < n -> Z_of_nat (Fib n) = M11 (power Mat2 matrix fib_mat n).
Proof.
 simple induction n.
 intro; absurd (0 < 0); auto with arith.
 intros.
 rewrite fib_n; unfold M11 in |- *; auto with arith.
Qed.