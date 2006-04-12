(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                        matrix.v                                  --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(*          2-2 matrices with natural coefficients                          *)

(* origninal version using nat instead of Z                                 *)

Require monoid.
Require Arith.
Require Compare_dec.
Require fmpc.

Record Mat2:Set :=
  mat2{
      M11:nat;
      M12:nat;
      M21:nat;
      M22:nat}.

Definition Id2:=(mat2 (S O) O O (S O)).   

Definition Mat_mult:=[M,M':Mat2]
                      (mat2 (plus (mult (M11 M) (M11 M'))
                                  (mult (M12 M) (M21 M'))  )
                            (plus (mult (M11 M) (M12 M'))
                                  (mult (M12 M) (M22 M'))  )
                            (plus (mult (M21 M) (M11 M'))
                                  (mult (M22 M) (M21 M'))  )
                            (plus (mult (M21 M) (M12 M'))
                                  (mult (M22 M) (M22 M'))  )).


Well_Known Mat_assoc: (M,M',M'':Mat2)
                       (Mat_mult M (Mat_mult M' M''))=
                       (Mat_mult (Mat_mult M M') M'').


Lemma matrix:(monoid Mat2).
 Refine (mkmonoid Mat2 Id2 Mat_mult ? ? ?).
(*
 Realizer (mkmonoid Mat2 Id2 Mat_mult).
 Program_all.
*)
 Exact Mat_assoc.
 Induction a. 
  Intros.
  Unfold Id2 Mat_mult;Simpl.
  Repeat Elim plus_n_O .
  Auto with v62.
  Induction a. 
  Intros.
  Unfold Id2 Mat_mult;Simpl.
  Repeat Elim mult_n_O .
  Repeat Rewrite mult_n_1. 
  Simpl;Repeat Elim plus_n_O.
  Auto with v62.
Defined.

(* Fibonacci numbers *)

(* definition *)

Fixpoint Fib[n:nat]:nat :=
    <nat>Case n of (* O *) (S O)
                         (* (S p ) *) [p:nat]
                                     <nat>Case p of (* O *) (S O)
                                                    (* S q *)
                                                   [q:nat](plus (Fib q)
                                                                (Fib p))
                                     end
           end.

Lemma Unfold_FibO:(Fib O)=(S O).
Proof.
 Unfold Fib;Simpl;Auto with v62.
Qed.

Lemma Unfold_Fib1:(Fib (S O))=(S O).
Proof.
 Unfold Fib;Simpl;Auto with v62.
Qed.

Lemma Unfold_FibSSn:(n:nat)(Fib (S (S n)))=(plus (Fib (S n)) (Fib (n))).
Proof.
 Intro n;Unfold 1 Fib.
 Simpl;Auto with v62.
Qed.


(* A "Decaled" Fibonnacci function *)

Definition shift_Fib:=[n:nat]<nat>Case n of O [p:nat](Fib p) end.

Lemma Unfold_shift_Fib:(n:nat)(shift_Fib (S n))=(Fib n).
Proof.
 Intro n;Unfold shift_Fib;Auto with v62.
Qed.

Lemma Simpl_shift_Fib:(n:nat)(shift_Fib (S (S n)))=
                             (plus (shift_Fib (S n)) (shift_Fib n)).
Proof.
 Induction n.
 Unfold shift_Fib Fib;Simpl;Auto with v62.
 Intros.
 Unfold shift_Fib.
 Rewrite Unfold_FibSSn;Auto with v62.
Qed.


Definition fib_mat:=(mat2 (S O) (S O) (S O) O).


Lemma fib_mat_n:(n:nat)(a,b,d:nat)
        (power Mat2 matrix fib_mat n)=(mat2 a b b d)
     -> (power Mat2 matrix fib_mat (S n))=
                                      (mat2 (plus a b) (plus b d) a b).
Proof.
 Intros;Simpl.
 Rewrite H.
 Unfold Mat_mult.
 Simpl.
 Repeat Elim plus_n_O.
 Auto with v62.
Qed.

Lemma fib_n:(n:nat)
             (power Mat2 matrix fib_mat (S n))=
                   (mat2 (shift_Fib (S (S n)))
                         (shift_Fib (S n))
                         (shift_Fib (S n))
                         (shift_Fib n)).
Proof.
 Induction n.
 Unfold power shift_Fib o u ;Simpl.
 Unfold fib_mat;Simpl.
 Unfold Mat_mult Id2;Simpl;Auto with v62.
 Intros.
 Rewrite (fib_mat_n (S n0) ? ? ? H).
 Rewrite (Simpl_shift_Fib (S n0)).
 Pattern 4 (shift_Fib (S (S n0))).
 Rewrite (Simpl_shift_Fib n0).
 Auto with v62.
Qed.


Lemma fib_computation:(n:nat)(lt O n)->
         (Fib n)=
         (M11 (power Mat2 matrix fib_mat n)).
Proof.
 Induction n.
 Intro;Absurd (lt O O);Auto with v62.
 Intros.
 Rewrite fib_n;Unfold M11;Auto with v62.
Qed.
