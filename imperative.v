(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                           imperative.v                           --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* Usage:

     Apply Imperative with A Pre Post;[
            Realizer <init:A> |
            Realizer <body:A->A> |
            Realizer <return:A->B> ].
            
*)

  
Goal
forall (A : Set) (Pre Post : A -> Prop) (B : Set),
{a : A | Pre a} ->
(forall a : A, Pre a -> {a' : A | Post a'}) ->
(forall a : A, Post a -> B) -> B.
exact
 (fun A Pre Post B start body return_ =>
  match start with
  | exist a pre =>
      match body a pre with
      | exist a' post => return_ a' post
      end
  end).
(*
Realizer [A,B:Set][start:A][body:A->A][return:A->B]
          (return (body start)).
Program_all.
*)
Save Imperative.


