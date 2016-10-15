Require Export P01.



(** **** Problem #1 : 2 stars, optional (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | 0=> nil
  | S c'=> cons n (repeat n c')
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. simpl. reflexivity. Qed.

