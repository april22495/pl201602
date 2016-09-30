Require Export P03.



(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.  
  intros n m p.
  induction n as [| n' InH].
  - simpl. reflexivity.
  - simpl. rewrite -> InH. rewrite -> plus_assoc. reflexivity. 
Qed.

