Require Export D.

Lemma plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
  Proof.
  intros n m.
  induction n as [| n' InH]. 
  - simpl. reflexivity.
  - simpl. rewrite -> InH. reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' InH].
  - simpl. induction m as [| m' InH']. 
  simpl. reflexivity. simpl. rewrite <-InH'. reflexivity.
  - simpl. rewrite -> InH. rewrite -> plus_n_Sm. reflexivity. 
  Qed.

