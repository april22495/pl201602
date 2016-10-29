Require Export P02.

Lemma plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
  Proof.
  intros n m.
  induction n as [| n' InH]. 
  - simpl. reflexivity.
  - simpl. rewrite -> InH. reflexivity.
Qed.


Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - destruct m. reflexivity.
    intros. inversion H.
  - intros. destruct m. inversion H.
    inversion H. rewrite <- plus_n_Sm in H1. rewrite <- plus_n_Sm in H1. inversion H1. apply IHn' in H2. rewrite H2. reflexivity. 
Qed.

