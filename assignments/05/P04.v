Require Export P03.



Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R.
  split.
  + intros [H1 | [H2 H3]].
  - split. left. apply H1. left. apply H1.
  - split. right. apply H2. right. apply H3.
  + intros [H1 H2].
  destruct H1.
  clear H2.
  left. apply H. destruct H2. left. apply H0. right. split. apply H. apply H0.
  Qed.
  
