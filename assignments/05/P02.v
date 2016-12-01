Require Export P01.



Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n.
  induction n as [| n'].
  - left. reflexivity.
  - intros. induction m as [| m'].
  right. reflexivity. 
  inversion H.
Qed.

