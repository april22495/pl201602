Require Export P02.



Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H.
  intros nH.
  unfold not.
  intros HP.
  apply H in HP.
  unfold not in nH.
  apply nH in HP.
  inversion HP.
Qed.

