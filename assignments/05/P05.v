Require Export P04.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros H2.
  inversion H2.
  apply H0 in H.
  inversion H.
Qed. 
