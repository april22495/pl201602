Require Export P05.



Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. 
  intros X P Q.
  split.
  - intros H.
  inversion H.
  inversion H0.
  + left. exists x. apply H1.
  + right. exists x. apply H1.
  - intros [H1 | H2].
  + inversion H1. exists x. left. apply H.
  + inversion H2. exists x. right. apply H.
  Qed.     

