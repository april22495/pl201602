Require Export P04.



Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof. 
  intros.
  induction l.
  simpl in H. inversion H.
  destruct (test x0) eqn: case.
  inversion H. rewrite case in H1. inversion H1. rewrite H2 in case. apply case.
  inversion H. rewrite case in H1. apply IHl in H1. apply H1.
 Qed.
