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
  simpl in H. rewrite case in H. inversion H. rewrite H1 in case. rewrite case. reflexivity.
  simpl in H. rewrite case in H. apply IHl in H. rewrite H. reflexivity.

 Qed.

