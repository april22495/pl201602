Require Export P06.

Lemma In_map: forall (A B: Type)(f:A->B)(x:A)(l:list A),
  In x l 
  -> In (f x) (map f l).
Proof. 
  intros A B f x l.
  induction l.
  - simpl. intros H. inversion H.
  - simpl. intros [H | H].
  + left. rewrite H. reflexivity.
  + right. apply IHl in H. apply H. 
  Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - intros H. induction l. 
  + simpl. inversion H. 
  + inversion H. 
  ++ exists a. split. apply H0. simpl. left. reflexivity.
  ++ apply IHl in H0. inversion H0. exists x. split. apply H1. simpl. right.  apply H1.
  - intros H. inversion H. destruct H0. rewrite <- H0.  apply In_map. apply H1.
  Qed.
