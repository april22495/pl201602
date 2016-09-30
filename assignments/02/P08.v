Require Export P07.



(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Lemma snoc_rev: forall l: natlist, forall v:nat,
  rev (snoc l v)= v :: (rev l).
Proof.
  intros l v.
  induction l as [| hd tl InH].
  - simpl. reflexivity.
  - simpl. rewrite -> InH. simpl. reflexivity. 
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [ | hd tl InH].
  - simpl. reflexivity.
  - simpl. rewrite -> snoc_rev. rewrite -> InH. reflexivity. 
Qed.

