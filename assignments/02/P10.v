Require Export P09.



Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  
  induction l1 as [| hd tl InH].
  - simpl. induction l2 as [| hd' tl' InH']. 
            simpl. reflexivity.
            simpl. rewrite -> InH'. simpl.
Qed.

