Require Export P08.



Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n. 
  induction l as [| hd tl InH]. 
  - simpl. reflexivity.
  - simpl. rewrite -> InH. reflexivity.  
Qed.

