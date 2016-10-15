Require Export P09.
Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Lemma snoc_rev_nat: forall (l: natlist) (v: nat),
  snoc (rev l) v= rev(v::l).
Proof.
  intros l v. induction l as [ | hd tl].
  - simpl. reflexivity. 
  - simpl. reflexivity. 
Qed.  

(*Lemma *)

(*  *)
Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof. 
  intros l1 l2.
  induction l1 as [| hd tl InH].
  - simpl. induction l2 as [| hd' tl' InH']. 
            simpl. reflexivity.
            simpl. rewrite -> snoc_rev_nat. rewrite->app_nil_end. reflexivity.
 - simpl. rewrite -> snoc_rev_nat. rewrite -> snoc_append. rewrite <- app_assoc. 
 simpl. rewrite -> InH. rewrite->snoc_append. reflexivity.
 Qed.   
            

