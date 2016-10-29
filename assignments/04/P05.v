Require Export D.



(** **** Problem #13 : 3 stars (apply_exercise1)  *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)
(*
Fixpoint snoc (l:list nat) (v:nat) : list nat := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Lemma snoc_rev: forall l: list nat, forall v:nat,
  rev (snoc l v)= v :: (rev l).
Proof.
  intros l v.
  induction l as [| hd tl InH].
  - simpl. reflexivity.
  - simpl. rewrite -> InH. simpl. reflexivity. 
Qed.

Lemma rev_hd_tl: forall hd: nat, forall tl: list nat,
  rev(hd::tl)=app (rev tl) [hd].
Proof.
  intros hd tl. simpl. reflexivity.
Qed. 


Theorem rev_involutive : forall l : list nat,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [ | hd tl InH].
  - simpl. reflexivity.
  - simpl. rewrite -> snoc_rev. rewrite -> InH. reflexivity. 
Qed.

*)


(*Theorem rev_involutive: forall l: list nat,
  rev(rev l)=l.
Proof.
  intros l.
  induction l as [ | hd tl Inh].
  - simpl. reflexivity.
  - simpl. 
  *)

SearchAbout rev.
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l. 
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed. 
  

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. 
  induction l1. 
  - simpl. induction l2. simpl. reflexivity. simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.


Theorem rev_involutive: forall l: list nat,
  rev(rev l)=l.
Proof.
  intros l.
  induction l as [| hd tl InH].
  - simpl. reflexivity.
  - simpl. induction tl as [ | thd ttl InH'].
      simpl. reflexivity. rewrite -> rev_app_distr. rewrite -> InH. simpl. reflexivity.
Qed.   
  
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' eq1.
  rewrite -> eq1. rewrite ->rev_involutive. reflexivity. 
  
Qed.
