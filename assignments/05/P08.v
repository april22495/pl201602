Require Export P07.



(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  |[]=> True
  |hd::tl=>(P hd)/\ (All P tl)
end.
  
Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  - intros H. induction l.
  + simpl. auto. 
  + simpl. split. 
    apply H. simpl. left. reflexivity.
    apply IHl. simpl in H. intros.
    SearchAbout or.
    apply or_intror with (A:=a=x) in H0.
    apply H in H0.
    apply H0.
  - intros. induction l as [| hd tl]. 
  + simpl in H. simpl in H0. inversion H0.
  + simpl in H0. simpl in H. destruct H0. 
  inversion H. rewrite H0 in H1. apply H1.
  inversion H. apply IHtl in H2. apply H2. apply H0.
  Qed.