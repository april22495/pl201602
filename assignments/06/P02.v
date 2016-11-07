Require Export P01.



(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint beq_list {A} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1 with
  |[]=> match l2 with 
        |[]=>true
        |hd::tl=>false
        end
  |hd1::tl1=>match l2 with
             |[]=>false
             |hd2::tl2=> if (beq hd1 hd2) then (beq_list beq tl1 tl2) else false
             end
  end.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof. split.
- generalize dependent l2. generalize dependent l1.
induction l1 as [| hd1 tl1].
+ induction l2 as [| hd2 tl2].
reflexivity.
simpl. intros. inversion H0.
+ induction l2 as [| hd2 tl2].
simpl. intros. inversion H0. 
simpl. remember (beq hd1 hd2) as b1. destruct b1.
remember (beq_list beq tl1 tl2) as b2. destruct b2. intros. destruct H0.
symmetry in Heqb1. apply H with (a1:=hd1) (a2:=hd2) in Heqb1. symmetry in Heqb2. apply IHtl1 with (l2:=tl2) in Heqb2.
rewrite Heqb1. rewrite Heqb2. reflexivity.
intros. inversion H0.
intros. inversion H0.
- generalize dependent l2. generalize dependent l1.
induction l1 as [| hd1 tl1].
+ induction l2 as [| hd2 tl2].
simpl. reflexivity.
simpl. intros. inversion H0.
+ induction l2 as [| hd2 tl2].
simpl. intros. inversion H0.
intros. inversion H0. simpl. 
assert (Hh1: hd2=hd2). { reflexivity. } 
assert (Hh: beq hd2 hd2=true). { apply H with (a1:=hd2) (a2:=hd2) in Hh1. apply Hh1.  }
rewrite H3 in IHtl1.
assert (Ht1: tl2=tl2). { reflexivity. } 
assert (Ht: beq_list beq tl2 tl2=true). { apply IHtl1 with (l2:=tl2) in Ht1. apply Ht1.  } 
rewrite Hh. rewrite Ht. reflexivity. 
Qed.

