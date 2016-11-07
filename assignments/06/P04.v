Require Export P03.



(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Theorem excluded_middle_to_double_negation_elimination:
  excluded_middle -> double_negation_elimination.
Proof.
unfold excluded_middle.
unfold double_negation_elimination.
intros.
unfold not in H0. destruct (H P). apply H1. unfold not in H1. apply H0 in H1. inversion H1.       
 Qed. 
 
Theorem notnot: forall P, 
 ~~ (P\/~P).
Proof.
  intros.
  unfold not. intros. apply H. right. intros. apply H. left. auto.
  Qed. 
Theorem double_negation_elimination_to_excluded_middle:
  double_negation_elimination -> excluded_middle.
Proof. 
unfold excluded_middle.
unfold double_negation_elimination.
intros.
unfold not in H. 
assert(~~(P\/~P)). { apply notnot. }
apply H in H0. apply H0.     

 Qed.

