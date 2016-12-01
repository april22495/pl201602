Require Export P07.



(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof. 
  unfold bequiv, cequiv.
  intros. split.
  - intros. inversion H2; subst.
    + simpl. apply E_IfTrue. rewrite <- H. assumption. apply H0. assumption.
    + apply E_IfFalse. rewrite <- H. assumption. apply H1. assumption.
  - intros. inversion H2; subst.
    + apply E_IfTrue. rewrite H. assumption. apply H0. assumption.
    + apply E_IfFalse. rewrite H. assumption. apply H1. assumption.
Qed.

