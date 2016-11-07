Require Export P04.



(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.  intros n m.
  intros E1 E2.
  induction E1.
  - simpl. apply E2.
  - simpl. apply ev_SS. apply IHE1.
Qed.

