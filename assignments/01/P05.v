Require Export P04.

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite ->H.
  rewrite ->H.
  destruct b as [true |false ].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
