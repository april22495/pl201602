Require Export P04.



(** **** Problem #10 : 1 star, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.  
  intros p. destruct p. simpl. reflexivity.
Qed.

