Require Export P02.



(** **** Problem : 2 stars (double_plus) *)

(* See [D.v] for the definition of [double] *)

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
intros.
induction n.
- reflexivity.
- simpl. rewrite <- plus_n_Sm. rewrite IHn. reflexivity.
Qed.

