Require Export P02.



(** **** Problem : 2 stars (double_plus) *)

(* See [D.v] for the definition of [double] *)

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  intros n.
  induction n as [| n' InH].
  simpl. reflexivity.
  simpl. rewrite -> InH. rewrite -> plus_n_Sm. reflexivity.
Qed.

