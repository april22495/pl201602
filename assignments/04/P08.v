Require Export P03.

(*
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.
  

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil   => 0
  | cons h t => S (length X t)
  end.
*)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l. generalize n.
  induction l.
  - simpl. reflexivity.
  - intros. simpl in H. destruct n0. 
  simpl. inversion H.
  simpl. apply IHl. inversion H. reflexivity. 
Qed.
