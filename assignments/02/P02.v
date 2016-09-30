Require Export P01.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. 
  intros n m p.
  rewrite -> plus_comm.   rewrite -> plus_comm. 
  induction n as [ | n' InH]. simpl. reflexivity.
  simpl. rewrite->InH. reflexivity.
Qed.

