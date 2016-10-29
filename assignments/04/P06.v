Require Export P01.



Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  y = z.
Proof. 
  intros X x y z l j e1 e2.
  inversion e1. inversion e2.  rewrite <-H0. reflexivity. 
Qed.

