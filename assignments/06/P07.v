Require Export P06.



Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. unfold lt. 
intros. split.
- induction H. 
+ apply le_n_S. induction n2. rewrite <- plus_n_O.  apply le_n.
 rewrite <- plus_n_Sm. apply le_S. apply IHn2.
+ apply le_S. apply IHle.
- induction H. 
+ apply le_n_S. induction n1. rewrite plus_O_n. apply le_n.
rewrite plus_Sn_m. apply le_S. apply IHn1.
+ apply le_S. apply IHle.
Qed. 