Require Export D.

(*software foundations: Maps*)

(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Axiom fun_ext : forall (A B : Type) (f g : A -> B),
  (forall x : A, f x = g x) -> f = g.

Lemma t_update_shadow_x1 : forall A (m: total_map A) v1 v2 x x1,
    (t_update (t_update m x v1) x v2) x1
  = (t_update m x v2) x1.
Proof.
intros.
unfold t_update.
remember (beq_id x x1) as b.
destruct b. reflexivity. reflexivity.
Qed.

  
Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof. 
intros.
destruct x. unfold t_update. 
remember (beq_id (Id n) x') as b.
Qed.

