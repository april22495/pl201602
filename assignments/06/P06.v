Require Export P05.



(** **** Exercise: 4 stars, advanced (ev_alternate)  *)
(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

(*
Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).
*)

(** Prove that this definition is logically equivalent to
    the old one. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
intros n. split.
-  intros H. induction H.
  + apply ev_0. 
  + apply ev_SS. apply ev_0.
  + apply ev_sum. apply IHev'1. apply IHev'2. 
- intros. induction H. 
  + apply ev'_0. 
  + apply ev'_sum with (n := 2) (m := n). apply ev'_2. apply IHev. 
Qed. 
