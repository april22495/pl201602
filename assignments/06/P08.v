Require Export P07.



(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq {X: Type}: list X -> list X -> Prop :=
| empty : forall xl, subseq [] xl
| found : forall (hd:X) (tl1 tl2: list X), subseq tl1 tl2 -> subseq (hd::tl1) (hd::tl2)
| pass hd tl1 tl2: subseq tl1 tl2->subseq tl1 (hd::tl2)
.

Example subseq_ex1: subseq [1;2;3] [1;2;3].
Proof. apply found. apply found. apply found. apply empty.
Qed. 
Example subseq_ex2: subseq [1;2;3] [1;1;1;2;2;3].
Proof. apply found. apply pass. apply pass. apply found. apply pass. apply found. apply empty.
Qed. 
Example subseq_ex3: subseq [1;2;3] [1;2;7;3].
Proof. apply found. apply found. apply pass. apply found. apply empty. Qed.

Example subseq_ex4: subseq [1;2;3] [5;6;1;9;9;2;7;3;8].
Proof. repeat constructor. Qed.

Example subseq_ex5: ~ subseq [1;2;3] [1;2].
Proof.
  intro H; repeat match goal with [H: subseq _ _ |- _] => inversion_clear H end. 
Qed.

Example subseq_ex6: ~ subseq [1;2;3] [1;3].
Proof.
intro H; repeat match goal with [H: subseq _ _ |- _] => inversion_clear H end.
Qed.

Example subseq_ex7: ~ subseq [1;2;3] [5;6;2;1;7;3;8].
Proof.
 intro H; repeat match goal with [H: subseq _ _ |- _] => inversion_clear H end.
Qed.

Lemma subseq_refl: forall X (l: list X), 
  subseq l l.
Proof. intros. induction l. 
apply empty.
apply found. apply IHl.  
Qed.

Lemma l_app_nil: forall X (l: list X), l++[]=l.
Proof. intros. induction l. simpl. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_cons_cons_app: forall X (h:X) (t l : list X), (h::t)++l=h::(t++l).
Proof. intros. reflexivity. 
Qed.  
Lemma subseq_app: forall X (l1 l2 l3: list X)
    (SUB: subseq l1 l2),
  subseq l1 (l2++l3).
Proof. 
intros. induction SUB. 
- apply empty.
- rewrite app_cons_cons_app. apply found. apply IHSUB.
- rewrite app_cons_cons_app.  apply pass. apply IHSUB. 
Qed.

