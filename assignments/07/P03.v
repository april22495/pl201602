Require Export P02.

(*Software Foundations - Imp*)

(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq(optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe(optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1)(optimize_0plus_b b2)
  end.
  
Example optimize_0plus_b_example1:
  optimize_0plus_b (BEq 
     (AMult (APlus (ANum 0) (APlus (ANum 0) (ANum 3)))
            (AMinus (ANum 5) (APlus (ANum 0) (ANum 1))))
     (APlus (ANum 2)
            (APlus (ANum 0)
                   (APlus (ANum 0) (ANum 1)))))
  = (BEq (AMult (ANum 3) (AMinus (ANum 5) (ANum 1)))
         (APlus (ANum 2) (ANum 1))).
Proof. simpl. reflexivity. Qed.  

Theorem optimize_0plus_aexp_sound: forall st a,
aeval st (optimize_0plus_aexp a)=aeval st a.
Proof.
  intros.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n.
      * simpl. rewrite IHa2. reflexivity.
      * induction a2. simpl. 

Theorem optimize_0plus_b_sound : forall st b,
  beval st (optimize_0plus_b b) = beval st b.
Proof.  
  intros.
  destruct b;
  try (simpl; reflexivity).
  simpl.
  
Qed.

