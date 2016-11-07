Require Export D.


Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
intros.
induction n as [| n'].
simpl. reflexivity. 
assert (H: forall n, evenb n= evenb(S (S n))).
{ intros. simpl. reflexivity. }
rewrite <- H with (n:=n'). rewrite IHn'. 
assert(Hb: forall b, b= negb(negb b)).
{ destruct b. simpl. reflexivity. simpl. reflexivity. }
rewrite <- Hb. reflexivity.
Qed.
(** [] *)

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof. 
  intros. induction n as [|n'].
  - simpl. exists 0. reflexivity.
  - inversion IHn'. remember (evenb n') as e. destruct e. 
  + assert(Hs: evenb(S n')=false). 
  { rewrite evenb_S with (n:= n'). rewrite <- Heqe. simpl. reflexivity. }
  rewrite Hs. exists x. rewrite H. reflexivity.
  + assert(Hs: evenb(S n')=true).
  { rewrite evenb_S with (n:=n'). rewrite <- Heqe. simpl. reflexivity.  }
  rewrite Hs. exists (S x). rewrite H. simpl. reflexivity. 
Qed.
  