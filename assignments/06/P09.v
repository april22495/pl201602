Require Export P08.

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof. 
intros. induction l.
- inversion H.
- destruct H. 
+ exists []. exists l. rewrite H. simpl. reflexivity.             
+ apply IHl in H. inversion H. inversion H0. 
exists (a::x0). exists x1. rewrite H1. reflexivity.       
 Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rp_base: forall x l, In x l -> repeats (x::l)
| rp_next: forall x l, repeats l -> repeats (x::l)
.


(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Lemma in_cons: forall X (x x2:X) (l: list X), 
In x l-> In x (x2::l).
Proof. intros. simpl. right. apply H.
Qed.
 
  
Lemma app_in: forall X (x:X) (l1 l2: list X),
In x (l1++l2) -> In x l1 \/ In x l2.
Proof. intros X x l1. induction l1.
simpl. intros. right. apply H.
intros. inversion H. left. rewrite H0. simpl. left. reflexivity.
apply IHl1 in H0. destruct H0. left. apply in_cons with (x2:= a) in H0. apply H0.
right. apply H0. 
Qed.

Lemma in_app: forall X (x:X) (l1 l2: list X),
In x l1 \/ In x l2-> In x (l1++l2).
Proof. intros. induction l1. simpl. inversion H. inversion H0. apply H0. 
destruct H. destruct H. 
simpl. left. apply H. 
simpl. right. apply or_introl with (B:=In x l2) in H. apply IHl1 in H. apply H.
simpl. right. apply or_intror with (A:=In x l1) in H. apply IHl1 in H. apply H.
Qed.

Lemma lem2: forall X (x0 sx: X) (x l: list X),
x0<> sx -> In x0 (x++sx::l)-> In x0 (x++l).
Proof. intros.
remember (sx::l) as l2. apply app_in in H0. destruct H0. 
- apply or_introl with (B:=In x0 l) in H0. apply in_app in H0. apply H0.
- rewrite Heql2 in H0. simpl in H0. destruct H0. 
+ rewrite H0 in H. destruct H0. destruct H. reflexivity.
+ apply or_intror with (A:=In x0 x) in H0. apply in_app in H0. apply H0.
Qed.  

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Lemma lengthlem: forall X (sx: X) (x x0: list X),
length (x ++ sx :: x0) = S (length (x ++ x0)).
Proof. intros. induction x. simpl. reflexivity.
simpl. rewrite IHx. reflexivity.
Qed.

Lemma lengthlem2: forall X (x:X)(l:list X),
length(x::l)=S(length l).
Proof. intros. simpl. reflexivity.
Qed.
    
Lemma lt: forall n m, 
S n<S m-> n<m.
Proof. intros.  inversion H. auto. apply le_S_n in H. auto. 
Qed.  
Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X sl1. induction sl1 as [|sx sl1' IHl1'].
   { unfold excluded_middle. intros. inversion H1.     }
   { intros sl2. intros.  
    destruct (H (In sx sl1')). 
    - apply rp_base. apply H2.
    - apply rp_next. 
    destruct (H (In sx sl2)).
    + apply in_split in H3. inversion H3. inversion H4.
    apply IHl1' with (l2:=(x++x0)).
    apply H.
    intros. destruct (H(x1=sx)). 
    * assert(Hn: In x1 (sx::sl1')). 
    { apply in_cons with (x2:=sx) in H6. apply H6. }
    apply (H0 (x1)) in Hn. rewrite <- H7 in H2. 
    apply contradiction_implies_anything with (P:= (In x1 sl1')) (Q:= (In x1 (x++x0))). split. apply H6. apply H2.  
    * apply in_cons with (x2:= sx) in H6. apply H0 in H6. apply lem2 with (x0:=x1) (sx:=sx) . apply H7. rewrite<- H5. apply H6.
    * assert (Hn: length sl2= S(length (x++x0))).
    { rewrite H5. apply lengthlem.  } 
    rewrite Hn in H1. rewrite lengthlem2 with (x:=sx)(l:=sl1') in H1. apply lt in H1. apply H1. 
    + apply IHl1' with (l2:=(sx::sl2)).
    apply H.
    intros. apply in_cons with (x2:=sx) in H4. apply H0 in H4. apply in_cons with (x2:=sx). apply H4.
    assert (Hn: In sx (sx::sl1')).
    { simpl. left. reflexivity. }
    apply H0 in Hn. apply contradiction_implies_anything with (P:=(In sx sl2))(Q:=(length (sx :: sl2) < length sl1')).
    split. apply Hn. apply H3.
    }
    Qed. 