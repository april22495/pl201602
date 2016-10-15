Require Export D.



(** **** Problem #7 : 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
           match l with
           | []=>([],[])
           |hd::tl=> (pair ((fst hd)::(fst (split tl))) ((snd hd)::(snd (split tl))) )
           end.
  

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.


Lemma maplist: forall X Y (x:X) (f:X->Y) (l:list X),
  map f (x::l) = (f x):: (map f l).
Proof. 
  intros X Y x f l.
  - simpl. reflexivity.
Qed.

Theorem split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.
Proof.
  intros X Y l.
  induction l as [| hd tl InH].
  - simpl. reflexivity.
  - rewrite -> maplist. rewrite <- InH. simpl. reflexivity.
Qed.

