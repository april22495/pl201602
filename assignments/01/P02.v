Require Export P01.

(** **** Problem #2: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Use [Fixpoint] to define it. *)

Fixpoint blt_nat (n m : nat) : bool :=
  match n with
  | 0=> match m with 
        |0 => false
        |S m' => true
        end
  | S n' =>  match m with 
            | 0=> false
            | S m' => blt_nat n' m'
            end
  end.

Compute (blt_nat 2 2).

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.
