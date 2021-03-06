type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool
 end

type id =
  nat
  (* singleton inductive, whose constructor was Id *)

val beq_id : id -> id -> bool

type 'a total_map = id -> 'a

val t_update : 'a1 total_map -> id -> 'a1 -> id -> 'a1

type state = nat total_map

type aexp =
| ANum of nat
| AId of id
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BLe of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

val aeval : state -> aexp -> nat

val beval : state -> bexp -> bool

type com =
| CSkip
| CAss of id * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

val ceval_step : state -> com -> nat -> state option
