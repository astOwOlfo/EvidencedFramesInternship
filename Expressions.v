Ltac inv H := inversion H; subst; clear H.

Inductive Empty : Type :=.

(* [range n] is a type with [n] elements [None], [Some None], [Some (Some None)], ...
   It is used for variable indeces and is to be though of as the type of integers less than [n]. *)
Fixpoint range (n : nat) : Type :=
  match n with
  | 0    => Empty
  | S n' => option (range n')
  end.

Inductive expr (code : Type) (var_bound : nat) : Type :=
  | ECode (c :       code)
  | EVar  (i :       range var_bound)
  | EApp  (lhs rhs : expr code var_bound).

Arguments ECode {code var_bound}.
Arguments EVar  {code var_bound}.
Arguments EApp  {code var_bound}.

Fixpoint nat_to_range {k : nat} (n : nat) :
                        range (S n + k) :=
  match n with
  | 0    => None
  | S n' => Some (nat_to_range n')
  end.

Definition evar {code : Type} {n : nat} (i : nat) : expr code (S i + n) :=
  @EVar _ (S i + n) (nat_to_range i).

Notation "ef * ea" := (EApp ef ea) (at level 40, left associativity).

Fixpoint esubst {code : Type} {n : nat} (c : code) (e : expr code (S n)) : expr code n :=
  match e with
  | ECode c'        => ECode c'
  | EVar  None      => ECode c
  | EVar  (Some i') => EVar i'
  | ef * ea         => esubst c ef * esubst c ea
  end.

Definition expr_map_codes {code code' : Type} (f : code -> code') {n : nat} :
                            expr code n -> expr code' n :=
  fix expr_map_codes (e : expr code n) : expr code' n :=
  match e with
  | EVar i  => EVar i
  | ECode c => ECode (f c)
  | ef * ea => expr_map_codes ef * expr_map_codes ea
  end.

Inductive codes_in {code : Type} {n : nat} (codes : code -> Prop) : expr code n -> Prop :=
  | CICode (c : code) :
        codes c ->
      codes_in codes (ECode c)
  | CIVar  (i : range n) :
      codes_in codes (EVar i)
  | CIApp  (lhs rhs : expr code n) :
        codes_in codes lhs ->
        codes_in codes rhs ->
      codes_in codes (lhs * rhs).
