Require Import EF.Expressions EF.ComputationalSystem.

From Coq Require Import Lists.List PeanoNat Program.Tactics Logic.Eqdep_dec.
Import ListNotations.

Lemma inj_pair2_nat (P : nat -> Type) (n : nat) (x y : P n) :
  existT P n x = existT P n y -> x = y.
Proof. apply inj_pair2_eq_dec. apply Nat.eq_dec. Qed.

Inductive foperation : Set :=
  | FConst (n : nat)
  | FSucc
  | FFlip
  | FOnDoElse (condition : list nat) (then_ else_ : foperation).

Variant fprimitive : Set :=
  | FOp  (operation : foperation)
  | FNat (n : nat).

Inductive foperation_reduces : foperation -> nat -> nat -> Prop :=
  | FRConst n m :
      foperation_reduces (FConst n) m n
  | FRSucc n :
      foperation_reduces FSucc n (S n)
  | FRFlip0 n :
      foperation_reduces FFlip n 0
  | FRFlip1 n :
      foperation_reduces FFlip n 0
  | FROnDoElseIn condition then_ else_ arg result :
        In arg condition ->
        foperation_reduces then_ arg result ->
      foperation_reduces (FOnDoElse condition then_ else_) arg result
  | FROnDoElseNotIn condition then_ else_ arg result :
        ~In arg condition ->
        foperation_reduces else_ arg result ->
      foperation_reduces (FOnDoElse condition then_ else_) arg result.

Variant fprimitive_reduces : fprimitive -> code fprimitive -> unit ->
                               code fprimitive -> unit -> Prop :=
  | FPR operation n m :
        foperation_reduces operation n m ->
      fprimitive_reduces (FOp operation) (CPrimitive (FNat n)) tt (CPrimitive (FNat m)) tt.

Variant fprimitive_terminates : fprimitive -> code fprimitive -> unit -> Prop :=
  | FPT operation n :
      fprimitive_terminates (FOp operation) (CPrimitive (FNat n)) tt.

Lemma fprimitive_progress pf ca (s : unit) :
    fprimitive_terminates pf ca s ->
  exists cr s',
    fprimitive_reduces pf ca s cr s'.
Proof.
  intro Hterm. destruct pf; inv Hterm.
  induction operation; try (repeat econstructor; fail).
  (* remaining case: FOnDoElse *)
  destruct (in_dec Nat.eq_dec n condition) as [HIn | HnotIn].
  + destruct IHoperation1 as [cr [[] Hred]]. inv Hred.
    eexists. eexists. constructor. eapply FROnDoElseIn; eassumption.
  + destruct IHoperation2 as [cr [[] Hred]]. inv Hred.
    eexists. eexists. constructor. eapply FROnDoElseNotIn; eassumption.
Qed.

Obligation Tactic := intros; constructor.

Program Definition flip_computational_system : computational_system := {|
  cprimitive            := fprimitive;
  cstate                := unit;
  cstate_nonempty       := tt;
  cprimitive_reduces    := fprimitive_reduces;
  cprimitive_terminates := fprimitive_terminates;
  cpossible_future      := fun _ _ => True
|}.

Definition fcode :           Type := ccode flip_computational_system.
Definition fexpr (n : nat) : Type := cexpr flip_computational_system n.

Definition flip_top_separator : separator flip_computational_system :=
  @top_separator flip_computational_system fprimitive_progress.

Inductive hole_foperation : Set :=
  | HHole
  | HConst (n : nat)
  | HSucc
  | HFlip
  | HOnDoElse (condition : list nat) (then_ else_ : hole_foperation).

Variant hole_fprimitive : Set :=
  | HNat (n : nat)
  | HOp (operation : hole_foperation).

Definition hole_fcode :           Type := code hole_fprimitive.
Definition hole_fexpr (n : nat) : Type := expr hole_fcode n.

Section Subst.

Variable os : foperation.

Fixpoint osubst_hole (oh : hole_foperation) : foperation :=
  match oh with
  | HHole                      => os
  | HConst n                   => FConst n
  | HSucc                      => FSucc
  | HFlip                      => FFlip
  | HOnDoElse condition then_ else_ => FOnDoElse condition (osubst_hole then_) (osubst_hole else_)
  end.

Definition psubst_hole (ph : hole_fprimitive) : fprimitive :=
  match ph with
  | HNat n => FNat n
  | HOp operation => FOp (osubst_hole operation)
  end.

Definition esubst_hole_aux {n : nat} (csubst_hole : hole_fcode -> code fprimitive) :
                             hole_fexpr n -> fexpr n :=
  fix esubst_hole_aux (eh : hole_fexpr n) :=
  match eh with
  | ECode ch => ECode (csubst_hole ch)
  | EVar i   => EVar i
  | ef * ea  => esubst_hole_aux ef * esubst_hole_aux ea
  end.

Fixpoint csubst_hole (ch : hole_fcode) : fcode :=
  match ch with
  | CPrimitive ph => CPrimitive (psubst_hole ph)
  | CLam n eh     => CLam n (esubst_hole_aux csubst_hole eh)
  end.

Definition esubst_hole {n : nat} : hole_fexpr n -> fexpr n :=
  esubst_hole_aux csubst_hole.

End Subst.

Definition finite_behavior : Set := list (nat * nat).

Axiom my_False : False.
Ltac my_admit := destruct my_False.

Lemma esubst_csubst_hole_eq (n : nat) (ch : hole_fcode) (eh : hole_fexpr (S n)) (o : foperation) :
    esubst (csubst_hole o ch) (esubst_hole o eh)
  = esubst_hole o (esubst ch eh).
Admitted.

Definition behaves (o : foperation) (b : finite_behavior) : Prop :=
  Forall (fun '(na, nr) =>  foperation_reduces o na nr) b.

Lemma freduction_depends_on_finite_behavior (chf cha : hole_fcode) (cr : fcode)
                                            (o : foperation) :
    ccode_reduces (csubst_hole o chf) (csubst_hole o cha) tt cr tt ->
  exists (b : finite_behavior) (chr : hole_fcode),
       cr = csubst_hole o chr
    /\ forall o' : foperation, behaves o' b ->
         ccode_reduces (csubst_hole o' chf) (csubst_hole o' cha) tt (csubst_hole o' chr) tt

with expr_freduction_depends_on_finite_behavior (eh : hole_fexpr 0) (cr : fcode)
                                                (o : foperation) :
    creduces (esubst_hole o eh) tt cr tt ->
  exists (b : finite_behavior) (chr : hole_fcode),
       cr = csubst_hole o chr
    /\ forall o' : foperation, behaves o' b ->
         creduces (esubst_hole o' eh) tt (csubst_hole o' chr) tt.

Proof.
  - (* freduction_depends_on_finite_behavior *)
    intro Hred. inv Hred; destruct chf; try discriminate.
    + (* RPrimitive *)
      my_admit.
    + (* RLam0 *)
      inv H. apply inj_pair2_nat in H3. subst.
      rewrite (esubst_csubst_hole_eq 0 cha e0) in H0.
      eapply expr_freduction_depends_on_finite_behavior in H0.
      my_admit.
    + (* RLamS *)
      inv H0. apply inj_pair2_nat in H2. subst.
      my_admit.
  - (* expr_freduction_depends_on_finite_behavior *)
    intro Hred. inv Hred; destruct eh; try discriminate.
    + (* RCode *)
      inv H0.
      my_admit.
    + (* RApp *)
      inv H. destruct s'. destruct s''.
      apply expr_freduction_depends_on_finite_behavior in H0.
      apply expr_freduction_depends_on_finite_behavior in H1.
      destruct H0 as [bf [chf [Ef Hredf]]]. subst.
      destruct H1 as [ba [cha [Ea Hreda]]]. subst.
      apply freduction_depends_on_finite_behavior in H2.
      my_admit.
Qed.
