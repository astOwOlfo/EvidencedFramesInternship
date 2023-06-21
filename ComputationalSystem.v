Require Import EF.Expressions.

From Coq Require Import Program.Tactics.

Inductive code (primitive : Type) : Type :=
  | CPrimitive (p : primitive)
  | CLam (n : nat) (e : expr (code primitive) (S n)).

Arguments CPrimitive {primitive} (p).
Arguments CLam       {primitive} (n e).

Section ReducesTerminates.

Context {primitive : Type} {state : Type}.
Variable primitive_reduces :    primitive -> code primitive -> state ->
                                  code primitive -> state -> Prop.
Variable primitive_terminates : primitive -> code primitive -> state -> Prop.

Inductive reduces : expr (code primitive) 0 -> state -> code primitive -> state -> Prop :=
  | RCode c s :
      reduces (ECode c) s c s
  | RApp ef ea cf ca cr s s' s'' s''' :
        reduces ef s cf s' ->
        reduces ea s' ca s'' ->
        code_reduces cf ca s'' cr s''' ->
      reduces (ef * ea) s cr s'''
      
with code_reduces : code primitive -> code primitive -> state -> code primitive -> state -> Prop :=
  | RPrimitive pf ca cr s s' :
        primitive_reduces pf ca s cr s' ->
      code_reduces (CPrimitive pf) ca s cr s'
  | RLam0 (e : expr (code primitive) 1) ca cr s s' :
        reduces (esubst ca e) s cr s' ->
      code_reduces (CLam 0 e) ca s cr s'
  | RLamS n (e : expr (code primitive) (S (S n))) ca s :
      code_reduces (CLam (S n) e) ca s (CLam n (esubst ca e)) s.

Inductive terminates : expr (code primitive) 0 -> state -> Prop :=
  | TCode c s :
      terminates (ECode c) s
  | TApp ef ea s :
        terminates ef s ->
        ( forall cf s', reduces ef s cf s' ->
              terminates ea s'
            /\ forall ca s'', reduces ea s' ca s'' ->
                 code_terminates cf ca s'' ) ->
    terminates (ef * ea) s
  
with code_terminates : code primitive -> code primitive -> state -> Prop :=
  | TPrimitive pf ca s :
        primitive_terminates pf ca s ->
      code_terminates (CPrimitive pf) ca s
  | TLam0 (e : expr (code primitive) 1) ca s :
        terminates (esubst ca e) s ->
      code_terminates (CLam 0 e) ca s
  | TLamS n (e : expr (code primitive) (S (S n))) ca s :
      code_terminates (CLam (S n) e) ca s.

End ReducesTerminates.

Record computational_system : Type := {
  cprimitive :            Type;
  cstate :                Type;
  cstate_nonempty :       cstate;
  cprimitive_reduces :    cprimitive -> code cprimitive -> cstate ->
                            code cprimitive -> cstate -> Prop;
  cprimitive_terminates : cprimitive -> code cprimitive -> cstate -> Prop;
  cpossible_future :      cstate -> cstate -> Prop
                            where "s <= t" := (cpossible_future s t);
  cpreservation cf ca s cr s' : code_reduces cprimitive_reduces cf ca s cr s' -> s <= s';
  cpossible_future_refl s : s <= s;
  cpossible_future_trans s s' s'' : s <= s' -> s' <= s'' -> s <= s''
}.

Arguments cprimitive_reduces    {c}.
Arguments cprimitive_terminates {c}.
Arguments cpossible_future      {c}.

Infix "<=" := cpossible_future (at level 70).

Section Shorthands.

Definition ccode (cs : computational_system) :           Type := code cs.(cprimitive).
Definition cexpr (cs : computational_system) (n : nat) : Type := expr (ccode cs) n.

Context {cs : computational_system}.

Definition creduces : cexpr cs 0 -> cstate cs -> ccode cs -> cstate cs -> Prop :=
  reduces cs.(cprimitive_reduces).
Definition ccode_reduces : ccode cs -> ccode cs -> cstate cs -> ccode cs -> cstate cs -> Prop :=
  code_reduces cs.(cprimitive_reduces).
Definition cterminates : cexpr cs 0 -> cstate cs -> Prop :=
  terminates cs.(cprimitive_reduces) cs.(cprimitive_terminates).
Definition ccode_terminates : ccode cs -> ccode cs -> cstate cs -> Prop :=
  code_terminates cs.(cprimitive_reduces) cs.(cprimitive_terminates).

End Shorthands.

Section Separator.

Record separator (cs : computational_system) : Type := {
  scarrier : ccode cs -> Prop;
  
  sprogress cf ca s :
      scarrier cf ->
      scarrier ca ->
      ccode_terminates cf ca s ->
    exists cr s',
      ccode_reduces cf ca s cr s';

  sclosed_under_reduction cf ca s cr s' :
      scarrier cf ->
      scarrier ca ->
      ccode_reduces cf ca s cr s' ->
    scarrier cr;

  sfunctionally_complete n (e : cexpr cs (S n)) :
      codes_in scarrier e ->
    scarrier (CLam n e)
}.

Arguments scarrier                {cs}.
Arguments sprogress               {cs}.
Arguments sclosed_under_reduction {cs}.
Arguments sfunctionally_complete  {cs}.

Coercion scarrier : separator >-> Funclass.

Context {cs : computational_system}.
Variable sep : separator cs.

Definition codes_in_separator (e : cexpr cs 0) : Prop :=
  codes_in sep.(scarrier) e.

Lemma closed_under_expr_reduction (e : cexpr cs 0) s cr s' :
    codes_in_separator e ->
    creduces e s cr s' ->
  sep cr.
Proof.
  revert s cr s'.
  induction e; intros s cr s' Hcodes_in_sep Hred; inv Hred; inv Hcodes_in_sep.
  - (* e = ECode cr *)
    assumption.
  - (* e = e1 * e2 *)
    eapply sclosed_under_reduction.
    + eapply IHe1; eassumption.
    + eapply IHe2; eassumption.
    + eassumption.
Qed.

Fixpoint expr_progress (e : cexpr cs 0)
                       (s : cstate cs)
                       (Hcodes_in : codes_in_separator e)
                       (Hterm : cterminates e s) :
  exists cr s',
    creduces e s cr s'.
Proof.
  inv Hterm.
  - (* case: TCode *)
    eexists. eexists. constructor.
  - (* case: TApp *)
    inv Hcodes_in.
    apply expr_progress in H; [| assumption]. destruct H as [cf [sf Hredf]].
    specialize (H0 _ _ Hredf). destruct H0 as [Hterma H].
    apply expr_progress in Hterma; [| assumption]. destruct Hterma as [ca [sa Hreda]].
    specialize (H _ _ Hreda).
    eassert (Hsepf := closed_under_expr_reduction _ _ _ _ H3 Hredf).
    eassert (Hsepa := closed_under_expr_reduction _ _ _ _ H4 Hreda).
    eapply sprogress in H; [| eassumption | eassumption]. destruct  H as [cr [sr Hredr]].
    eexists. eexists. econstructor; eassumption.
Qed.

Section TopSeparator.

Variable primitive_progress :
           forall (pf : cprimitive cs) (ca : ccode cs) (s : cstate cs),
               cprimitive_terminates pf ca s ->
             exists cr s',
               cprimitive_reduces pf ca s cr s'.

Lemma progress_of_primitive_progress (cf ca : ccode cs) (s : cstate cs) :
    ccode_terminates cf ca s ->
  exists cr s',
    ccode_reduces cf ca s cr s'

with expr_progress_of_primitive_progress (e : cexpr cs 0) (s : cstate cs) :
    cterminates e s ->
  exists cr s',
    creduces e s cr s'.

Proof.
  - (* progress_of_primitive_progress *)
    intro Hterm. inv Hterm.
    + (* case: TPrimitive *)
      apply primitive_progress in H. destruct H as [cr [s' Hprimred]].
      eexists. eexists. constructor. eassumption.
    + (* case: TLam0 *)
      apply expr_progress_of_primitive_progress in H. destruct H as [cr [s' Hred]].
      eexists. eexists. constructor. eassumption.
    + (* case TLamS *)
      eexists. eexists. econstructor.
  - (* expr_progress_of_primitive_progress *)
    intro Hterm. inv Hterm.
    + (* case: TCode *)
      eexists. eexists. econstructor.
    + (* case: TApp *)
      eapply expr_progress_of_primitive_progress in H. destruct H as [cf [sf Hredf]].
      specialize (H0 _ _ Hredf). destruct H0 as [Hterma H].
      apply expr_progress_of_primitive_progress in Hterma. destruct Hterma as [ca [sa Hreda]].
      specialize (H _ _ Hreda).
      apply progress_of_primitive_progress in H. destruct H as [cr [sr Hredr]].
      eexists. eexists. econstructor; eassumption.
Qed.

Obligation Tactic := intros; apply I || apply progress_of_primitive_progress; assumption.

Program Definition top_separator : separator cs :=
{| scarrier := fun _ => True |}.

End TopSeparator.

End Separator.

Section ChurchRepresentations.

Context {primitive : Type}.

Definition cidentity :     code primitive := CLam 0 (evar 0).

Definition cchurch_true :  code primitive := CLam 1 (evar 0).
Definition cchurch_false : code primitive := CLam 1 (evar 1).

Fixpoint cchurch_nat_aux (n : nat) : expr (code primitive) 2 :=
  match n with
  | 0    => evar 1
  | S n' => evar 0 * cchurch_nat_aux n'
  end.

Definition cchurch_nat (n : nat) : code primitive :=
  CLam 1 (cchurch_nat_aux n).

End ChurchRepresentations.

Definition cdeterministic (cs : computational_system) : Prop :=
  forall (cf ca cr cr' : ccode cs) (s s' s'' : cstate cs),
      ccode_reduces cf ca s cr s' ->
      ccode_reduces cf ca s cr' s'' ->
    cr = cr' /\ s = s'.

(* Tactic used to automatically prove goals of the form
   [codes_in separator exprerrios] or [separator code]  *)
Ltac prove_codes_in := repeat (    eassumption
                                || apply sfunctionally_complete
                                || constructor
                                || eapply sclosed_under_reduction );
                       fail.