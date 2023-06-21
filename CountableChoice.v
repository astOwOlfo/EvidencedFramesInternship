Require Import EF.ComputationalSystem EF.Expressions EF.EvidencedFrames EF.ComputationalSystemToEF.

Require Import ClassicalChoice Logic.Eqdep_dec.

Lemma inj_pair2_nat (P : nat -> Type) (n : nat) (x y : P n) :
  existT P n x = existT P n y -> x = y.
Proof. apply inj_pair2_eq_dec. apply Nat.eq_dec. Qed.

Notation "{ P 'for' x }" := (fun Q => exists x, P = Q).
Notation "{ P 'for' x 'in' A }" := (fun Q => exists x : A, P = Q).

Inductive nonempty (T : Type) : Prop :=
  | Nonempty (x : T).

Section CountableChoice.

Variable E : EvidencedFrame.

Definition total {A B : Type} (relation : A -> B -> PROP E) : PROP E :=
  emeet _ {ejoin _ {relation x y for y in B} for x in A}.

Definition function_subset_relation {A B : Type} (f : A -> B) (rel : A -> B -> PROP E) : PROP E :=
  emeet _ {rel x (f x) for x in A}.

Variable (I : Type).

Definition countable_choice : PROP E :=
  emeet _ { eimp _ (total rel)
                   (ejoin _ {function_subset_relation f rel for f in nat -> I})
            for rel in nat -> I -> PROP E }.

Definition realized (theorem : PROP E) : Prop :=
  exists ecc : Evidence E,
    Evidences _ (etop _) ecc theorem.

End CountableChoice.

Section ComputationalSystem.

Variables (cs : computational_system)
          (sep : separator cs).

Local Notation "'E'" := (computational_system_to_ef cs sep Demonic).

Variable I : Type.

Lemma countable_choice_realized_iff :
      realized _ (countable_choice E I)
  <-> exists cc : Evidence E,
        forall (rel : nat -> I -> PROP E),
          forall (n : nat) (c : ccode cs) (s : cstate cs), ejoin _ {rel n i for i in I} c s ->
            exists i : I,
              reduces_to_predicate cs Demonic (proj1_sig cc) c s (rel n i). (* why does the [cevidence_to_code] coercion not work? *)
Admitted.

Program Definition eunion_PROP_family (pi : PROP E -> Prop) : PROP E :=
{| fcarrier := fun c s => exists p, pi p /\ p c s |}.
Next Obligation. (* ffuture_stable *)
  intros c s s' Hss' [p [Hcarrier Hpcs]].
  exists p. split; [| eapply ffuture_stable]; eassumption.
Qed.

Lemma ejoin_elim (pi : PROP E -> Prop) :
  exists eje : Evidence E,
    Evidences _ (ejoin _ pi) eje (eunion_PROP_family pi).
Proof.
  destruct (emeete E)  as [meete  Hmeete].
  destruct (emeeti E)  as [meeti  Hmeeti].
  destruct (ecut E)    as [cut    Hcut].
  destruct (econji E)  as [conji  Hconji].
  destruct (econje2 E) as [conje2 Hconje2].
  destruct (eimpe E)   as [impe   Himpe].
  destruct (eimpi E)   as [impi   Himpi].
  destruct (eaxiom E)  as [axiom  Haxiom].
  destruct (etopi E)   as [topi   Htopi].
  eexists.
  eapply Hcut. { apply Hmeete. eexists. reflexivity. }
  eapply Hcut. 2: { apply Himpe. }
  apply Hconji. 2: { apply Haxiom. }
  eapply Hcut. { apply Htopi. }
  apply Hmeeti. intros ? [p Hpip]. subst.
  apply Himpi.
  eapply Hcut. { apply Hconje2. }
  unshelve instantiate (1 := exist _ (CLam 0 (evar 0)) _); [prove_codes_in |].
  simpl. intros c s Hpcs. split.
  - constructor. constructor.
  - intros cr s' Hred.
    inv Hred. apply inj_pair2_nat in H. subst.
    inv H0.
    eexists. split; eassumption.
Qed.

End ComputationalSystem.

Section Deterministic.

Variables (cs : computational_system)
          (sep : separator cs)
          (Hdeterministic : cdeterministic cs).

Local Notation "'E'" := (computational_system_to_ef cs sep Demonic).

Variable I : Type.

Lemma deterministic_demonic_countable_choice_realized :
  realized _ (countable_choice E I).
Proof.
  destruct (emeete E)  as [meete  Hmeete].
  destruct (emeeti E)  as [meeti  Hmeeti].
  destruct (ejoine E)  as [joine  Hjoine].
  destruct (ejoini E)  as [joini  Hjoini].
  destruct (ecut E)    as [cut    Hcut].
  destruct (econji E)  as [conji  Hconji].
  destruct (econje2 E) as [conje2 Hconje2].
  destruct (eimpe E)   as [impe   Himpe].
  destruct (eimpi E)   as [impi   Himpi].
  destruct (eaxiom E)  as [axiom  Haxiom].
  destruct (etopi E)   as [topi   Htopi].
  eexists.
  eapply Hmeeti. intros ? [rel ?]. subst.
  apply Himpi.
  eapply Hcut. { apply Hconje2. }
  intros c s Hevidences_tot.
  
  eassert (forall n : nat, reduces_to_predicate cs Demonic _ c s (ejoin _ {rel n i for i in I})).
  { intro n. apply Hjoine. }
  eassert (H := ejoin_elim _ _ _). destruct H as [join_elim Hjoin_elim].
  specialize (Hjoin_elim _ _ Hevidences_tot).



  apply countable_choice_realized_iff.
  eexists. intros rel n c s Hjoincs.
  eassert (H := ejoin_elim _ _ _). destruct H as [join_elim Hjoin_elim].
  specialize (Hjoin_elim _ _ Hjoincs).

End Deterministic.
