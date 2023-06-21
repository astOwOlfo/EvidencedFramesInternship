Require Import EF.ComputationalSystem EF.EvidencedFrames.

From Coq Require Import Program.Tactics.

Section ComputationalSystemToEF.

Variables cs : computational_system.

Record future_stable_predicate : Type := {
  fcarrier :       ccode cs -> cstate cs -> Prop;
  ffuture_stable : forall c s s', s <= s' -> fcarrier c s -> fcarrier c s';
}.

Coercion fcarrier : future_stable_predicate >-> Funclass.

Variable sep : separator cs.

Definition cevidence : Type := { c : ccode cs | sep c }.

Definition cevidence_to_ccode (e : cevidence) : ccode cs := proj1_sig e.
Coercion cevidence_to_ccode : cevidence >-> ccode.

Variant interpretation_of_non_determinism : Set :=
  | Demonic
  | Angelic.

Variable iond : interpretation_of_non_determinism.

Definition reduces_to_predicate (cf ca : ccode cs) (s : cstate cs)
                                (p : ccode cs -> cstate cs -> Prop) : Prop :=
  match iond with
  | Demonic => ccode_terminates cf ca s /\ forall cr s', ccode_reduces cf ca s cr s' -> p cr s'
  | Angelic => exists cr s', ccode_reduces cf ca s cr s' /\ p cr s'
  end.

Program Definition computational_system_to_ef : EvidencedFrame := {|
  PROP := future_stable_predicate;
  Evidence := cevidence;
  Evidences p1 e p2 := forall c s, p1 c s -> reduces_to_predicate e c s p2;
  etop := {| fcarrier := fun _ _ => True |};
  econj p1 p2 := {| fcarrier := fun c s => forall s', s <= s' ->
                                                reduces_to_predicate c cchurch_true  s p1
                                             /\ reduces_to_predicate c cchurch_false s p2 |};
  euniimp p1 pi := {| fcarrier := fun c s => forall p s' c1, pi p -> s <= s' -> p1 c1 s' ->
                                               reduces_to_predicate c c1 s' p |}
|}.
Admit Obligations.

End ComputationalSystemToEF.
