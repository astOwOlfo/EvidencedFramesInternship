Require Import Program.
Obligation Tactic := idtac.

Definition Class : Type := Type.
Definition SET : Class := Type.

(** * Locally Preordered Bicategories *)

Record LocallyPreorderedBicategory : Type := locally_preordered_bicategory {
  Object : Class;
  Morphism : Object -> Object -> Type;
  Refines : forall {o1 o2 : Object}, Morphism o1 o2 -> Morphism o1 o2 -> Prop;
  cid : forall o : Object, Morphism o o;
  ccomp : forall {o1 o2 o3 : Object}, Morphism o1 o2 -> Morphism o2 o3 -> Morphism o1 o3;
  crefl : forall o1 o2 : Object, forall f : Morphism o1 o2, Refines f f;
  ctrans : forall o1 o2 : Object, forall f f' f'' : Morphism o1 o2, Refines f f' -> Refines f' f'' -> Refines f f'';
  crefine : forall o1 o2 o3 : Object, forall f12 f12' : Morphism o1 o2, forall f23 f23' : Morphism o2 o3, Refines f12 f12' -> Refines f23 f23' -> Refines (ccomp f12 f23) (ccomp f12' f23');
  cidl : forall o1 o2 : Object, forall f : Morphism o1 o2, Refines f (ccomp (cid o1) f) /\ Refines (ccomp (cid o1) f) f;
  cidr : forall o1 o2 : Object, forall f : Morphism o1 o2, Refines f (ccomp f (cid o2)) /\ Refines (ccomp f (cid o2)) f;
  cassoc : forall o1 o2 o3 o4 : Object, forall f12 : Morphism o1 o2, forall f23 : Morphism o2 o3, forall f34 : Morphism o3 o4, Refines (ccomp (ccomp f12 f23) f34) (ccomp f12 (ccomp f23 f34)) /\ Refines (ccomp f12 (ccomp f23 f34)) (ccomp (ccomp f12 f23) f34);
}.

Definition Equiv (C : LocallyPreorderedBicategory) {o1 o2 : Object C} (f g : Morphism C o1 o2) : Prop
:= Refines C f g /\ Refines C g f.



(** * Pseudofunctor *)

Record Pseudofunctor {C1 C2 : LocallyPreorderedBicategory} : Type := pseudofunctor {
  MapObject : Object C1 -> Object C2;
  MapMorphism : forall {o1 o1' : Object C1}, Morphism C1 o1 o1' -> Morphism C2 (MapObject o1) (MapObject o1');
  maprefines : forall {o1 o1' : Object C1}, forall f1 f1' : Morphism C1 o1 o1', Refines C1 f1 f1' -> Refines C2 (MapMorphism f1) (MapMorphism f1');
  mapid : forall o1 : Object C1, Equiv C2 (cid C2 (MapObject o1)) (MapMorphism (cid C1 o1));
  mapcomp : forall {o1 o1' o1'' : Object C1}, forall f1 : Morphism C1 o1 o1', forall f1' : Morphism C1 o1' o1'', Equiv C2 (ccomp C2 (MapMorphism f1) (MapMorphism f1')) (MapMorphism (ccomp C1 f1 f1'))
}.
Arguments Pseudofunctor : clear implicits.

Program Definition cat_id (C : LocallyPreorderedBicategory) : Pseudofunctor C C
:= pseudofunctor C C (fun o => o) (fun o o' m => m) _ _ _.
Obligation Tactic := intro C; simpl.
Next Obligation. auto. Qed.
Next Obligation. intro. split; apply crefl. Qed.
Next Obligation. intros. split; apply crefl. Qed.

Program Definition cat_comp {C1 C2 C3 : LocallyPreorderedBicategory} (F : Pseudofunctor C1 C2) (G : Pseudofunctor C2 C3) : Pseudofunctor C1 C3
:= pseudofunctor C1 C3 (fun o1 => MapObject G (MapObject F o1)) (fun o1 o1' m1 => MapMorphism G (MapMorphism F m1)) _ _ _.
Obligation Tactic := intros C1 C2 C3 F G; simpl; intros.
Next Obligation. apply maprefines. apply maprefines. assumption. Qed.
Next Obligation.
 split.
  eapply ctrans; [ apply mapid | ]. apply maprefines. apply mapid.
  eapply ctrans; [ | apply mapid ]. apply maprefines. apply mapid.
Qed.
Next Obligation.
 intros. split.
  eapply ctrans; [ apply mapcomp | ]. apply maprefines. apply mapcomp.
  eapply ctrans; [ | apply mapcomp ]. apply maprefines. apply mapcomp.
Qed.





(** * Pseudonatural Transformations *)

Record PseudonaturalTransformation {C1 C2 : LocallyPreorderedBicategory} {F G : Pseudofunctor C1 C2} : Type
:= pseudonatural_transformation {
  Transform : forall o1 : Object C1, Morphism C2 (MapObject F o1) (MapObject G o1);
  natural : forall {o1 o1' : Object C1}, forall m1 : Morphism C1 o1 o1', Equiv C2 (ccomp C2 (MapMorphism F m1) (Transform o1')) (ccomp C2 (Transform o1) (MapMorphism G m1))
}.
Arguments PseudonaturalTransformation : clear implicits.
Arguments PseudonaturalTransformation {C1 C2}.
Arguments pseudonatural_transformation : clear implicits.
Arguments pseudonatural_transformation {C1 C2}.

Program Definition func_id {C1 C2 : LocallyPreorderedBicategory} (F : Pseudofunctor C1 C2) : PseudonaturalTransformation F F
:= pseudonatural_transformation F F (fun o1 => cid C2 (MapObject F o1)) _.
Obligation Tactic := intros C1 C2 F.
Next Obligation.
 intros. split.
  eapply ctrans; try apply cidr. apply cidl.
  eapply ctrans; try apply cidl. apply cidr.
Qed.

Program Definition func_comp {C1 C2 : LocallyPreorderedBicategory} {F G H : Pseudofunctor C1 C2} (n : PseudonaturalTransformation F G) (n' : PseudonaturalTransformation G H) : PseudonaturalTransformation F H
:= pseudonatural_transformation F H (fun o1 => ccomp C2 (Transform n o1) (Transform n' o1)) _.
Obligation Tactic := intros C1 C2 F G H n n'.
Next Obligation.
 intros. split.
  eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply crefine; [ apply natural | apply crefl ] | ]. eapply ctrans; [ apply cassoc | ]. apply crefine; [ apply crefl | ]. apply natural.
  eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply crefine; [ apply crefl | apply natural ] | ]. eapply ctrans; [ apply cassoc | ]. apply crefine; [ | apply crefl ]. apply natural.
Qed.

Definition PseudonaturalTransformationEquiv {C1 C2 : LocallyPreorderedBicategory} {F G : Pseudofunctor C1 C2} (n n' : PseudonaturalTransformation F G) : Prop
:= forall o1 : Object C1, Equiv C2 (Transform n o1) (Transform n' o1).


(** * Biadjoint Biequivalence *)

Record BiadjointBiequivalence {C1 C2 : LocallyPreorderedBicategory} : Type := biadjoint_biequivalence {
 to : Pseudofunctor C1 C2;
 from : Pseudofunctor C2 C1;
 dom_unit : PseudonaturalTransformation (cat_id C1) (cat_comp to from);
 dom_counit : PseudonaturalTransformation (cat_comp to from) (cat_id C1);
 cod_unit : PseudonaturalTransformation (cat_id C2) (cat_comp from to);
 cod_counit : PseudonaturalTransformation (cat_comp from to) (cat_id C2);
 dom_unit_counit : PseudonaturalTransformationEquiv (func_comp dom_unit dom_counit) (func_id (cat_id C1));
 dom_counit_unit : PseudonaturalTransformationEquiv (func_comp dom_counit dom_unit) (func_id (cat_comp to from));
 cod_unit_counit : PseudonaturalTransformationEquiv (func_comp cod_unit cod_counit) (func_id (cat_id C2));
 cod_counit_unit : PseudonaturalTransformationEquiv (func_comp cod_counit cod_unit) (func_id (cat_comp from to));
 unit_counit_adj : (* any one of the following implies the rest, given the above structure *)
                   (forall o1 : Object C1, Equiv C2 (ccomp C2 (MapMorphism to (Transform dom_unit o1)) (Transform cod_counit (MapObject to o1))) (cid C2 (MapObject to o1)))
                /\ (forall o1 : Object C1, Equiv C2 (ccomp C2 (Transform cod_unit (MapObject to o1)) (MapMorphism to (Transform dom_counit o1))) (cid C2 (MapObject to o1)))
                /\ (forall o2 : Object C2, Equiv C1 (ccomp C1 (MapMorphism from (Transform cod_unit o2)) (Transform dom_counit (MapObject from o2))) (cid C1 (MapObject from o2)))
                /\ (forall o2 : Object C2, Equiv C1 (ccomp C1 (Transform dom_unit (MapObject from o2)) (MapMorphism from (Transform cod_counit o2))) (cid C1 (MapObject from o2)))
}.
Arguments BiadjointBiequivalence : clear implicits.

Obligation Tactic := intros C1 C2 C3 E E'; unfold PseudonaturalTransformationEquiv; simpl.
Program Definition equivalence_comp {C1 C2 C3 : LocallyPreorderedBicategory} (E : BiadjointBiequivalence C1 C2) (E' : BiadjointBiequivalence C2 C3) : BiadjointBiequivalence C1 C3
:= biadjoint_biequivalence C1 C3
                           (cat_comp (to E) (to E'))
                           (cat_comp (from E') (from E))
                           (pseudonatural_transformation _ _ (fun o1 => ccomp C1 (Transform (dom_unit E) o1) (MapMorphism (from E) (Transform (dom_unit E') (MapObject (to E) o1)))) _)
                           (pseudonatural_transformation _ _ (fun o1 => ccomp C1 (MapMorphism (from E) (Transform (dom_counit E') (MapObject (to E) o1))) (Transform (dom_counit E) o1)) _)
                           (pseudonatural_transformation _ _ (fun o3 => ccomp C3 (Transform (cod_unit E') o3) (MapMorphism (to E') (Transform (cod_unit E) (MapObject (from E') o3)))) _)
                           (pseudonatural_transformation _ _ (fun o3 => ccomp C3 (MapMorphism (to E') (Transform (cod_counit E) (MapObject (from E') o3))) (Transform (cod_counit E') o3)) _)
                           _ _ _ _ _.
Next Obligation.
 intros. split.
  eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ apply crefine; [ apply (natural (dom_unit E)) | apply crefl ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply (natural (dom_unit E')) | ]. simpl. apply crefine; apply crefl.
  eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ | apply crefine; [ apply (natural (dom_unit E)) | apply crefl ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply (natural (dom_unit E')) ]. simpl. apply crefine; apply crefl.
Qed.
Next Obligation.
 intros. split.
  eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ | apply crefine; [ apply crefl | apply (natural (dom_counit E)) ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply (natural (dom_counit E')) ]. simpl. apply crefine; apply crefl.
  eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ apply crefine; [ apply crefl | apply (natural (dom_counit E)) ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply (natural (dom_counit E')) | ]. simpl. apply crefine; apply crefl.
Qed.
Next Obligation.
 intros. split.
  eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ apply crefine; [ apply (natural (cod_unit E')) | apply crefl ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply (natural (cod_unit E)) | ]. simpl. apply crefine; apply crefl.
  eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ | apply crefine; [ apply (natural (cod_unit E')) | apply crefl ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply (natural (cod_unit E)) ]. simpl. apply crefine; apply crefl.
Qed.
Next Obligation.
 intros. split.
  eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ | apply crefine; [ apply crefl | apply (natural (cod_counit E')) ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply (natural (cod_counit E)) ]. simpl. apply crefine; apply crefl.
  eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ apply crefine; [ apply crefl | apply (natural (cod_counit E')) ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply (natural (cod_counit E)) | ]. simpl. apply crefine; apply crefl.
Qed.
Next Obligation.
 intros o1. split.
  eapply ctrans; [ | eapply (dom_unit_counit E) ]. simpl. eapply ctrans; [ apply (cassoc C1 _ _ _ _ (Transform (dom_unit E) o1)) | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply cidl ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply maprefines; apply (dom_unit_counit E') ]. simpl. apply mapcomp.
  eapply ctrans; [ eapply (dom_unit_counit E) | ]. simpl. eapply ctrans; [ | apply (cassoc C1 _ _ _ _ (Transform (dom_unit E) o1)) ]. apply crefine; try apply crefl. eapply ctrans; [ apply cidl | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply maprefines; apply (dom_unit_counit E') | ]. apply mapcomp.
Qed.
Next Obligation.
 intros o1. split.
  eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply maprefines; apply (dom_counit_unit E') ]. simpl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply (cassoc C1 _ _ _ _ (MapMorphism (from E) (Transform (dom_counit E') (MapObject (to E) o1)))) | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply cidl ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. apply dom_counit_unit.
  eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply maprefines; eapply (dom_counit_unit E') | ]. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply (cassoc C1 _ _ _ _ (MapMorphism (from E) (Transform (dom_counit E') (MapObject (to E) o1)))) ]. apply crefine; try apply crefl. eapply ctrans; [ apply cidl | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. apply dom_counit_unit.
Qed.
Next Obligation.
 intros o3. split.
  eapply ctrans; [ | eapply (cod_unit_counit E') ]. simpl. eapply ctrans; [ apply (cassoc C3 _ _ _ _ (Transform (cod_unit E') o3)) | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply cidl ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply maprefines; apply (cod_unit_counit E) ]. simpl. apply mapcomp.
  eapply ctrans; [ eapply (cod_unit_counit E') | ]. simpl. eapply ctrans; [ | apply (cassoc C3 _ _ _ _ (Transform (cod_unit E') o3)) ]. apply crefine; try apply crefl. eapply ctrans; [ apply cidl | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply maprefines; apply (cod_unit_counit E) | ]. apply mapcomp.
Qed.
Next Obligation.
 intros o3. split.
  eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply maprefines; apply (cod_counit_unit E) ]. simpl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply (cassoc C3 _ _ _ _ (MapMorphism (to E') (Transform (cod_counit E) (MapObject (from E') o3)))) | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply cidl ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. apply cod_counit_unit.
  eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply maprefines; eapply (cod_counit_unit E) | ]. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply (cassoc C3 _ _ _ _ (MapMorphism (to E') (Transform (cod_counit E) (MapObject (from E') o3)))) ]. apply crefine; try apply crefl. eapply ctrans; [ apply cidl | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. apply cod_counit_unit.
Qed.
Next Obligation.
 repeat apply conj; intro; split.
  eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply cidr ]. eapply ctrans; [ | apply crefine; [ apply maprefines; apply (let (p, _) := unit_counit_adj E in p) | apply (let (p, _) := unit_counit_adj E' in p) ] ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply crefine; [ apply mapcomp | apply crefl ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. apply (natural (cod_counit E)).
  eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply cidr | ]. eapply ctrans; [ apply crefine; [ apply maprefines; apply (let (p, _) := unit_counit_adj E in p) | apply (let (p, _) := unit_counit_adj E' in p) ] | ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply crefine; [ apply mapcomp | apply crefl ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. apply (natural (cod_counit E)).
  eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply cidl ]. eapply ctrans; [ | apply crefine; [ apply (let (_, p) := unit_counit_adj E' in let (p, _) := p in p) | apply maprefines; apply (let (_, p) := unit_counit_adj E in let (p, _) := p in p) ] ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply crefine; [ apply crefl | apply mapcomp ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. apply (natural (cod_unit E)).
  eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply cidl | ]. eapply ctrans; [ apply crefine; [ apply (let (_, p) := unit_counit_adj E' in let (p, _) := p in p) | apply maprefines; apply (let (_, p) := unit_counit_adj E in let (p, _) := p in p) ] | ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply mapcomp ]. simpl. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply crefine; [ apply crefl | apply mapcomp ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. apply (natural (cod_unit E)).
  eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply cidr ]. eapply ctrans; [ | apply crefine; [ apply maprefines; apply (let (_, p) := unit_counit_adj E' in let (_, p) := p in let (p, _) := p in p) | apply (let (_, p) := unit_counit_adj E in let (_, p) := p in let (p, _) := p in p) ] ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply crefine; [ apply mapcomp | apply crefl ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. apply (natural (dom_counit E')).
  eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply cidr | ]. eapply ctrans; [ apply crefine; [ apply maprefines; apply (let (_, p) := unit_counit_adj E' in let (_, p) := p in let (p, _) := p in p) | apply (let (_, p) := unit_counit_adj E in let (_, p) := p in let (p, _) := p in p) ] | ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply mapcomp ]. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply crefine; [ apply mapcomp | apply crefl ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. apply (natural (dom_counit E')).
  eapply ctrans; [ | apply mapid ]. eapply ctrans; [ | apply cidl ]. eapply ctrans; [ | apply crefine; [ apply (let (_, p) := unit_counit_adj E in let (_, p) := p in let (_, p) := p in p) | apply maprefines; apply (let (_, p) := unit_counit_adj E' in let (_, p) := p in let (_, p) := p in p) ] ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. simpl. eapply ctrans; [ apply mapcomp | ]. eapply ctrans; [ | apply mapcomp ]. apply maprefines. eapply ctrans; [ apply crefine; [ apply crefl | apply mapcomp ] | ]. eapply ctrans; [ apply cassoc | ]. eapply ctrans; [ | apply cassoc ]. apply crefine; try apply crefl. apply (natural (dom_unit E')).
  eapply ctrans; [ apply mapid | ]. eapply ctrans; [ apply cidl | ]. eapply ctrans; [ apply crefine; [ apply (let (_, p) := unit_counit_adj E in let (_, p) := p in let (_, p) := p in p) | apply maprefines; apply (let (_, p) := unit_counit_adj E' in let (_, p) := p in let (_, p) := p in p) ] | ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. eapply ctrans; [ | apply mapcomp ]. simpl. eapply ctrans; [ apply mapcomp | ]. apply maprefines. eapply ctrans; [ | apply crefine; [ apply crefl | apply mapcomp ] ]. eapply ctrans; [ | apply cassoc ]. eapply ctrans; [ apply cassoc | ]. apply crefine; try apply crefl. apply (natural (dom_unit E')).
Qed.



