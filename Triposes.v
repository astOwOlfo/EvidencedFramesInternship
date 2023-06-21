Require Import Program.
Require Import EF.Categories.
Obligation Tactic := idtac.


(** * Pre-Heyting Algebras *)

(** ** Definition *)

Record PreHeytingAlgebra : Type := preheyting_algebra {
  Carrier : SET;
  LEq : Carrier -> Carrier -> Prop;
  htop : Carrier;
  hconj : Carrier -> Carrier -> Carrier;
  hbot : Carrier;
  hdisj : Carrier -> Carrier -> Carrier;
  himp : Carrier -> Carrier -> Carrier;
  hrefl : forall x : Carrier, LEq x x;
  htrans : forall x y z : Carrier, LEq x y -> LEq y z -> LEq x z;
  htopi : forall x : Carrier, LEq x htop;
  hconji : forall x y1 y2 : Carrier, LEq x y1 -> LEq x y2 -> LEq x (hconj y1 y2);
  hconjp1 : forall x1 x2 : Carrier, LEq (hconj x1 x2) x1;
  hconjp2 : forall x1 x2 : Carrier, LEq (hconj x1 x2) x2;
  hbote : forall x : Carrier, LEq hbot x;
  hdisjp1 : forall x1 x2 : Carrier, LEq x1 (hdisj x1 x2);
  hdisjp2 : forall x1 x2 : Carrier, LEq x2 (hdisj x1 x2);
  hdisje : forall x1 x2 y : Carrier, LEq x1 y -> LEq x2 y -> LEq (hdisj x1 x2) y;
  himpir : forall x1 x2 y : Carrier, LEq (hconj x1 x2) y -> LEq x1 (himp x2 y);
  himppr : forall x y : Carrier, LEq (hconj x (himp x y)) y;
}.

Lemma htrans' (H : PreHeytingAlgebra) (x y z : Carrier H) : LEq H y z -> LEq H x y -> LEq H x z.
 intros. eapply htrans; eassumption.
Qed.
Lemma hconje1 (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H x1 y -> LEq H (hconj H x1 x2) y.
 intro. apply htrans with x1; try assumption. apply hconjp1.
Qed.
Lemma hconje2 (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H x2 y -> LEq H (hconj H x1 x2) y.
 intro. apply htrans with x2; try assumption. apply hconjp2.
Qed.
Lemma hconjm (H : PreHeytingAlgebra) (x1 y1 x2 y2 : Carrier H) : LEq H x1 y1 -> LEq H x2 y2 -> LEq H (hconj H x1 x2) (hconj H y1 y2).
 intros. apply hconji; [ apply hconje1 | apply hconje2 ]; assumption.
Qed.
Lemma hconjm1 (H : PreHeytingAlgebra) (x y z : Carrier H) : LEq H x y -> LEq H (hconj H x z) (hconj H y z).
 intro. apply hconjm; try assumption. apply hrefl.
Qed.
Lemma hconjm2 (H : PreHeytingAlgebra) (x y z : Carrier H) : LEq H x y -> LEq H (hconj H z x) (hconj H z y).
 intro. apply hconjm; try assumption. apply hrefl.
Qed.
Lemma hconjsym (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H (hconj H x1 x2) y -> LEq H (hconj H x2 x1) y.
 intro. apply htrans with (hconj H x1 x2); try assumption. apply hconji; [ apply hconjp2 | apply hconjp1 ].
Qed.
Lemma hconjassoc (H : PreHeytingAlgebra) (x1 x2 x3 y : Carrier H) : LEq H (hconj H x1 (hconj H x2 x3)) y -> LEq H (hconj H (hconj H x1 x2) x3) y.
 intro. eapply htrans; try eassumption. apply hconji.
  apply hconje1. apply hconjp1.
  apply hconji.
   apply hconje1. apply hconjp2.
   apply hconjp2.
Qed.
Lemma hdisji1 (H : PreHeytingAlgebra) (x y1 y2 : Carrier H) : LEq H x y1 -> LEq H x (hdisj H y1 y2).
 intro. apply htrans with y1; try assumption. apply hdisjp1.
Qed.
Lemma hdisji2 (H : PreHeytingAlgebra) (x y1 y2 : Carrier H) : LEq H x y2 -> LEq H x (hdisj H y1 y2).
 intro. apply htrans with y2; try assumption. apply hdisjp2.
Qed.
Lemma himpr (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H x1 (himp H x2 y) -> LEq H (hconj H x1 x2) y.
 intro. apply htrans with (hconj H x2 (himp H x2 y)); try apply himppr. apply hconjsym. apply hconjm2. assumption.
Qed.
Lemma himpil (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H (hconj H x1 x2) y -> LEq H x2 (himp H x1 y).
 intro. apply himpir. apply hconjsym. assumption.
Qed.
Lemma himpl (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H x2 (himp H x1 y) -> LEq H (hconj H x1 x2) y.
 intro. apply himpr. apply himpil. apply himpr. assumption.
Qed.
Lemma himpm (H : PreHeytingAlgebra) (x1 y1 x2 y2 : Carrier H) : LEq H y1 x1 -> LEq H x2 y2 -> LEq H (himp H x1 x2) (himp H y1 y2).
 intros. apply himpil. apply htrans with (hconj H x1 (himp H x1 x2)).
  apply hconjm1. assumption.
  apply htrans with x2; try assumption. apply himppr.
Qed.
Lemma himpm1 (H : PreHeytingAlgebra) (x y z : Carrier H) : LEq H y x -> LEq H (himp H x z) (himp H y z).
 intro. apply himpm; try assumption. apply hrefl.
Qed.
Lemma himpm2 (H : PreHeytingAlgebra) (x y z : Carrier H) : LEq H x y -> LEq H (himp H z x) (himp H z y).
 intro. apply himpm; try assumption. apply hrefl.
Qed.
Lemma himpapp (H : PreHeytingAlgebra) (x1 x2 y : Carrier H) : LEq H (htop H) x1 -> LEq H x2 y -> LEq H (himp H x1 x2) y.
 intros. eapply htrans; [ | apply himppr ]. apply hconji; [ apply hrefl | ]. apply himpm; try assumption. eapply htrans; [ apply htopi | ]. assumption.
Qed.

(** ** Morphisms *)

Record PHAMorphism {H1 H2 : PreHeytingAlgebra} : Type := pha_morphism {
  carrier : Carrier H1 -> Carrier H2;
  hmleq : forall x y : Carrier H1, LEq H1 x y -> LEq H2 (carrier x) (carrier y);
  hmtop : LEq H2 (htop H2) (carrier (htop H1));
  hmconj : forall x1 x2 : Carrier H1, LEq H2 (hconj H2 (carrier x1) (carrier x2)) (carrier (hconj H1 x1 x2));
  hmbot : LEq H2 (carrier (hbot H1)) (hbot H2);
  hmdisj : forall x1 x2 : Carrier H1, LEq H2 (carrier (hdisj H1 x1 x2)) (hdisj H2 (carrier x1) (carrier x2));
  hmimp : forall x1 x2 : Carrier H1, LEq H2 (himp H2 (carrier x1) (carrier x2)) (carrier (himp H1 x1 x2))
}.
Arguments PHAMorphism : clear implicits.

Lemma hmtopi {H1 H2 : PreHeytingAlgebra} (f : PHAMorphism H1 H2) (y : Carrier H2) : LEq H2 (carrier f (htop H1)) y <-> LEq H2 (htop H2) y.
 split.
  intro. eapply htrans; [ apply (hmtop f) | ]. assumption.
  intro. eapply htrans; [ | eassumption ]. apply htopi.
Qed.
Lemma hmtope {H1 H2 : PreHeytingAlgebra} (f : PHAMorphism H1 H2) (x : Carrier H2) : LEq H2 x (htop H2) -> LEq H2 x (carrier f (htop H1)).
 intro. eapply htrans; [ | apply (hmtop f) ]. assumption.
Qed.
Lemma hmconji (H1 H2 : PreHeytingAlgebra) (f : PHAMorphism H1 H2) (x : Carrier H2) (y1 y2 : Carrier H1) : LEq H2 (carrier f (hconj H1 y1 y2)) x <-> LEq H2 (hconj H2 (carrier f y1) (carrier f y2)) x.
 split.
  intro. eapply htrans; [ apply hmconj | ]. assumption.
  intro. eapply htrans; try eassumption. apply hconji.
   apply hmleq. apply hconjp1.
   apply hmleq. apply hconjp2.
Qed.
Lemma hmconje (H1 H2 : PreHeytingAlgebra) (f : PHAMorphism H1 H2) (x : Carrier H2) (y1 y2 : Carrier H1) : LEq H2 x (hconj H2 (carrier f y1) (carrier f y2)) -> LEq H2 x (carrier f (hconj H1 y1 y2)).
 intro. eapply htrans; [ | apply hmconj ]. assumption.
Qed.
Lemma hmboti {H1 H2 : PreHeytingAlgebra} (f : PHAMorphism H1 H2) (y : Carrier H2) : LEq H2 (hbot H2) y -> LEq H2 (carrier f (hbot H1)) y.
 intro. eapply htrans; [ apply (hmbot f) | ]. assumption.
Qed.
Lemma hmdisji (H1 H2 : PreHeytingAlgebra) (f : PHAMorphism H1 H2) (x1 x2 : Carrier H1) (y : Carrier H2) : LEq H2 (hdisj H2 (carrier f x1) (carrier f x2)) y <-> LEq H2 (carrier f (hdisj H1 x1 x2)) y.
 split.
  intro. eapply htrans; [ apply hmdisj | ]. assumption.
  intro. eapply htrans; try eassumption. apply hdisje; apply hmleq; [ apply hdisjp1 | apply hdisjp2 ].
Qed.
Lemma hmdisje (H1 H2 : PreHeytingAlgebra) (f : PHAMorphism H1 H2) (x : Carrier H2) (y1 y2 : Carrier H1) : LEq H2 x (hdisj H2 (carrier f y1) (carrier f y2)) <-> LEq H2 x (carrier f (hdisj H1 y1 y2)).
 split.
  intro. eapply htrans; try eassumption. apply hdisje; apply hmleq; [ apply hdisjp1 | apply hdisjp2 ].
  intro. eapply htrans; [ | apply hmdisj ]. assumption.
Qed.
Lemma hmimpi (H1 H2 : PreHeytingAlgebra) (f : PHAMorphism H1 H2) (x : Carrier H2) (y1 y2 : Carrier H1) : LEq H2 (himp H2 (carrier f y1) (carrier f y2)) x -> LEq H2 (carrier f (himp H1 y1 y2)) x.
 intro. eapply htrans; try eassumption. apply himpil. apply hmconji. apply hmleq. apply himppr.
Qed.
Lemma hmimpe (H1 H2 : PreHeytingAlgebra) (f : PHAMorphism H1 H2) (x : Carrier H2) (y1 y2 : Carrier H1) : LEq H2 x (himp H2 (carrier f y1) (carrier f y2)) <-> LEq H2 x (carrier f (himp H1 y1 y2)).
 split.
  intro. eapply htrans; [ | apply hmimp ]. assumption.
  intro. apply himpir. eapply htrans; [ apply hconjm1; eassumption | ]. apply hmconji. apply hmleq. apply hconjsym. apply himppr.
Qed.

Definition hmid (H : PreHeytingAlgebra) : PHAMorphism H H.
refine (pha_morphism H H (fun x => x) _ _ _ _ _ _).
 trivial.
 apply hrefl.
 intros. apply hrefl.
 apply hrefl.
 intros. apply hrefl.
 intros. apply hrefl.
Defined.

Definition hmcomp {H1 H2 H3 : PreHeytingAlgebra} (f : PHAMorphism H1 H2) (g : PHAMorphism H2 H3) : PHAMorphism H1 H3.
refine (pha_morphism H1 H3 (fun x => carrier g (carrier f x)) _ _ _ _ _ _).
 intros. apply hmleq. apply hmleq. assumption.
 eapply htrans; [ apply (hmtop g) | ]. apply hmleq. apply hmtop.
 intros. eapply htrans; [ apply (hmconj g) | ]. apply hmleq. apply hmconj.
 eapply htrans; [ | apply (hmbot g) ]. apply hmleq. apply hmbot.
 intros. eapply htrans; [ | apply (hmdisj g) ]. apply hmleq. apply hmdisj.
 intros. eapply htrans; [ apply (hmimp g) | ]. apply hmleq. apply hmimp.
Defined.

Definition PHARefines {H1 H2 : PreHeytingAlgebra} (f g : PHAMorphism H1 H2) : Prop
:= forall x : Carrier H1, LEq H2 (carrier f x) (carrier g x).
Definition PHAEquiv {H1 H2 : PreHeytingAlgebra} (f g : PHAMorphism H1 H2) : Prop
:= forall x : Carrier H1, LEq H2 (carrier f x) (carrier g x) /\ LEq H2 (carrier g x) (carrier f x).




(** * Reflection-Based Triposes *)

(** The equivalence with Set-Based Triposes is given far below *)

(** ** Definition *)

Record Tripos : Class := tripos {
  Pred : SET -> PreHeytingAlgebra;
  subst : forall {A B : SET}, (A -> B) -> PHAMorphism (Pred B) (Pred A);
  tforall : forall A B : SET, Carrier (Pred (prod A B)) -> Carrier (Pred A);
  texists : forall A B : SET, Carrier (Pred (prod A B)) -> Carrier (Pred A);
  treflect : forall A : SET, (A -> Prop) -> Carrier (Pred A);
  Omega : SET;
  holds : Carrier (Pred Omega);
  chi : forall {A : SET}, Carrier (Pred A) -> A -> Omega;
  tid : forall A : SET, PHARefines (hmid (Pred A)) (subst (fun a => a)) /\ PHARefines (subst (fun a => a)) (hmid (Pred A));
  tcomp : forall {A B C : SET}, forall f : A -> B, forall g : B -> C, PHARefines (hmcomp (subst g) (subst f)) (subst (fun a => g (f a))) /\ PHARefines (subst (fun a => g (f a))) (hmcomp (subst g) (subst f));
  tforallsubst : forall A1 A2 B : SET, forall f : A1 -> A2, forall pab : Carrier (Pred (prod A2 B)), LEq (Pred A1) (tforall A1 B (carrier (subst (fun ab => pair (f (fst ab)) (snd ab))) pab)) (carrier (subst f) (tforall A2 B pab));
  tforalladj : forall A B : SET, forall pa : Carrier (Pred A), forall pab : Carrier (Pred (prod A B)), LEq (Pred (prod A B)) (carrier (subst fst) pa) pab <-> LEq (Pred A) pa (tforall A B pab);
  texistssubst : forall A1 A2 B : SET, forall f : A1 -> A2, forall pab : Carrier (Pred (prod A2 B)), LEq (Pred A1) (carrier (subst f) (texists A2 B pab)) (texists A1 B (carrier (subst (fun ab => pair (f (fst ab)) (snd ab))) pab));
  texistsadj : forall A B : SET, forall pa : Carrier (Pred A), forall pab : Carrier (Pred (prod A B)), LEq (Pred (prod A B)) pab (carrier (subst fst) pa) <-> LEq (Pred A) (texists A B pab) pa;
  treflectleq (A : SET) (sa sa' : A -> Prop) : (forall a : A, sa a -> sa' a) -> LEq (Pred A) (treflect A sa) (treflect A sa');
  treflectsubst {A B : SET} (f : A -> B) (sb : B -> Prop) : LEq (Pred A) (treflect A (fun a => sb (f a))) (carrier (subst f) (treflect B sb)) /\ LEq (Pred A) (carrier (subst f) (treflect B sb)) (treflect A (fun a => sb (f a)));
  treflectopcart : forall A : SET, forall {B : SET}, forall sa : A -> Prop, forall f : A -> B, forall sb : B -> Prop, forall pb : Carrier (Pred B), (forall b : B, sb b -> exists2 a : A, f a = b & sa a) -> LEq (Pred A) (treflect A sa) (carrier (subst f) pb) -> LEq (Pred B) (treflect B sb) pb;
  treflecttop : forall A : SET, LEq (Pred A) (htop (Pred A)) (treflect A (fun _ => True));
  treflectconj : forall A : SET, forall sa1 sa2 : A -> Prop, LEq (Pred A) (hconj (Pred A) (treflect A sa1) (treflect A sa2)) (treflect A (fun a => sa1 a /\ sa2 a));
  tholds : forall A : SET, forall p : Carrier (Pred A), LEq (Pred A) p (carrier (subst (chi p)) holds) /\ LEq (Pred A) (carrier (subst (chi p)) holds) p
}.
(* TODO: prove reflect provides equality *)

Lemma tidi (T : Tripos) (A : SET) (pa pa' : Carrier (Pred T A)) : LEq (Pred T A) pa pa' -> LEq (Pred T A) (carrier (subst T (fun a => a)) pa) pa'.
 intro. eapply htrans; [ apply tid | ]. assumption.
Qed.
Lemma tidi' (T : Tripos) (A : SET) (pa pa' : Carrier (Pred T A)) : LEq (Pred T A) (carrier (subst T (fun a => a)) pa) pa' -> LEq (Pred T A) pa pa'.
 intro. eapply htrans; [ apply tid | ]. assumption.
Qed.
Lemma tide (T : Tripos) (A : SET) (pa pa' : Carrier (Pred T A)) : LEq (Pred T A) pa pa' -> LEq (Pred T A) pa (carrier (subst T (fun a => a)) pa').
 destruct (tid T A) as [ tid _ ]. intro. eapply htrans; [ | apply tid ]. assumption.
Qed.
Lemma tide' (T : Tripos) (A : SET) (pa pa' : Carrier (Pred T A)) : LEq (Pred T A) pa (carrier (subst T (fun a => a)) pa') -> LEq (Pred T A) pa pa'.
 destruct (tid T A) as [ _ tid ]. intro. eapply htrans; [ | apply tid ]. assumption.
Qed.
Lemma tcompi {T : Tripos} {A B C : SET} (f : A -> B) (g : B -> C) (pc : Carrier (Pred T C)) (pa : Carrier (Pred T A)) : LEq (Pred T A) (carrier (subst T f) (carrier (subst T g) pc)) pa <-> LEq (Pred T A) (carrier (subst T (fun a => g (f a))) pc) pa.
 split; intro; (eapply htrans; [ apply (tcomp T f g) | ]; assumption).
Qed.
Lemma tcompe {T : Tripos} {A B C : SET} (f : A -> B) (g : B -> C) (pa : Carrier (Pred T A)) (pc : Carrier (Pred T C)) : LEq (Pred T A) pa (carrier (subst T f) (carrier (subst T g) pc)) <-> LEq (Pred T A) pa (carrier (subst T (fun a => g (f a))) pc).
 split; intro; (eapply htrans; [ | apply (tcomp T f g) ]; assumption).
Qed.
Lemma tforallsubsti (T : Tripos) (A1 A2 B : SET) (f : A1 -> A2) (pa1 : Carrier (Pred T A1)) (pa2b : Carrier (Pred T (prod A2 B))) : LEq (Pred T A1) (tforall T A1 B (carrier (subst T (fun (p : prod A1 B) => pair (f (fst p)) (snd p))) pa2b)) pa1 -> LEq (Pred T A1) (carrier (subst T f) (tforall T A2 B pa2b)) pa1.
 intro. eapply htrans; try eassumption. apply tforalladj. apply tcompi. apply (tcompi (fun p => pair (f (fst p)) (snd p)) fst). apply hmleq. apply tforalladj. apply hrefl.
Qed.
Lemma tforallsubste (T : Tripos) (A1 A2 B : SET) (f : A1 -> A2) (pa1 : Carrier (Pred T A1)) (pa2b : Carrier (Pred T (prod A2 B))) : LEq (Pred T A1) pa1 (tforall T A1 B (carrier (subst T (fun (p : prod A1 B) => pair (f (fst p)) (snd p))) pa2b)) -> LEq (Pred T A1) pa1 (carrier (subst T f) (tforall T A2 B pa2b)).
 intro. eapply htrans; [ | apply tforallsubst ]. assumption.
Qed.
Lemma tforallproji {T : Tripos} {A B : SET} (f : A -> B) (pab : Carrier (Pred T (prod A B))) (pa : Carrier (Pred T A)) : LEq (Pred T A) (carrier (subst T (fun a => pair a (f a))) pab) pa -> LEq (Pred T A) (tforall T A B pab) pa.
 intro. eapply htrans; try eassumption. apply tidi'. apply (tcompi (fun a => pair a (f a)) fst). apply hmleq. apply tforalladj. apply hrefl.
Qed.
Lemma tforallm (T : Tripos) (A B : SET) (pab pab' : Carrier (Pred T (prod A B))) : LEq (Pred T (prod A B)) pab pab' -> LEq (Pred T A) (tforall T A B pab) (tforall T A B pab').
 intro. apply tforalladj. eapply htrans; [ | eassumption ]. apply tforalladj. apply hrefl.
Qed.
Lemma texistssubsti (T : Tripos) (A1 A2 B : SET) (f : A1 -> A2) (pa1 : Carrier (Pred T A1)) (pa2b : Carrier (Pred T (prod A2 B))) : LEq (Pred T A1) (texists T A1 B (carrier (subst T (fun (p : prod A1 B) => pair (f (fst p)) (snd p))) pa2b)) pa1 -> LEq (Pred T A1) (carrier (subst T f) (texists T A2 B pa2b)) pa1.
 intro. eapply htrans; [ apply texistssubst | ]. assumption.
Qed.
Lemma texistssubste (T : Tripos) (A1 A2 B : SET) (f : A1 -> A2) (pa1 : Carrier (Pred T A1)) (pa2b : Carrier (Pred T (prod A2 B))) : LEq (Pred T A1) pa1 (texists T A1 B (carrier (subst T (fun (p : prod A1 B) => pair (f (fst p)) (snd p))) pa2b)) -> LEq (Pred T A1) pa1 (carrier (subst T f) (texists T A2 B pa2b)).
 intro. eapply htrans; try eassumption. apply texistsadj. apply tcompe. apply (tcompe (fun p => pair (f (fst p)) (snd p)) fst). apply hmleq. apply texistsadj. apply hrefl.
Qed.
Lemma texistsproje {T : Tripos} {A B : SET} (f : A -> B) (pab : Carrier (Pred T (prod A B))) (pa : Carrier (Pred T A)) : LEq (Pred T A) pa (carrier (subst T (fun a => pair a (f a))) pab) -> LEq (Pred T A) pa (texists T A B pab).
 intro. eapply htrans; try eassumption. apply tide'. apply (tcompe (fun a => pair a (f a)) fst). apply hmleq. apply texistsadj. apply hrefl.
Qed.
Lemma texistsm (T : Tripos) (A B : SET) (pab pab' : Carrier (Pred T (prod A B))) : LEq (Pred T (prod A B)) pab pab' -> LEq (Pred T A) (texists T A B pab) (texists T A B pab').
 intro. apply texistsadj. eapply htrans; [ eassumption | ]. apply texistsadj. apply hrefl.
Qed.
Lemma treflectsubsti {T : Tripos} {A B : SET} (f : A -> B) (pa : Carrier (Pred T A)) (pb : B -> Prop) : LEq (Pred T A) (treflect T A (fun a => pb (f a))) pa <-> LEq (Pred T A) (carrier (subst T f) (treflect T B pb)) pa.
 split; intro; (eapply htrans; [ apply treflectsubst | ]; assumption).
Qed.
Lemma treflectsubste {T : Tripos} {A B : SET} (f : A -> B) (pa : Carrier (Pred T A)) (pb : B -> Prop) : LEq (Pred T A) pa (treflect T A (fun a => pb (f a))) <-> LEq (Pred T A) pa (carrier (subst T f) (treflect T B pb)).
 split; intro; (eapply htrans; [ | apply treflectsubst ]; assumption).
Qed.
Lemma treflecttopi (T : Tripos) (A : SET) (pa : Carrier (Pred T A)) : LEq (Pred T A) (treflect T A (fun a => True)) pa -> LEq (Pred T A) (htop (Pred T A)) pa.
 intro. eapply htrans; [ apply treflecttop | ]. assumption.
Qed.
Lemma treflectconji (T : Tripos) (A : SET) (sa1 sa2 : A -> Prop) (pa : Carrier (Pred T A)) : LEq (Pred T A) (treflect T A (fun a => sa1 a /\ sa2 a)) pa -> LEq (Pred T A) (hconj (Pred T A) (treflect T A sa1) (treflect T A sa2)) pa.
 intro. eapply htrans; [ apply treflectconj | ]. assumption.
Qed.
Lemma tholdssubst {T : Tripos} {A B : SET} (f : A -> B) (p : Carrier (Pred T B)) : LEq (Pred T A) (carrier (subst T f) p) (carrier (subst T (fun a => chi T p (f a))) (holds T)) /\ LEq (Pred T A) (carrier (subst T (fun a => chi T p (f a))) (holds T)) (carrier (subst T f) p).
 split.
  apply tcompe. apply hmleq. apply tholds.
  apply tcompi. apply hmleq. apply tholds.
Qed.
Lemma tholdssubsti {T : Tripos} {A B : SET} (f : A -> B) (pb : Carrier (Pred T B)) (pa : Carrier (Pred T A)) : LEq (Pred T A) (carrier (subst T (fun a => chi T pb (f a))) (holds T)) pa <-> LEq (Pred T A) (carrier (subst T f) pb) pa.
 split; intro; (eapply htrans; [ apply (tholdssubst f) | ]; assumption).
Qed.
Lemma tholdssubste {T : Tripos} {A B : SET} (f : A -> B) (pa : Carrier (Pred T A)) (pb : Carrier (Pred T B)) : LEq (Pred T A) pa (carrier (subst T (fun a => chi T pb (f a))) (holds T)) <-> LEq (Pred T A) pa (carrier (subst T f) pb).
 split; intro; (eapply htrans; [ | apply (tholdssubst f) ]; assumption).
Qed.

Lemma tsubsteq {T : Tripos} {A B : SET} (f g : A -> B) : (forall a : A, f a = g a) -> PHARefines (subst T f) (subst T g).
 unfold PHARefines. intros fg pb. assert (LEq (Pred T (prod B B)) (treflect T (prod B B) (fun p => fst p = snd p)) (himp (Pred T (prod B B)) (carrier (subst T fst) pb) (carrier (subst T snd) pb))) as le.
  apply (treflectopcart T B (fun _ => True) (fun b => pair b b)).
   intros [ b b' ]. simpl. intro. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
  apply (hmleq (subst T (fun a => pair (f a) (g a)))) in le. apply treflectsubsti in le. simpl in le. apply hmimpe in le. apply himpr in le. apply tcompe in le. eapply htrans; [ clear le | apply le ]. apply hconji.
   eapply htrans; [ apply htopi | ]. eapply htrans; [ apply treflecttop | ]. apply treflectleq. auto.
   apply tcompe. simpl. apply tcompe. apply tide. apply hrefl.
Qed.

Definition ttop (T : Tripos) : Omega T
:= chi T (htop (Pred T unit)) tt.
Definition tconj (T : Tripos) (p1 p2 : Omega T) : Omega T
:= chi T (hconj (Pred T (prod (Omega T) (Omega T))) (carrier (subst T fst) (holds T)) (carrier (subst T snd) (holds T))) (pair p1 p2).
Definition tbot (T : Tripos) : Omega T
:= chi T (hbot (Pred T unit)) tt.
Definition tdisj (T : Tripos) (p1 p2 : Omega T) : Omega T
:= chi T (hdisj (Pred T (prod (Omega T) (Omega T))) (carrier (subst T fst) (holds T)) (carrier (subst T snd) (holds T))) (pair p1 p2).
Definition timp (T : Tripos) (p1 p2 : Omega T) : Omega T
:= chi T (himp (Pred T (prod (Omega T) (Omega T))) (carrier (subst T fst) (holds T)) (carrier (subst T snd) (holds T))) (pair p1 p2).

Lemma ttop_as_forall (T : Tripos) (A : SET) : LEq (Pred T A) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (carrier (subst T snd) (holds T)) (carrier (subst T snd) (holds T)))) (htop (Pred T A)) /\ LEq (Pred T A) (htop (Pred T A)) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (carrier (subst T snd) (holds T)) (carrier (subst T snd) (holds T)))).
 split.
  apply htopi.
  apply tforalladj. apply himpir. apply hconje2. apply hrefl.
Qed.
Lemma tconj_as_forall (T : Tripos) (A : SET) (pa1 pa2 : Carrier (Pred T A)) : LEq (Pred T A) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa1) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa2) (carrier (subst T snd) (holds T)))) (carrier (subst T snd) (holds T)))) (hconj (Pred T A) pa1 pa2) /\ LEq (Pred T A) (hconj (Pred T A) pa1 pa2) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa1) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa2) (carrier (subst T snd) (holds T)))) (carrier (subst T snd) (holds T)))).
 split.
  apply tforallproji with (chi T (hconj (Pred T A) pa1 pa2)). apply hmimpi. apply himpapp.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. simpl. apply tidi. apply hmimpe. apply himpir. apply tcompe. simpl. apply tholdssubste. apply tide. apply hconji.
    apply hconjp1.
    apply hconje2. apply tcompi. apply tid.
   apply tcompi. simpl. apply tholdssubsti. apply tid.
  apply tforalladj. apply hmconji. apply hconjsym. apply himpir. apply hconjassoc. apply himpl. apply himpl. apply hrefl.
Qed.
Lemma tbot_as_forall (T : Tripos) (A : SET) : LEq (Pred T A) (tforall T A (Omega T) (carrier (subst T snd) (holds T))) (hbot (Pred T A)) /\ LEq (Pred T A) (hbot (Pred T A)) (tforall T A (Omega T) (carrier (subst T snd) (holds T))).
 split.
  apply tforallproji with (chi T (hbot (Pred T A))). apply tcompi. apply tholdssubsti. apply hmbot.
  apply hbote.
Qed.
Lemma tdisj_as_forall (T : Tripos) (A : SET) (pa1 pa2 : Carrier (Pred T A)) : LEq (Pred T A) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa1) (carrier (subst T snd) (holds T))) (himp (Pred T (prod A (Omega T))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa2) (carrier (subst T snd) (holds T))) (carrier (subst T snd) (holds T))))) (hdisj (Pred T A) pa1 pa2) /\ LEq (Pred T A) (hdisj (Pred T A) pa1 pa2) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa1) (carrier (subst T snd) (holds T))) (himp (Pred T (prod A (Omega T))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa2) (carrier (subst T snd) (holds T))) (carrier (subst T snd) (holds T))))).
 split.
  apply tforallproji with (chi T (hdisj (Pred T A) pa1 pa2)). apply hmimpi. apply himpapp.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply hmdisje. apply hdisji1. apply hrefl.
   apply hmimpi. apply himpapp.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply hmdisje. apply hdisji2. apply hrefl.
    apply tcompi. simpl. apply tholdssubsti. apply tid.
  apply hdisje; apply tforalladj; apply himpir.
   apply himpir. apply hconje1. apply himppr.
   apply hconje1. apply himpir. apply himppr.
Qed.
Lemma texists_as_forall (T : Tripos) (A B : SET) (pab : Carrier (Pred T (prod A B))) : LEq (Pred T A) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (tforall T (prod A (Omega T)) B (himp (Pred T (prod (prod A (Omega T)) B)) (carrier (subst T (fun t => pair (fst (fst t)) (snd t))) pab) (carrier (subst T (fun t => snd (fst t))) (holds T)))) (carrier (subst T snd) (holds T)))) (texists T A B pab) /\ LEq (Pred T A) (texists T A B pab) (tforall T A (Omega T) (himp (Pred T (prod A (Omega T))) (tforall T (prod A (Omega T)) B (himp (Pred T (prod (prod A (Omega T)) B)) (carrier (subst T (fun t => pair (fst (fst t)) (snd t))) pab) (carrier (subst T (fun t => snd (fst t))) (holds T)))) (carrier (subst T snd) (holds T)))).
 split.
  apply tforallproji with (chi T (texists T A B pab)). apply hmimpi. apply himpapp.
   apply tforallsubste. apply tforalladj. apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply texistssubste. apply texistsproje with snd. apply tcompe. simpl. apply hrefl.
   apply tcompi. simpl. apply tholdssubsti. apply tid.
  apply texistsadj. apply tforallsubste. apply tforalladj. apply hmimpe. apply himpir. apply tcompe. simpl. apply himpl. apply tforallsubsti. apply tforallproji with (fun t => snd (fst t)). apply tcompi. simpl. apply hmimpi. apply himpm.
   apply tcompe. simpl. apply tsubsteq. intros [ [ ? ? ] ? ]. reflexivity.
   apply tcompi. simpl. apply hrefl.
Qed.

Definition tmeet (T : Tripos) : (Omega T -> Prop) -> Omega T
:= chi T (tforall T (Omega T -> Prop) (Omega T) (himp (Pred T (prod (Omega T -> Prop) (Omega T))) (treflect T (prod (Omega T -> Prop) (Omega T)) (fun p => (fst p) (snd p))) (carrier (subst T snd) (holds T)))).

Lemma tmeeti (T : Tripos) (A : Type) (sap : A -> Omega T -> Prop) (pa : Carrier (Pred T A)) : LEq (Pred T (prod A (Omega T))) (treflect T (prod A (Omega T)) (fun p => sap (fst p) (snd p))) (himp (Pred T (prod A (Omega T))) (carrier (subst T fst) pa) (carrier (subst T snd) (holds T))) -> LEq (Pred T A) pa (carrier (subst T (fun a => tmeet T (sap a))) (holds T)).
 intro. apply tholdssubste. apply tforallsubste. apply tforalladj. apply hmimpe. apply himpir. apply himpl. apply treflectsubsti. simpl. eapply htrans; [ eassumption | ]. clear. apply himpm2. apply tcompe. simpl. apply tcompe. apply tid.
Qed.
Lemma tmeete (T : Tripos) (A : Type) (sap : A -> Omega T -> Prop) (pa : A -> Omega T) (pa' : Carrier (Pred T A)) : (forall a : A, sap a (pa a)) -> LEq (Pred T A) (carrier (subst T pa) (holds T)) pa' -> LEq (Pred T A) (carrier (subst T (fun a => tmeet T (sap a))) (holds T)) pa'.
 intros. apply tholdssubsti. apply tforallsubsti. apply tforallproji with pa. apply tcompi. simpl. apply hmimpi. apply himpapp.
  apply treflectsubste. simpl. eapply htrans; [ apply treflecttop | ]. apply treflectleq. auto.
  apply tcompi. simpl. eapply htrans; [ | eassumption ]. apply tcompi. apply tid.
Qed.
Lemma tmeetreflecte (T : Tripos) (A : Type) (sa : A -> Prop) (sap : A -> Omega T -> Prop) (pa : A -> Omega T) (pa' : Carrier (Pred T A)) : (forall a : A, sa a -> sap a (pa a)) -> LEq (Pred T A) (carrier (subst T pa) (holds T)) pa' -> LEq (Pred T A) (hconj (Pred T A) (carrier (subst T (fun a => tmeet T (sap a))) (holds T)) (treflect T A sa)) pa'.
 intros. apply himpr. apply tholdssubsti. apply tforallsubsti. apply tforallproji with pa. apply tcompi. simpl. apply hmimpi. apply himpm.
  apply treflectsubste. simpl. apply treflectleq. auto.
  apply tcompi. simpl. eapply htrans; [ | eassumption ]. apply tcompi. apply tid.
Qed.


(** ** Morphisms *)

Record TriposMorphism {int : Prop} {T1 T2 : Tripos} : Type := tripos_morphism {
  Map : forall {A : SET}, Carrier (Pred T1 A) -> Carrier (Pred T2 A);
  mapleq : forall A : SET, forall pa pa' : Carrier (Pred T1 A), LEq (Pred T1 A) pa pa' -> LEq (Pred T2 A) (Map pa) (Map pa');
  mapconj : forall A : SET, forall pa1 pa2 : Carrier (Pred T1 A), LEq (Pred T2 A) (hconj (Pred T2 A) (Map pa1) (Map pa2)) (Map (hconj (Pred T1 A) pa1 pa2));
  mapimp : forall A : SET, forall pai pao : Carrier (Pred T1 A), LEq (Pred T2 A) (himp (Pred T2 A) (Map pai) (Map pao)) (Map (himp (Pred T1 A) pai pao));
  mapsubst : forall A B : SET, forall f : A -> B, forall pb : Carrier (Pred T1 B), LEq (Pred T2 A) (carrier (subst T2 f) (Map pb)) (Map (carrier (subst T1 f) pb)) /\ LEq (Pred T2 A) (Map (carrier (subst T1 f) pb)) (carrier (subst T2 f) (Map pb));
  mapforall : forall A B : SET, forall pab : Carrier (Pred T1 (prod A B)), LEq (Pred T2 A) (tforall T2 A B (Map pab)) (Map (tforall T1 A B pab));
  mapreflect : forall A : SET, forall sa : A -> Prop, LEq (Pred T2 A) (Map (treflect T1 A sa)) (treflect T2 A sa) /\ LEq (Pred T2 A) (treflect T2 A sa) (Map (treflect T1 A sa));
  mapomega : exists2 f : Omega T2 -> Omega T1, LEq (Pred T2 (Omega T2)) (holds T2) (carrier (subst T2 f) (Map (holds T1))) /\ LEq (Pred T2 (Omega T2)) (carrier (subst T2 f) (Map (holds T1))) (holds T2) & int -> exists2 finv : Omega T1 -> Omega T2, (fun p1 : Omega T1 => p1) = (fun p1 : Omega T1 => f (finv p1)) & (fun p2 : Omega T2 => p2) = (fun p2 : Omega T2 => finv (f p2))
}.
Arguments TriposMorphism : clear implicits.

Lemma mapsubsti {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A B : SET) (f : A -> B) (pb : Carrier (Pred T1 B)) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) (carrier (subst T2 f) (Map F pb)) pa <-> LEq (Pred T2 A) (Map F (carrier (subst T1 f) pb)) pa.
 split; intro; eapply htrans; try eassumption; apply mapsubst.
Qed.
Lemma mapsubste {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A B : SET) (f : A -> B) (pb : Carrier (Pred T1 B)) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) pa (carrier (subst T2 f) (Map F pb)) <-> LEq (Pred T2 A) pa (Map F (carrier (subst T1 f) pb)).
 split; intro; eapply htrans; try eassumption; apply mapsubst.
Qed.
Lemma mapforalli {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A B : SET) (pab : Carrier (Pred T1 (prod A B))) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) (tforall T2 A B (Map F pab)) pa <-> LEq (Pred T2 A) (Map F (tforall T1 A B pab)) pa.
 split; intro.
  eapply htrans; try eassumption. apply tforalladj. apply mapsubsti. apply mapleq. apply tforalladj. apply hrefl.
  eapply htrans; try eassumption. apply mapforall.
Qed.
Lemma mapforalle {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A B : SET) (pab : Carrier (Pred T1 (prod A B))) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) pa (tforall T2 A B (Map F pab)) <-> LEq (Pred T2 A) pa (Map F (tforall T1 A B pab)).
 split; intro; eapply htrans; try eassumption; apply mapforalli; apply hrefl.
Qed.
Lemma mapconji {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) (pa1 pa2 : Carrier (Pred T1 A)) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) (hconj (Pred T2 A) (Map F pa1) (Map F pa2)) pa <-> LEq (Pred T2 A) (Map F (hconj (Pred T1 A) pa1 pa2)) pa.
 split; intro.
  eapply htrans; try eassumption. apply hconji.
   apply mapleq. apply hconjp1.
   apply mapleq. apply hconjp2.
  eapply htrans; try eassumption. apply mapconj.
Qed.
Lemma mapimpi {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) (pai pao : Carrier (Pred T1 A)) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) (himp (Pred T2 A) (Map F pai) (Map F pao)) pa <-> LEq (Pred T2 A) (Map F (himp (Pred T1 A) pai pao)) pa.
 split; intro.
  eapply htrans; try eassumption. apply himpil. apply mapconji. apply mapleq. apply himppr.
  eapply htrans; try eassumption. apply mapimp.
Qed.
Lemma mapimpe {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) (pai pao : Carrier (Pred T1 A)) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) pa (himp (Pred T2 A) (Map F pai) (Map F pao)) <-> LEq (Pred T2 A) pa (Map F (himp (Pred T1 A) pai pao)).
 split; intro; eapply htrans; try eassumption; apply mapimpi; apply hrefl.
Qed.

Lemma maptop {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) : LEq (Pred T2 A) (htop (Pred T2 A)) (Map F (htop (Pred T1 A))).
 eapply htrans; [ | apply mapleq; apply ttop_as_forall ]. eapply htrans; [ | apply mapforall ]. apply tforalladj. eapply htrans; [ | apply mapimp ]. apply himpir. apply hconjp2.
Qed.
Lemma maptopi {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) (htop (Pred T2 A)) pa <-> LEq (Pred T2 A) (Map F (htop (Pred T1 A))) pa.
 split; intro; eapply htrans; try eassumption.
  apply htopi.
  apply maptop.
Qed.
Lemma maptope {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) (pa : Carrier (Pred T2 A)) : LEq (Pred T2 A) pa (htop (Pred T2 A)) <-> LEq (Pred T2 A) pa (Map F (htop (Pred T1 A))).
 split; intro; eapply htrans; try eassumption; apply (maptopi F); apply hrefl.
Qed.
Lemma mapbot {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) : LEq (Pred T2 A) (Map F (hbot (Pred T1 A))) (hbot (Pred T2 A)).
 eapply htrans; [ apply mapleq; apply tbot_as_forall | ]. eapply htrans; [ | apply tbot_as_forall ]. apply mapforalli. apply tforalladj. apply tforallsubsti. destruct (mapomega F) as [ f mapomega _ ]. apply tforallproji with (fun p => f (snd p)). apply tcompi. simpl. apply mapsubsti. eapply htrans; [ apply mapleq; apply tcomp | ]. simpl. apply mapsubsti. apply tcompi. apply hmleq. apply mapomega.
Qed.
Lemma mapdisj {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A : SET) (pa1 pa2 : Carrier (Pred T1 A)) : LEq (Pred T2 A) (Map F (hdisj (Pred T1 A) pa1 pa2)) (hdisj (Pred T2 A) (Map F pa1) (Map F pa2)).
 eapply htrans; [ apply mapleq; apply tdisj_as_forall | ]. eapply htrans; [ | apply tdisj_as_forall ]. apply mapforalli. apply tforalladj. apply tforallsubsti. destruct (mapomega F) as [ f mapomega _ ]. apply tforallproji with (fun p => f (snd p)). apply tcompi. simpl. eapply htrans.
  apply mapsubsti. apply mapleq. apply hmimpi. apply himpm.
   apply hmimpe. apply himpm.
    apply tcompi. simpl. apply tcompi. apply tidi. apply hrefl.
    apply tcompe. simpl. apply hrefl.
   apply hmimpi. apply himpm.
    apply hmimpe. apply himpm.
     apply tcompi. simpl. apply tcompi. apply tidi. apply hrefl.
     apply tcompe. simpl. apply hrefl.
    apply tcompi. simpl. apply hrefl.
 apply mapimpi. apply himpm.
  apply mapimpe. apply himpm.
   apply mapsubst.
   apply mapsubste. apply tcompe. apply hmleq. apply mapomega.
  apply mapimpi. apply himpm.
   apply mapimpe. apply himpm.
    apply mapsubst.
    apply mapsubste. apply tcompe. apply hmleq. apply mapomega.
   apply mapsubsti. apply tcompi. apply hmleq. apply mapomega.
Qed.
Lemma mapexists {int : Prop} {T1 T2 : Tripos} (F : TriposMorphism int T1 T2) (A B : SET) (pab : Carrier (Pred T1 (prod A B))) : LEq (Pred T2 A) (Map F (texists T1 A B pab)) (texists T2 A B (Map F pab)).
 eapply htrans; [ apply mapleq; apply texists_as_forall | ]. eapply htrans; [ | apply texists_as_forall ]. apply mapforalli. apply tforalladj. apply tforallsubsti. destruct (mapomega F) as [ f mapomega _ ]. apply tforallproji with (fun p => f (snd p)). apply tcompi. simpl. eapply htrans.
  apply mapsubsti. apply mapleq. apply hmimpi. apply himpm.
   apply tforallsubste. apply tforallm. apply hmimpe. apply himpm.
    apply tcompi. simpl. apply hrefl.
    apply tcompe. simpl. apply hrefl.
   apply tcompi. simpl. apply hrefl.
  apply mapimpi. apply himpm.
   apply mapforalle. apply tforallm. apply mapimpe. apply himpm.
    apply mapsubst.
    apply mapsubste. apply tcompe. apply hmleq. apply mapomega.
   apply mapsubsti. apply tcompi. apply hmleq. apply mapomega.
Qed.
(* TODO: mapeq *)

Definition tripos_id (int : Prop) (T : Tripos) : TriposMorphism int T T.
refine (tripos_morphism int T T (fun A p => p) _ _ _ _ _ _ _).
 intros. assumption.
 intros. apply hrefl.
 intros. apply hrefl.
 intros. split; apply hrefl.
 intros. apply hrefl.
 intros. split; apply hrefl.
 exists (fun p => p).
  split; apply tid.
  intros _. exists (fun p => p); reflexivity.
Defined.
Definition tripos_comp {int : Prop} {T1 T2 T3 : Tripos} (F : TriposMorphism int T1 T2) (G : TriposMorphism int T2 T3) : TriposMorphism int T1 T3.
refine (tripos_morphism int T1 T3 (fun A p1 => Map G (Map F p1)) _ _ _ _ _ _ _).
 intros. apply mapleq. apply mapleq. assumption.
 intros. eapply htrans; try apply mapconj. apply mapleq. apply mapconj.
 intros. eapply htrans; try apply mapimp. apply mapleq. apply mapimp.
 intros. split; eapply htrans; try apply mapsubst; apply mapleq; apply mapsubst.
 intros. eapply htrans; try apply mapforall. apply mapleq. apply mapforall.
 intros. split; eapply htrans; try eapply mapreflect; apply mapleq; apply mapreflect.
 destruct (mapomega F) as [ f mapomegaF intF ]. destruct (mapomega G) as [ g mapomegaG intG ]. exists (fun p1 => f (g p1)).
  split; eapply htrans; try apply mapomegaG.
   apply tcompe. apply hmleq. apply mapsubste. apply mapleq. apply mapomegaF.
   apply tcompi. apply hmleq. apply mapsubsti. apply mapleq. apply mapomegaF.
 intro i. destruct intF as [ finv finvf ffinv ]; try assumption. destruct intG as [ ginv ginvg gginv ]; try assumption. exists (fun p => ginv (finv p)).
  change ((fun p => p) = (fun p => f ((fun p => g (ginv p)) (finv p)))). rewrite <- ginvg. assumption.
  change ((fun p => p) = (fun p => ginv ((fun p => finv (f p)) (g p)))). rewrite <- ffinv. assumption.
Defined.

Definition TriposRefines {int : Prop} {T1 T2 : Tripos} (F G : TriposMorphism int T1 T2) : Prop
:= forall A : SET, forall p : Carrier (Pred T1 A), LEq (Pred T2 A) (Map F p) (Map G p).
Definition TriposEquiv {int : Prop} {T1 T2 : Tripos} (F G : TriposMorphism int T1 T2) : Prop
:= forall A : SET, forall p : Carrier (Pred T1 A), LEq (Pred T2 A) (Map F p) (Map G p) /\ LEq (Pred T2 A) (Map G p) (Map F p).

(** ** Categories Trip_int / Trip_ext **)

Program Definition TriposCategory (int : Prop) : LocallyPreorderedBicategory
:= locally_preordered_bicategory Tripos (TriposMorphism int) (@TriposRefines int) (tripos_id int) (@tripos_comp int) _ _ _ _ _ _.
Obligation Tactic := intro int; unfold TriposRefines; simpl.
Next Obligation. intros. apply hrefl. Qed.
Next Obligation. intros T1 T2 F G H ? ? ? p. apply htrans with (Map G p); auto. Qed.
Next Obligation. intros T1 T2 T3 F F' G G' ? ? ? p. apply htrans with (Map G (Map F' p)); try auto. apply mapleq. auto. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.




(** * Set-Based Triposes *)

(** ** Definition *)

Definition Pullback {A1 A2 B1 B2 : SET} (a12 : A1 -> A2) (b12 : B1 -> B2) (ab1 : A1 -> B1) (ab2 : A2 -> B2) : Prop
:= (forall a1 : A1, ab2 (a12 a1) = b12 (ab1 a1))
/\ (forall a1 a1' : A1, a12 a1 = a12 a1' -> ab1 a1 = ab1 a1' -> a1 = a1')
/\ (forall X : SET, forall fa2 : X -> A2, forall fb1 : X -> B1, (forall x : X, ab2 (fa2 x) = b12 (fb1 x)) -> exists2 fa1 : X -> A1, (forall x : X, a12 (fa1 x) = fa2 x) & (forall x : X, ab1 (fa1 x) = fb1 x)).

Record SetTripos : Class := set_tripos {
  sPred : SET -> PreHeytingAlgebra;
  ssubst : forall {A B : SET}, (A -> B) -> PHAMorphism (sPred B) (sPred A);
  stforall : forall A B : SET, (A -> B) -> Carrier (sPred A) -> Carrier (sPred B);
  stexists : forall A B : SET, (A -> B) -> Carrier (sPred A) -> Carrier (sPred B);
  sOmega : SET;
  sholds : Carrier (sPred sOmega);
  schi : forall {A : SET}, Carrier (sPred A) -> A -> sOmega;
  stid : forall A : SET, PHARefines (hmid (sPred A)) (ssubst (fun a => a)) /\ PHARefines (ssubst (fun a => a)) (hmid (sPred A));
  stcomp : forall {A B C : SET}, forall f : A -> B, forall g : B -> C, PHARefines (hmcomp (ssubst g) (ssubst f)) (ssubst (fun a => g (f a))) /\ PHARefines (ssubst (fun a => g (f a))) (hmcomp (ssubst g) (ssubst f));
  stforallsubst : forall {A1 A2 B1 B2 : SET}, forall a12 : A1 -> A2, forall b12 : B1 -> B2, forall ab1 : A1 -> B1, forall ab2 : A2 -> B2, forall pb1 : Carrier (sPred B1), Pullback a12 b12 ab1 ab2 -> LEq (sPred A2) (stforall A1 A2 a12 (carrier (ssubst ab1) pb1)) (carrier (ssubst ab2) (stforall B1 B2 b12 pb1));
  stforalladj : forall A B : SET, forall f : A -> B, forall pa : Carrier (sPred A), forall pb : Carrier (sPred B), LEq (sPred A) (carrier (ssubst f) pb) pa <-> LEq (sPred B) pb (stforall A B f pa);
  stexistssubst : forall {A1 A2 B1 B2 : SET}, forall a12 : A1 -> A2, forall b12 : B1 -> B2, forall ab1 : A1 -> B1, forall ab2 : A2 -> B2, forall pb1 : Carrier (sPred B1), Pullback a12 b12 ab1 ab2 -> LEq (sPred A2) (carrier (ssubst ab2) (stexists B1 B2 b12 pb1)) (stexists A1 A2 a12 (carrier (ssubst ab1) pb1));
  stexistsadj : forall A B : SET, forall f : A -> B, forall pa : Carrier (sPred A), forall pb : Carrier (sPred B), LEq (sPred A) pa (carrier (ssubst f) pb) <-> LEq (sPred B) (stexists A B f pa) pb;
  stholds : forall A : SET, forall p : Carrier (sPred A), LEq (sPred A) p (carrier (ssubst (schi p)) sholds) /\ LEq (sPred A) (carrier (ssubst (schi p)) sholds) p
}.

Lemma stforallsubstproji {S : SetTripos} {A B C : SET} (g : C -> A) (f : A -> B) (h : C -> B) (pa : Carrier (sPred S A)) (pc : Carrier (sPred S C)) : (fun c : C => f (g c)) = h -> LEq (sPred S C) (carrier (ssubst S g) pa) pc -> LEq (sPred S C) (carrier (ssubst S h) (stforall S A B f pa)) pc.
 intro e. intro. eapply htrans; try eassumption. rewrite <- e. eapply htrans; [ apply stcomp | ]. simpl. apply hmleq. apply stforalladj. apply hrefl.
Qed.
Lemma stforallproji {S : SetTripos} {A B : SET} (g : B -> A) (f : A -> B) (pa : Carrier (sPred S A)) (pb : Carrier (sPred S B)) : (fun b : B => f (g b)) = (fun b : B => b) -> LEq (sPred S B) (carrier (ssubst S g) pa) pb -> LEq (sPred S B) (stforall S A B f pa) pb.
 intro e. intro. eapply htrans; [ apply stid | ]. apply stforallsubstproji with g; assumption.
Qed.
Lemma stforallm (S : SetTripos) (A B : SET) (f : A -> B) (pa pa' : Carrier (sPred S A)) : LEq (sPred S A) pa pa' -> LEq (sPred S B) (stforall S A B f pa) (stforall S A B f pa').
 intro. apply stforalladj. eapply htrans; [ | eassumption ]. apply stforalladj. apply hrefl.
Qed.
Lemma stexistssubstproje {S : SetTripos} {A B C : SET} (g : C -> A) (f : A -> B) (h : C -> B) (pa : Carrier (sPred S A)) (pc : Carrier (sPred S C)) : (fun c : C => f (g c)) = h -> LEq (sPred S C) pc (carrier (ssubst S g) pa) -> LEq (sPred S C) pc (carrier (ssubst S h) (stexists S A B f pa)).
 intro e. intro. eapply htrans; try eassumption. rewrite <- e. eapply htrans; [ | apply stcomp ]. simpl. apply hmleq. apply stexistsadj. apply hrefl.
Qed.
Lemma stexistsproje {S : SetTripos} {A B : SET} (g : B -> A) (f : A -> B) (pa : Carrier (sPred S A)) (pb : Carrier (sPred S B)) : (fun b : B => f (g b)) = (fun b : B => b) -> LEq (sPred S B) pb (carrier (ssubst S g) pa) -> LEq (sPred S B) pb (stexists S A B f pa).
 intro e. intro. eapply htrans; try eassumption. eapply htrans; [ | apply stid ]. rewrite <- e. eapply htrans; [ | apply stcomp ]. simpl. apply hmleq. apply stexistsadj. apply hrefl.
Qed.
Lemma stexistsm (S : SetTripos) (A B : SET) (f : A -> B) (pa pa' : Carrier (sPred S A)) : LEq (sPred S A) pa pa' -> LEq (sPred S B) (stexists S A B f pa) (stexists S A B f pa').
 intro. apply stexistsadj. eapply htrans; [ eassumption | ]. apply stexistsadj. apply hrefl.
Qed.

Lemma sttop_as_forall (S : SetTripos) (A : SET) : LEq (sPred S A) (stforall S (prod A (sOmega S)) A fst (himp (sPred S (prod A (sOmega S))) (carrier (ssubst S snd) (sholds S)) (carrier (ssubst S snd) (sholds S)))) (htop (sPred S A)) /\ LEq (sPred S A) (htop (sPred S A)) (stforall S (prod A (sOmega S)) A fst (himp (sPred S (prod A (sOmega S))) (carrier (ssubst S snd) (sholds S)) (carrier (ssubst S snd) (sholds S)))).
 split.
  apply htopi.
  apply stforalladj. apply himpir. apply hconje2. apply hrefl.
Qed.
Lemma stexists_as_forall (S : SetTripos) (A B : SET) (f : A -> B) (pa : Carrier (sPred S A)) : LEq (sPred S B) (stforall S (prod B (sOmega S)) B fst (himp (sPred S (prod B (sOmega S))) (stforall S (prod A (sOmega S)) (prod B (sOmega S)) (fun p => pair (f (fst p)) (snd p)) (himp (sPred S (prod A (sOmega S))) (carrier (ssubst S fst) pa) (carrier (ssubst S snd) (sholds S)))) (carrier (ssubst S snd) (sholds S)))) (stexists S A B f pa) /\ LEq (sPred S B) (stexists S A B f pa) (stforall S (prod B (sOmega S)) B fst (himp (sPred S (prod B (sOmega S))) (stforall S (prod A (sOmega S)) (prod B (sOmega S)) (fun p => pair (f (fst p)) (snd p)) (himp (sPred S (prod A (sOmega S))) (carrier (ssubst S fst) pa) (carrier (ssubst S snd) (sholds S)))) (carrier (ssubst S snd) (sholds S)))).
 split.
  apply stforallproji with (fun b => pair b (schi S (stexists S A B f pa) b)); try reflexivity. apply hmimpi. apply himpapp.
   eapply htrans; [ | eapply (stforallsubst S f _ (fun a => pair a (schi S (stexists S A B f pa) (f a)))) ].
    apply stforalladj. apply hmimpe. apply himpir. apply hconje2. eapply htrans; [ apply stcomp | ]. eapply htrans; [ | apply stcomp ]. simpl. eapply htrans; [ | apply stcomp ]. simpl. apply stexistsadj. eapply htrans; [ | apply (stholds S _ (stexists S A B f pa)) ]. apply stexistsm. apply stid.
    unfold Pullback. repeat split.
     intros a a' _ e. inversion e. reflexivity.
     intros X fa2 fb1 e. exists (fun x => fst (fb1 x)).
      intro x. specialize (e x). inversion e. reflexivity.
      intro x. specialize (e x). destruct (fb1 x). simpl in *. inversion e. reflexivity.
   eapply htrans; [ apply stcomp | ]. simpl. eapply htrans; [ apply stholds | ]. apply hrefl.
  apply stexistsadj. eapply htrans; [ | eapply (stforallsubst S fst fst (fun p => pair (f (fst p)) (snd p)) f) ].
   apply stforalladj. apply hmimpe. apply himpir. eapply htrans; [ | apply stcomp ]. apply himpl. apply stforallsubstproji with (fun p => p); try reflexivity. eapply htrans; [ apply stid | ]. simpl. apply himpm.
    apply hrefl.
    eapply htrans; [ | apply stcomp ]. simpl. apply stid.
   unfold Pullback. repeat split.
    intros [ a p ] [ a' p' ]. simpl. intros ? e. inversion e. subst. reflexivity.
    intros X fa2 fb1 e. exists (fun x => pair (fa2 x) (snd (fb1 x))).
     trivial.
     intro x. specialize (e x). destruct (fb1 x). simpl in *. subst. reflexivity.
Qed.

(** ** Morphisms *)

Record SetTriposMorphism {int : Prop} {S1 S2 : SetTripos} : Type := set_tripos_morphism {
  sMap : forall {A : SET}, Carrier (sPred S1 A) -> Carrier (sPred S2 A);
  smapleq : forall A : SET, forall pa pa' : Carrier (sPred S1 A), LEq (sPred S1 A) pa pa' -> LEq (sPred S2 A) (sMap pa) (sMap pa');
  smapconj : forall A : SET, forall pa1 pa2 : Carrier (sPred S1 A), LEq (sPred S2 A) (hconj (sPred S2 A) (sMap pa1) (sMap pa2)) (sMap (hconj (sPred S1 A) pa1 pa2));
  smapimp : forall A : SET, forall pai pao : Carrier (sPred S1 A), LEq (sPred S2 A) (himp (sPred S2 A) (sMap pai) (sMap pao)) (sMap (himp (sPred S1 A) pai pao));
  smapsubst : forall A B : SET, forall f : A -> B, forall pb : Carrier (sPred S1 B), LEq (sPred S2 A) (carrier (ssubst S2 f) (sMap pb)) (sMap (carrier (ssubst S1 f) pb)) /\ LEq (sPred S2 A) (sMap (carrier (ssubst S1 f) pb)) (carrier (ssubst S2 f) (sMap pb));
  smapforall : forall A B : SET, forall f : A -> B, forall pa : Carrier (sPred S1 A), LEq (sPred S2 B) (stforall S2 A B f (sMap pa)) (sMap (stforall S1 A B f pa));
  smapomega : exists2 f : sOmega S2 -> sOmega S1, LEq (sPred S2 (sOmega S2)) (sholds S2) (carrier (ssubst S2 f) (sMap (sholds S1))) /\ LEq (sPred S2 (sOmega S2)) (carrier (ssubst S2 f) (sMap (sholds S1))) (sholds S2) & int -> exists2 finv : sOmega S1 -> sOmega S2, (fun p1 : sOmega S1 => p1) = (fun p1 : sOmega S1 => f (finv p1)) & (fun p2 : sOmega S2 => p2) = (fun p2 : sOmega S2 => finv (f p2))
}.
Arguments SetTriposMorphism : clear implicits.

Lemma smapimpi {int : Prop} {S1 S2 : SetTripos} (F : SetTriposMorphism int S1 S2) (A : SET) (pai pao : Carrier (sPred S1 A)) (pa : Carrier (sPred S2 A)) : LEq (sPred S2 A) (himp (sPred S2 A) (sMap F pai) (sMap F pao)) pa <-> LEq (sPred S2 A) (sMap F (himp (sPred S1 A) pai pao)) pa.
 split; intro; eapply htrans; try eassumption.
  apply himpir. eapply htrans; [ apply smapconj | ]. apply smapleq. apply himpr. apply hrefl.
  apply smapimp.
Qed.
Lemma smapforalli {int : Prop} {S1 S2 : SetTripos} (F : SetTriposMorphism int S1 S2) (A B : SET) (f : A -> B) (pa : Carrier (sPred S1 A)) (pb : Carrier (sPred S2 B)) : LEq (sPred S2 B) (stforall S2 A B f (sMap F pa)) pb <-> LEq (sPred S2 B) (sMap F (stforall S1 A B f pa)) pb.
 split; intro; eapply htrans; try eassumption.
  apply stforalladj. eapply htrans; [ apply smapsubst | ]. apply smapleq. apply stforalladj. apply hrefl.
  apply smapforall.
Qed.

Lemma smaptop {int : Prop} {S1 S2 : SetTripos} (F : SetTriposMorphism int S1 S2) (A : SET) : LEq (sPred S2 A) (htop (sPred S2 A)) (sMap F (htop (sPred S1 A))).
 eapply htrans; [ | apply smapleq; apply sttop_as_forall ]. eapply htrans; [ | apply smapforall ]. apply stforalladj. eapply htrans; [ | apply smapimp ]. apply himpir. apply hconjp2.
Qed.
Lemma smapexists {int : Prop} {S1 S2 : SetTripos} (F : SetTriposMorphism int S1 S2) (A B : SET) (f : A -> B) (pa : Carrier (sPred S1 A)) : LEq (sPred S2 B) (sMap F (stexists S1 A B f pa)) (stexists S2 A B f (sMap F pa)).
 eapply htrans; [ apply smapleq; apply stexists_as_forall | ]. eapply htrans; [ | apply stexists_as_forall ]. apply smapforalli. apply stforalladj. destruct (smapomega F) as [ sf smapomega _ ]. apply stforallsubstproji with (fun p => pair (fst p) (sf (snd p))); try reflexivity. eapply htrans.
  eapply htrans; [ apply smapsubst | ]. apply smapleq. apply hmimpi. apply himpm.
   eapply htrans; [ | eapply (stforallsubst S1 (fun p => pair (f (fst p)) (snd p)) _ (fun p => pair (fst p) (sf (snd p)))) ].
    apply stforallm. apply hmimpe. apply himpm; apply stcomp.
    repeat split.
     intros [ a p2 ] [ a' p2' ]. simpl. intros ep2 ea. inversion ep2. inversion ea. reflexivity.
     intros X fa2 fb1 e. exists (fun x => pair (fst (fb1 x)) (snd (fa2 x))).
      intro x. specialize (e x). destruct (fa2 x). simpl in *. inversion e. reflexivity.
      intro x. specialize (e x). destruct (fb1 x). simpl in *. inversion e. reflexivity.
   eapply htrans; [ apply stcomp | ]. simpl. apply hrefl.
  apply smapimpi. apply himpm.
   eapply htrans; [ | apply smapforall ]. apply stforallm. eapply htrans; [ | apply smapimp ]. apply himpm.
    apply smapsubst.
    eapply htrans; [ | apply smapsubst ]. simpl. eapply htrans; [ | apply stcomp ]. simpl. apply hmleq. apply smapomega.
   eapply htrans; [ apply smapsubst | ]. eapply htrans; [ apply stcomp | ]. simpl. apply hmleq. apply smapomega.
Qed.


(** ** Categories of Set-Bases Triposes *)

Definition SetTriposRefines {int : Prop} {S1 S2 : SetTripos} (F G : SetTriposMorphism int S1 S2) : Prop
:= forall A : SET, forall p : Carrier (sPred S1 A), LEq (sPred S2 A) (sMap F p) (sMap G p).

Definition SurjectiveSubstitutionsReflect (S : SetTripos) : Prop
:= forall A B : SET, forall f : A -> B, forall pb pb' : Carrier (sPred S B), (forall b : B, exists a : A, f a = b) -> LEq (sPred S A) (carrier (ssubst S f) pb) (carrier (ssubst S f) pb') -> LEq (sPred S B) pb pb'.

Program Definition SurjSetTriposCategory (int : Prop) : LocallyPreorderedBicategory
:= locally_preordered_bicategory (sig SurjectiveSubstitutionsReflect)
                                 (fun S1 S2 => SetTriposMorphism int (proj1_sig S1) (proj1_sig S2))
                                 (fun S1 S2 => @SetTriposRefines int (proj1_sig S1) (proj1_sig S2))
                                 (fun S => set_tripos_morphism int (proj1_sig S) (proj1_sig S) (fun A p => p) _ _ _ _ _ _)
                                 (fun S1 S2 S3 F G => set_tripos_morphism int (proj1_sig S1) (proj1_sig S3) (fun A p1 => sMap G (sMap F p1)) _ _ _ _ _ _)
                                 _ _ _ _ _ _.
Obligation Tactic := intros int [ S ? ]; simpl; clear.
Next Obligation. auto. Qed.
Next Obligation. intros. apply hrefl. Qed.
Next Obligation. intros. apply hrefl. Qed.
Next Obligation. intros. split; apply hrefl. Qed.
Next Obligation. intros. apply hrefl. Qed.
Next Obligation.
 exists (fun p => p).
  split; apply stid.
  intros _. exists (fun p => p); reflexivity.
Qed.
Obligation Tactic := intros int [ S1 ? ] [ S2 ? ] [ S3 ? ]; simpl; clear.
Next Obligation. intros. apply smapleq. apply smapleq. assumption. Qed.
Next Obligation. intros. eapply htrans; [ apply smapconj | ]. apply smapleq. apply smapconj. Qed.
Next Obligation. intros. eapply htrans; [ apply smapimp | ]. apply smapleq. apply smapimp. Qed.
Next Obligation.
 intros. split.
  eapply htrans; [ apply smapsubst | ]. apply smapleq. apply smapsubst.
  eapply htrans; [ | apply smapsubst ]. apply smapleq. apply smapsubst.
Qed.
Next Obligation. intros. eapply htrans; [ apply smapforall | ]. apply smapleq. apply smapforall. Qed.
Next Obligation. intros. destruct (smapomega F) as [ f [ ? ? ] finv ]. destruct (smapomega G) as [ g [ ? ? ] ginv ]. exists (fun p3 => f (g p3)).
 split.
  eapply htrans; [ eassumption | ]. eapply htrans; [ apply smapsubst | ]. eapply htrans; [ | apply smapsubst ]. apply smapleq. eapply htrans; [ | apply stcomp ]. simpl. apply hmleq. assumption.
  eapply htrans; [ | eassumption ]. eapply htrans; [ | apply smapsubst ]. eapply htrans; [ apply smapsubst | ]. apply smapleq. eapply htrans; [ apply stcomp | ]. simpl. apply hmleq. assumption.
 intro i. destruct finv as [ finv finvf ffinv ]; try assumption. destruct ginv as [ ginv ginvg gginv ]; try assumption. exists (fun p1 => ginv (finv p1)).
  change ((fun p1 => p1) = (fun p1 => f ((fun p2 => g (ginv p2)) (finv p1)))). rewrite <- ginvg. assumption.
  change ((fun p1 => p1) = (fun p3 => ginv ((fun p2 => finv (f p2)) (g p3)))). rewrite <- ffinv. assumption.
Qed.
Obligation Tactic := intros int [ S1 ? ] [ S2 ? ]; unfold SetTriposRefines; simpl; clear.
Next Obligation. intros. apply hrefl. Qed.
Next Obligation. intros. eapply htrans; auto. Qed.
Next Obligation. intros. eapply htrans; try auto. apply smapleq. auto. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.


(** * Reflection-Based Tripos and Set-Based Tripos with Reflective Surjective Substitutions Equivalence *)

Program Definition tripos_to_set_tripos (int : Prop) : Pseudofunctor (TriposCategory int) (SurjSetTriposCategory int)
:= pseudofunctor (TriposCategory int)
                 (SurjSetTriposCategory int)
                 (fun T => exist _ (set_tripos (Pred T) (@subst T) (fun A B f pa => tforall T B A (himp (Pred T (prod B A)) (treflect T (prod B A) (fun p => f (snd p) = fst p)) (carrier (subst T snd) pa))) (fun A B f pa => texists T B A (hconj (Pred T (prod B A)) (treflect T (prod B A) (fun p => f (snd p) = fst p)) (carrier (subst T snd) pa))) (Omega T) (holds T) (@chi T) _ _ _ _ _ _ _) _)
                 (fun T1 T2 F => set_tripos_morphism int _ _ (@Map int T1 T2 F) _ _ _ _ _ _)
                 _ _ _.
Obligation Tactic := simpl; intros int T.
Next Obligation. apply tid. Qed.
Next Obligation. apply tcomp. Qed.
Next Obligation.
 intros A1 A2 B1 B2 a12 b12 ab1 ab2 pb1 e. apply tforallsubste. apply tforalladj. apply hmimpe. apply himpir. apply tcompe. simpl. apply himpl. apply treflectsubsti. simpl. apply treflectopcart with A1 (fun _ => True) (fun a1 => pair (a12 a1) (ab1 a1)).
  destruct e as [ comm [ mono uni ] ]. specialize (uni (@sig (prod A2 B1) (fun p => b12 (snd p) = ab2 (fst p))) (fun p => fst (proj1_sig p)) (fun p => snd (proj1_sig p))). destruct uni as [ fa1 ? ? ].
   intros [ [ a2 b1 ] e ]. simpl in *. symmetry. assumption.
   intros [ a2 b1 ]. simpl. intro e. exists (fa1 (exist (fun p => b12 (snd p) = ab2 (fst p)) (pair a2 b1) e)); try trivial. f_equal.
    apply H.
    apply H0.
  apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tforallsubsti. apply tforallproji with (fun a => a). apply tcompi. simpl. apply hmimpi. apply himpapp.
   eapply htrans; [ apply treflecttop | ]. apply treflectsubste. apply treflectleq. auto.
   apply tcompi. simpl. apply tcomp.
Qed.
Next Obligation.
 intros. split; intro le.
  apply tforalladj. apply himpir. apply himpl. apply treflectopcart with A (fun _ => True) (fun a => pair (f a) a).
   intros [ ? ? ]. simpl. intro. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tcompi. apply tidi. apply tide. assumption.
  apply tforalladj in le. apply himpr in le. apply himpil in le. apply htrans with (hconj (Pred T A) (treflect T A (fun _ => True)) (carrier (subst T f) pb)).
   apply hconji; try apply hrefl. eapply htrans; try apply treflecttop. apply htopi.
   apply himpr. apply treflectopcart with (prod B A) (fun p => f (snd p) = fst p) snd.
    intros a _. exists (pair (f a) a); trivial.
    eapply htrans; [ apply hconji; [ apply hrefl | apply le ] | ]. clear le. apply himpr. apply treflectopcart with (sig (fun p : prod B A => f (snd p) = fst p)) (fun _ => True) (@proj1_sig (prod B A) (fun p => f (snd p) = fst p)).
     intros p e. exists (exist _ p e); trivial.
    apply hmimpe. apply himpir. apply hconje2. apply tcompe. apply hmimpe. apply hmimpi. apply himpm.
     apply tcompi. apply tcompe. apply tsubsteq. intros [ ? ? ]. simpl. assumption.
     apply tcomp.
Qed.
Next Obligation.
 intros A1 A2 B1 B2 a12 b12 ab1 ab2 pb1 e. apply texistssubsti. apply texistsadj. apply hmconji. apply himpl. apply tcompi. simpl. apply himpir. apply himpl. apply treflectsubsti. simpl. apply treflectopcart with A1 (fun _ => True) (fun a1 => pair (a12 a1) (ab1 a1)).
  destruct e as [ comm [ mono uni ] ]. specialize (uni (@sig (prod A2 B1) (fun p => b12 (snd p) = ab2 (fst p))) (fun p => fst (proj1_sig p)) (fun p => snd (proj1_sig p))). destruct uni as [ fa1 ? ? ].
   intros [ [ a2 b1 ] e ]. simpl in *. symmetry. assumption.
   intros [ a2 b1 ]. simpl. intro e. exists (fa1 (exist (fun p => b12 (snd p) = ab2 (fst p)) (pair a2 b1) e)); try trivial. f_equal.
    apply H.
    apply H0.
  apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply texistssubste. apply texistsproje with (fun a => a). apply tcompe. simpl. apply hmconje. apply hconji.
   eapply htrans; [ apply htopi | ]. eapply htrans; [ apply treflecttop | ]. apply treflectsubste. apply treflectleq. auto.
   apply tcompe. simpl. apply tcomp.
Qed.
Next Obligation.
 intros. split; intro le.
  apply texistsadj. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (f a) a).
   intros [ ? ? ]. simpl. intro. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tcompe. apply tidi. apply tide. assumption.
  apply texistsadj in le. apply himpir in le. apply htrans with (hconj (Pred T A) (treflect T A (fun _ => True)) pa).
   apply hconji; try apply hrefl. eapply htrans; try apply treflecttop. apply htopi.
   apply himpr. apply treflectopcart with (prod B A) (fun p => f (snd p) = fst p) snd.
    intros a _. exists (pair (f a) a); trivial.
    eapply htrans; [ apply hconji; [ apply hrefl | apply le ] | ]. clear le. apply himpr. apply treflectopcart with (sig (fun p : prod B A => f (snd p) = fst p)) (fun _ => True) (@proj1_sig (prod B A) (fun p => f (snd p) = fst p)).
     intros p e. exists (exist _ p e); trivial.
    apply hmimpe. apply himpir. apply hconje2. apply tcompe. apply hmimpe. apply hmimpi. apply himpm.
     apply tcomp.
     apply tcompi. apply tcompe. apply tsubsteq. intros [ ? ? ]. simpl. symmetry. assumption.
Qed.
Next Obligation. apply tholds. Qed.
Next Obligation.
 unfold SurjectiveSubstitutionsReflect. simpl. intros A B f pb pb' surj. intro. apply htrans with (hconj (Pred T B) (treflect T B (fun _ => True)) pb).
  apply hconji; try apply hrefl. eapply htrans; [ | apply treflecttop ]. apply htopi.
  apply himpr. apply treflectopcart with A (fun _ => True) f.
   intros b _. destruct surj with b as [ a ? ]. exists a; trivial.
   apply hmimpe. apply himpir. apply hconje2. assumption.
Qed.
Obligation Tactic := simpl; intros int T1 T2 F.
Next Obligation. apply mapleq. Qed.
Next Obligation. apply mapconj. Qed.
Next Obligation. apply mapimp. Qed.
Next Obligation. apply mapsubst. Qed.
Next Obligation.
 intros A B f pa. apply mapforalle. apply tforallm. apply mapimpe. apply himpm.
  apply mapreflect.
  apply mapsubst.
Qed.
Next Obligation. apply mapomega. Qed.
Obligation Tactic := unfold Equiv; simpl (Refines _); unfold SetTriposRefines; simpl; intro int.
Next Obligation. unfold TriposRefines. trivial. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.

Definition FuncProj2Sig_SET : Prop
:= forall A : SET, forall sa : A -> Prop, forall a : A, forall p p' : sa a, exist sa a p = exist sa a p' -> p = p'.

Definition UIP_SET : Prop
:= forall A : SET, forall a : A, forall e : a = a, e = eq_refl a.

Definition func_proj2_sig_uip_SET : FuncProj2Sig_SET -> UIP_SET
:= fun fp2s A a e
=> match e
         as e'
         in _ = a'
         return exist (eq a) a e = exist (eq a) a' e' -> e = eq_refl a
         with
   | eq_refl => fp2s A (eq a) a e (eq_refl a)
   end (eq_refl (exist (eq a) a e)).

Definition uip_func_proj2_sig_SET : UIP_SET -> FuncProj2Sig_SET
:= fun uip A sa a p p' e
=> match uip A a (match e in _ = s return a = match s with exist _ a' _ => a' end with eq_refl => eq_refl a end)
         in _ = ue
         return p = match ue in _ = a' return sa a' -> sa a with eq_refl => fun p' => p' end p'
         with
   | eq_refl => match e
                as e
                in _ = s
                return p = match match e
                                       in _ = s
                                       return a = match s with
                                                  | exist _ a' _ => a'
                                                  end
                                                  with
                                 | eq_refl => eq_refl
                                 end
                                 in _ = a'
                                 return sa a' -> sa a
                                 with
                           | eq_refl => fun p' => p'
                           end match s with exist _ a' p' => p' end
                with
          | eq_refl => eq_refl p
          end
  end.

(** ** PseudoFunctor *)

Program Definition set_tripos_to_tripos (uip : UIP_SET) (int : Prop) : Pseudofunctor (SurjSetTriposCategory int) (TriposCategory int)
:= pseudofunctor (SurjSetTriposCategory int)
                 (TriposCategory int)
                 (fun S => let S := proj1_sig S in tripos (sPred S) (@ssubst S) (fun A B => stforall S (prod A B) A fst) (fun A B => stexists S (prod A B) A fst) (fun A sa => stexists S (sig sa) A (@proj1_sig A sa) (htop (sPred S (sig sa)))) (sOmega S) (sholds S) (@schi S) _ _ _ _ _ _ _ _ _ _ _ _)
                 (fun S1 S2 F => tripos_morphism int _ _ (@sMap int S1 S2 F) _ _ _ _ _ _ _)
                 _ _ _.
Obligation Tactic := simpl; intros uip int [ S surjrefl ]; simpl.
Next Obligation. apply stid. Qed.
Next Obligation. apply stcomp. Qed.
Next Obligation.
 intros. apply stforallsubst. repeat split.
  intros [ a1 b ] [ a1' b' ]. simpl. intros ? e. inversion e. subst. reflexivity.
  intros X fa2 fb1 e. exists (fun x => pair (fa2 x) (snd (fb1 x))); try trivial. simpl. intro x. specialize (e x). destruct (fb1 x) as [ a2 b ]. simpl in *. subst. reflexivity.
Qed.
Next Obligation. intros. apply stforalladj. Qed.
Next Obligation.
 intros. apply stexistssubst. repeat split.
  intros [ a1 b ] [ a1' b' ]. simpl. intros ? e. inversion e. subst. reflexivity.
  intros X fa2 fb1 e. exists (fun x => pair (fa2 x) (snd (fb1 x))); try trivial. simpl. intro x. specialize (e x). destruct (fb1 x) as [ a2 b ]. simpl in *. subst. reflexivity.
Qed.
Next Obligation. intros. apply stexistsadj. Qed.
Next Obligation. intros A sa sa' conv. apply stexistsadj. eapply htrans; [ | apply stcomp ]. simpl. eapply htrans; [ | apply stcomp ]. simpl. change (fun a => @proj1_sig A sa a) with (fun a => @proj1_sig A sa' (exist sa' (proj1_sig a) (conv _ (proj2_sig a)))). eapply htrans; [ | apply stcomp ]. simpl. apply hmtopi with (f := ssubst S (fun a : sig sa => exist sa' (proj1_sig a) (conv _ (proj2_sig a)))). apply hmleq. apply stexistsadj. apply hrefl. Qed.
Next Obligation.
 intros. split.
  apply stexistsadj with (f := @proj1_sig A (fun a => sb (f a))). eapply htrans; [ | apply stcomp ]. change (fun a => f (proj1_sig a)) with (fun a => @proj1_sig B sb (exist sb (f (proj1_sig a)) (@proj2_sig A (fun a => sb (f a)) a))). eapply htrans; [ | apply stcomp ]. simpl. apply (hmtopi (ssubst S (fun a : sig (fun a => sb (f a)) => exist sb (f (proj1_sig a)) (proj2_sig a)))). apply hmleq. apply stexistsadj. apply hrefl.
  eapply htrans; [ apply (stexistssubst S (@proj1_sig A (fun a => sb (f a))) (@proj1_sig B sb) (fun a : sig (fun a => sb (f a)) => exist sb (f (proj1_sig a)) (proj2_sig a)) f) | ].
   repeat split.
    intros [ ? ? ] [ ? ? ]. simpl. intros ? e. subst. apply uip_func_proj2_sig_SET in e; try assumption. subst. reflexivity.
    intros X fa2 fb1 e. simple refine (ex_intro2 _ _ (fun x => exist (fun a => sb (f a)) (fa2 x) _) _ _); simpl; try trivial.
     rewrite (e x). destruct (fb1 x). trivial.
     intro x. rewrite e. destruct (fb1 x). reflexivity.
   apply stexistsadj. apply hmtopi. apply stexistsadj. apply hrefl.
Qed.
Next Obligation.
 intros A B sa f sb pb surj le. apply stexistsadj. apply (surjrefl (sig2 sa (fun a => sb (f a))) (sig sb) (fun a => exist sb (f (proj1_sig (sig_of_sig2 a))) (proj3_sig a))).
  intros [ b bsb ]. destruct surj with b as [ a ? asa ]; try assumption. subst. eexists (exist2 _ _ a asa bsb). simpl. reflexivity.
  apply hmtopi. eapply htrans; [ | apply stcomp ]. simpl. eapply htrans; [ | apply (stcomp S (@sig_of_sig2 A sa (fun a => sb (f a))) (fun a => f (proj1_sig a))) ]. simpl. apply (hmtopi (ssubst S (@sig_of_sig2 A sa (fun a => sb (f a))))). apply hmleq. eapply htrans; [ | apply stcomp ]. apply stexistsadj. assumption.
Qed.
Next Obligation.
 intro. apply htrans with (stexists S (sig (fun a : A => True)) A (@proj1_sig A (fun _ => True)) (carrier (ssubst S (@proj1_sig A (fun _ => True))) (htop (sPred S A)))).
  eapply htrans; [ | apply (stexistssubst S (@proj1_sig A (fun _ => True)) (fun a : A => a) _ (fun a : A => a)) ].
   apply stexistsadj. apply hrefl.
   repeat split.
    intros [ ? [] ] [ ? [] ]. simpl. intros. subst. reflexivity.
    intros. exists (fun x => exist (fun a => True) (fa2 x) I); auto.
  apply stexistsadj. apply hmtopi. apply stexistsadj. apply hrefl.
Qed.
Next Obligation.
 intros. apply himpr. apply stexistsadj. apply hmimpe. apply himpir. apply hconje2. eapply htrans; [ apply (stexistssubst S (fun a : sig (fun a => sa1 a /\ sa2 a) => exist sa1 (proj1_sig a) (let (p1, _) := proj2_sig a in p1)) (@proj1_sig A sa2) (fun a : sig (fun a => sa1 a /\ sa2 a) => exist sa2 (proj1_sig a) (let (_, p2) := proj2_sig a in p2)) (@proj1_sig A sa1)) | ].
  repeat split.
   intros [ ? [ ? ? ] ] [ ? [ ? ? ] ]. simpl. intros e1 e2. inversion e1. subst. apply uip_func_proj2_sig_SET in e1; try assumption. apply uip_func_proj2_sig_SET in e2; try assumption. subst. reflexivity.
   intros X fa2 fb1 e. simple refine (ex_intro2 _ _ (fun x => exist (fun a => sa1 a /\ sa2 a) (proj1_sig (fa2 x)) _) _ _); simpl.
    specialize (e x). destruct (fa2 x). simpl in *. split; try assumption. destruct (fb1 x). simpl in *. subst. assumption.
    intro. generalize (e x). intro. destruct (fa2 x). destruct (fb1 x). simpl. reflexivity.
    intro. generalize (e x). intro. destruct (fa2 x). destruct (fb1 x). simpl in *. destruct e0. reflexivity.
  apply (stexistsadj S (sig (fun a => sa1 a /\ sa2 a))). apply hmtopi. eapply htrans; [ | apply stcomp ]. simpl. apply stexistsadj. apply hrefl.
Qed.
Next Obligation. apply stholds. Qed.
Obligation Tactic := simpl; intros _ int [ S1 ? ] [ S2 ? ]; simpl; clear.
Next Obligation. apply smapleq. Qed.
Next Obligation. apply smapconj. Qed.
Next Obligation. apply smapimp. Qed.
Next Obligation. apply smapsubst. Qed.
Next Obligation. intros. apply smapforall. Qed.
Next Obligation.
 intros. split.
  eapply htrans; [ apply smapexists | ]. apply stexistsm. apply htopi.
  apply stexistsadj. eapply htrans; [ | apply smapsubst ]. eapply htrans; [ apply (smaptop F) | ]. apply smapleq. apply stexistsadj. apply hrefl.
Qed.
Next Obligation. apply smapomega. Qed.
Obligation Tactic := unfold Equiv; simpl (Refines _); unfold TriposRefines; simpl; intros _ int.
Next Obligation. unfold SetTriposRefines. trivial. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.
Next Obligation. intros. split; intros; apply hrefl. Qed.

Lemma stsubsteq (uip : UIP_SET) {S : SetTripos} (surjrefl : SurjectiveSubstitutionsReflect S) {A B : SET} (f g : A -> B) : (forall a : A, f a = g a) -> PHARefines (ssubst S f) (ssubst S g).
 apply (@tsubsteq (MapObject (set_tripos_to_tripos uip True) (exist _ S surjrefl))).
Qed.

(** ** Biadjoint biequivalence *)

Obligation Tactic := intros uip int; unfold PseudonaturalTransformationEquiv; unfold Equiv; simpl (Refines _); unfold TriposRefines; unfold SetTriposRefines; simpl; clear; try (auto; fail); try (intros; repeat split; intros; apply hrefl).
Program Definition tripos_set_tripos_equivalence (uip : UIP_SET) (int : Prop) : BiadjointBiequivalence (TriposCategory int) (SurjSetTriposCategory int)
:= biadjoint_biequivalence (TriposCategory int)
                           (SurjSetTriposCategory int)
                           (tripos_to_set_tripos int)
                           (set_tripos_to_tripos uip int)
                           (pseudonatural_transformation _ _ (fun T => tripos_morphism _ _ _ (fun A p => p) _ _ _ _ _ _ _) _)
                           (pseudonatural_transformation _ _ (fun T => tripos_morphism _ _ _ (fun A p => p) _ _ _ _ _ _ _) _)
                           (pseudonatural_transformation _ _ (fun S => set_tripos_morphism _ _ _ (fun A p => p) _ _ _ _ _ _) _)
                           (pseudonatural_transformation _ _ (fun S => set_tripos_morphism _ _ _ (fun A p => p) _ _ _ _ _ _) _)
                           _ _ _ _ _.
Next Obligation.
 intros T A B pab. apply tforalladj. apply tforallsubsti. apply tforallproji with (fun p => p). apply tcompi. simpl. apply hmimpi. apply himpapp.
  apply treflectsubste. simpl. eapply htrans; [ apply treflecttop | ]. apply treflectleq. reflexivity.
  apply tcompi. apply tid.
Qed.
Next Obligation.
 intros T A sa. split.
  apply treflectopcart with (sig sa) (fun _ => True) (@proj1_sig A sa).
   intros a s. exists (exist sa a s); trivial.
   apply texistssubste. apply texistsproje with (fun s => s). apply tcompe. simpl. apply hmconje. apply hconji.
    apply treflectsubste. simpl. apply treflectleq. reflexivity.
    apply tcompe. apply hmtope. apply htopi.
  apply texistsadj. apply hconje1. apply treflectsubste. apply treflectleq. intros [ a [ a' ? ] ]. simpl. intro. subst. assumption.
Qed.
Next Obligation.
 intro T. exists (fun p => p).
  split; apply tid.
  intros _. exists (fun p => p); reflexivity.
Qed.
Next Obligation.
 intros T A B pab. apply tforalladj. apply tforallsubsti. apply tforallproji with (fun t => snd (snd t)). apply tcompi. simpl. apply himpir. apply himpl. apply treflectopcart with (prod A B) (fun _ => True) (fun p => pair (fst p) p).
  intros [ ? ? ]. simpl. intro. subst. eauto.
  apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tsubsteq. intros [ ? ? ]. reflexivity.
Qed.
Next Obligation.
 intros T A sa. split.
  apply texistsadj. apply hconje1. apply treflectsubste. apply treflectleq. intros [ a [ a' ? ] ]. simpl. intro. subst. assumption.
  apply treflectopcart with (sig sa) (fun _ => True) (@proj1_sig A sa).
   intros a s. exists (exist sa a s); trivial.
   apply texistssubste. apply texistsproje with (fun s => s). apply tcompe. simpl. apply hmconje. apply hconji.
    apply treflectsubste. simpl. apply treflectleq. reflexivity.
    apply tcompe. apply hmtope. apply htopi.
Qed.
Next Obligation.
 intro T. exists (fun p => p).
  split; apply tid.
  intros _. exists (fun p => p); reflexivity.
Qed.
Obligation Tactic := intros uip int; unfold Equiv; simpl (Refines _); unfold TriposRefines; unfold SetTriposRefines; simpl; intros [ S ? ]; simpl; clear; try (auto; fail); try (intros; repeat split; intros; apply hrefl).
Next Obligation.
 intros A B f pa. apply stforalladj. apply stforallsubstproji with (fun a => pair (f a) a); try reflexivity. apply hmimpi. apply himpapp.
  apply stexistssubstproje with (fun a => exist (fun p => f (snd p) = fst p) (pair (f a) a) (eq_refl (f a))); try reflexivity. apply hmtope. apply htopi.
  eapply htrans; [ apply stcomp | ]. simpl. apply stid.
Qed.
Next Obligation.
 exists (fun p => p).
  split; apply stid.
  intros _. exists (fun p => p); reflexivity.
Qed.
Obligation Tactic := intros uip int; unfold Equiv; simpl (Refines _); unfold TriposRefines; unfold SetTriposRefines; simpl; intros [ S ? ]; simpl; try (auto; fail); try (intros; repeat split; intros; apply hrefl).
Next Obligation.
 intros A B f pa. apply stforalladj. apply himpir. apply himpl. apply stexistsadj. apply hmimpe. apply himpir. apply hconje2. eapply htrans; [ apply (stcomp S _ fst) | ]. eapply htrans; [ | apply stcomp ]. apply htrans with (carrier (ssubst S (fun p => f (snd (proj1_sig p)))) (stforall S A B f pa)).
  apply stsubsteq; try assumption. intros [ [ ? ? ] ? ]. simpl in *. subst. reflexivity.
  eapply htrans; [ apply stcomp | ]. simpl. apply hmleq. apply stforalladj. apply hrefl.
Qed.
Obligation Tactic := intros uip int; unfold Equiv; simpl (Refines _); unfold TriposRefines; unfold SetTriposRefines; simpl; intros [ S ? ]; simpl; clear; try (auto; fail); try (intros; repeat split; intros; apply hrefl).
Next Obligation.
 exists (fun p => p).
  split; apply stid.
  intros _. exists (fun p => p); reflexivity.
Qed.
Obligation Tactic := intros uip int; unfold PseudonaturalTransformationEquiv; unfold Equiv; simpl (Refines _); unfold TriposRefines; unfold SetTriposRefines; simpl; clear; try (auto; fail); try (intros; repeat split; intros; apply hrefl).
Solve Obligations.
