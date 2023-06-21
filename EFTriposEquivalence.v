Require Import Program.
Require Import EF.Categories.
Require Import EF.Triposes.
Require Import EF.EvidencedFrames.

Obligation Tactic := idtac.

(**  * UFam : from Evidenced Frames to Triposes *)

(** ** Definition *)

Program Definition UFamPHA (E : EvidencedFrame) (A : SET) : PreHeytingAlgebra
  := preheyting_algebra (A -> PROP E)
                        (fun p p' => exists e : Evidence E, forall a : A, Evidences E (p a) e (p' a))
                        (fun a => etop E)
                        (fun p1 p2 a => econj E (p1 a) (p2 a))
                        (fun a => ebot E)
                        (fun p1 p2 a => edisj E (p1 a) (p2 a))
                        (fun pi po a => eimp E (pi a) (po a))
                        _ _ _ _ _ _ _ _ _ _ _ _.
Obligation Tactic := intros E A.
Next Obligation. intro p. destruct (eaxiom E). eauto. Qed.
Next Obligation. intros p1 p2 p3 [ ? ? ] [ ? ? ]. destruct (ecut E). eauto. Qed.
Next Obligation. intro p. destruct (etopi E). eauto. Qed.
Next Obligation. intros p p1 p2 [ ? ? ] [ ? ? ]. destruct (econji E). eauto. Qed.
Next Obligation. intros p1 p2. destruct (econje1 E). eauto. Qed.
Next Obligation. intros p1 p2. destruct (econje2 E). eauto. Qed.
Next Obligation. intro p. destruct (ebote E). eauto. Qed.
Next Obligation. intros p1 p2. destruct (edisji1 E). eauto. Qed.
Next Obligation. intros p1 p2. destruct (edisji2 E). eauto. Qed.
Next Obligation. intros p1 p2 p' [ ? ? ] [ ? ? ]. destruct (edisje E). eauto. Qed.
Next Obligation. intros p pi po [ ? ? ]. destruct (eimpi E). eauto. Qed.
Next Obligation. intros pi po. destruct (eimpe E). eauto. Qed.

Program Definition UFam (E : EvidencedFrame) : Tripos
  := tripos (UFamPHA E)
            (fun A B f => pha_morphism (UFamPHA E B) (UFamPHA E A) (fun p => fun a => p (f a)) _ _ _ _ _ _)
            (fun A B pab => fun a => emeet E (fun p => exists b : B, pab (pair a b) = p))
            (fun A B pab => fun a => ejoin E (fun p => exists b : B, pab (pair a b) = p))
            (fun A sa => fun a => ejoin E (fun p => sa a /\ etop E = p))
            (PROP E)
            (fun p => p)
            (fun A p => p) _ _ _ _ _ _ _ _ _ _ _ _.
Obligation Tactic := intro E; unfold PHARefines; simpl.
Next Obligation. intros A B f p p' [ ? ? ]. eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation.
 intros. split; intros [ ? e ].
  destruct (emeeti E) as [ emi emeeti ]. eexists. intro. apply emeeti. intros p' [ ? ? ]. subst. apply (e (pair a _)).
  destruct (emeete E) as [ eme emeete ]. destruct (ecut E) as [ ec ecut ]. eexists. intros [ a b ]. eapply ecut; [ apply e | ]. apply emeete. eauto.
Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation.
 split; intros [ ? e ].
  destruct (ejoine E) as [ eje ejoine ]. eexists. intro. apply ejoine. intros p' [ ? ? ]. subst. apply (e (pair a _)).
  destruct (ejoini E) as [ eji ejoini ]. destruct (ecut E) as [ ec ecut ]. eexists. intros [ a b ]. eapply ecut; [ | apply e ]. apply ejoini. eauto.
Qed.
Next Obligation. intros. destruct (ejoini E) as [ eji ejoini ]. destruct (ejoine E) as [ eje ejoine ]. destruct (ecut E) as [ ec ecut ]. eexists. intros. apply ejoine. intros ? [ ? ? ]. apply ejoini. auto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.
Next Obligation. intros A B sa f sb pb surj [ ? e ]. destruct (ejoini E) as [ eji ejoini ]. destruct (ejoine E) as [ eje ejoine ]. destruct (ecut E) as [ ec ecut ]. eexists. intros. apply ejoine. intros b [ sbb ? ]. apply surj in sbb. destruct sbb as [ ? ? ]. subst. eapply ecut; [ | apply e ]. apply ejoini. auto. Qed.
Next Obligation. intros. destruct (ejoini E) as [ eji ejoini ]. eexists. intros _. apply ejoini. auto. Qed.
Next Obligation. intros. destruct (ejoini E) as [ eji ejoini ]. destruct (ejoine E) as [ eje ejoine ]. destruct (ecut E) as [ ec ecut ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. destruct (econji E) as [ eci econji ]. destruct (econje1 E) as [ ece1 econje1 ]. destruct (econje2 E) as [ ece2 econje2 ]. eexists. intros. eapply ecut; [ | apply eimpe ]. apply econji; [ apply econje2 | ]. eapply ecut; [ apply econje1 | ]. apply ejoine. intros ? [ ? ? ]. subst. apply eimpi. eapply ecut; [ apply econje2 | ]. apply ejoine. intros ? [ ? ? ]. apply ejoini. auto. Qed.
Next Obligation. destruct (eaxiom E). eauto. Qed.


(** ** Functoriality of UFam *)

Program Definition UFamMorphism (int : Prop) (E1 E2 : EvidencedFrame) (F : EvidencedFrameMorphism int E1 E2) : TriposMorphism int (UFam E1) (UFam E2)
:= tripos_morphism int (UFam E1) (UFam E2) (fun A f a => Convert F (f a)) _ _ _ _ _ _ _.
Obligation Tactic := intros int E1 E2 F; simpl.
Next Obligation. intros A pa1 pa1' [ e1 ? ]. destruct (conevidence F e1) as [ e2 conevidence ]. exists e2. auto. Qed.
Next Obligation. intros. destruct (conconj F) as [ cc conconj ]. exists cc. auto. Qed.
Next Obligation. intros. destruct (conimp F) as [ ci conimp ]. exists ci. auto. Qed.
Next Obligation. intros. destruct (eaxiom E2) as [ ea2 eaxiom2 ]. split; exists ea2; auto. Qed.
Next Obligation. intros. destruct (conmeet F) as [ cm conmeet ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (emeeti E2) as [ emi2 emeeti2 ]. destruct (emeete E2) as [ eme2 emeete2 ]. eexists. intro. eapply ecut2; [ | apply conmeet ]. apply emeeti2. intros ? [ ? [ ? ? ] ? ]. subst. apply emeete2. eauto. Qed.
Next Obligation.
 intros. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (etopi E2) as [ eti2 etopi2 ]. destruct (ejoini E2) as [ eji2 ejoini2 ]. destruct (ejoine E2) as [ eje2 ejoine2 ]. split.
  destruct (conjoin F) as [ cj conjoin ]. eexists. intro. eapply ecut2; [ apply conjoin | ]. apply ejoine2. intros ? [ ? [ ? ? ] ? ]. subst. eapply ecut2; [ apply etopi2 | ]. apply ejoini2. auto.
  destruct (contop F) as [ ct contop ]. destruct (ejoini E1) as [ eji1 ejoini1 ]. edestruct (conevidence F) as [ ce' conevidence' ]. eexists. intro. apply ejoine2. intros ? [ ? ? ]. subst. eapply ecut2; [ apply contop | ]. apply conevidence'. apply ejoini1. auto.
Qed.
Next Obligation.
 destruct (conprop F) as [ f [ e2 [ e2' ef ] ] ? ]. exists f.
  split.
   exists e2. apply ef.
   exists e2'. apply ef.
  assumption.
Qed.

Program Definition UFamFunctor (int : Prop) : Pseudofunctor (EvidencedFrameCategory int) (TriposCategory int)
:= pseudofunctor (EvidencedFrameCategory int) (TriposCategory int) UFam (@UFamMorphism int) _ _ _.
Obligation Tactic := intro int; unfold Equiv; simpl (Refines _); unfold TriposRefines; simpl.
Next Obligation. intros E1 E2 F G ref A pa. destruct ref. eauto. Qed.
Next Obligation. intro E. destruct (eaxiom E). eauto. Qed.
Next Obligation. intros E1 E2 E3 F G. destruct (eaxiom E3). eauto. Qed.




(** * RAS: from Triposes to Evidenced Frames *)

(** ** Definition *)

Definition ReflectedAxiomSchema (T : Tripos) (R : Omega T -> Omega T -> Prop) : Prop
:= LEq (Pred T (prod (Omega T) (Omega T))) (hconj (Pred T (prod (Omega T) (Omega T))) (treflect T (prod (Omega T) (Omega T)) (fun p => R (fst p) (snd p))) (carrier (subst T fst) (holds T))) (carrier (subst T snd) (holds T)).

Program Definition RAS (T : Tripos) : EvidencedFrame
:= evidenced_frame (Omega T) (sig (ReflectedAxiomSchema T)) (fun p1 e p2 => proj1_sig e p1 p2) (ttop T) (tconj T) (fun p pi => timp T p (tmeet T pi)) _ _ _ _ _ _ _ _.
Obligation Tactic := intro T.
Next Obligation.
 simple refine (ex_intro _ (exist _ (@eq (Omega T)) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (Omega T) (fun p => True) (fun p => pair p p)).
   intros [ p1 p2 ] e. simpl in e. destruct e. exists p1; trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
  simpl. reflexivity.
Qed.
Next Obligation.
 simple refine (ex_intro _ (fun r12 r23 => exist _ (fun p1 p3 => exists2 p2, proj1_sig r12 p1 p2 & proj1_sig r23 p2 p3) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (prod (Omega T) (prod (Omega T) (Omega T))) (fun t => proj1_sig r12 (fst (snd t)) (fst t) /\ proj1_sig r23 (fst t) (snd (snd t))) snd).
   intros [ p1 p3 ] e. simpl in e. destruct e as [ p2 ? ? ]. exists (pair p2 (pair p1 p3)); auto.
   apply hmimpe. apply himpir. destruct r23 as [ r23 ias23 ]. simpl. unfold ReflectedAxiomSchema in ias23. apply (hmleq (subst T (fun (t : prod (Omega T) (prod (Omega T) (Omega T))) => pair (fst t) (snd (snd t))))) in ias23. apply tcompe in ias23. apply tcompe. eapply htrans; [ | apply ias23 ]. clear ias23. apply hmconje. apply hconji.
    apply hconje1. apply treflectsubste. apply treflectleq. intros [ p1 [ p2 p3 ] ]. simpl. intros [ _ ? ]. assumption.
    destruct r12 as [ r12 ias12 ]. simpl. apply (hmleq (subst T (fun (t : prod (Omega T) (prod (Omega T) (Omega T))) => pair (fst (snd t)) (fst t)))) in ias12. apply tcompe in ias12. apply tcompe. eapply htrans; [ | apply ias12 ]. clear ias12. apply hmconje. apply hconjm.
     apply treflectsubste. apply treflectleq. intros [ p1 [ p2 p3 ] ]. simpl. intros [ ? _ ]. assumption.
     apply tcompi. apply tcompe. simpl. apply hrefl.
  simpl. intros. exists p2; assumption.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p pt => ttop T = pt) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (Omega T) (fun p => True) (fun p => pair p (ttop T))).
   intros [ p pt ] e. simpl in e. destruct e. exists p; trivial.
   apply hmimpe. apply himpir. apply tcompe. simpl. apply tholdssubste. apply hmtope. apply htopi.
  simpl. reflexivity.
Qed.
Next Obligation.
 simple refine (ex_intro _ (fun r1 r2 => exist _ (fun p p' => exists2 p1, proj1_sig r1 p p1 & exists2 p2, proj1_sig r2 p p2 & tconj T p1 p2 = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (prod (Omega T) (prod (Omega T) (Omega T))) (fun t => proj1_sig r1 (fst t) (fst (snd t)) /\ proj1_sig r2 (fst t) (snd (snd t))) (fun t => pair (fst t) (tconj T (fst (snd t)) (snd (snd t))))).
   intros [ p p' ] e. simpl in e. destruct e as [ p1 ? [ p2 ? ? ] ]. subst. exists (pair p (pair p1 p2)); auto.
   apply hmimpe. apply himpir. apply tcompe. simpl. apply tholdssubste. apply hmconje. apply hconji.
    apply tcompe. simpl. destruct r1 as [ r1 ias1 ]. unfold ReflectedAxiomSchema in ias1. simpl. apply (hmleq (subst T (fun t : (prod (Omega T) (prod (Omega T) (Omega T))) => pair (fst t) (fst (snd t))))) in ias1. apply tcompe in ias1. simpl in ias1. eapply htrans; [ | apply ias1 ]. clear ias1. apply hmconje. apply hconjm.
     apply treflectsubste. apply treflectleq. intros [ p1 [ p2 p3 ] ]. simpl. intros [ ? _ ]. assumption.
     apply tcompi. apply tcompe. simpl. apply hrefl.
    apply tcompe. simpl. destruct r2 as [ r2 ias2 ]. unfold ReflectedAxiomSchema in ias2. simpl. apply (hmleq (subst T (fun t : (prod (Omega T) (prod (Omega T) (Omega T))) => pair (fst t) (snd (snd t))))) in ias2. apply tcompe in ias2. simpl in ias2. eapply htrans; [ | apply ias2 ]. clear ias2. apply hmconje. apply hconjm.
     apply treflectsubste. apply treflectleq. intros [ p1 [ p2 p3 ] ]. simpl. intros [ _ ? ]. assumption.
     apply tcompi. apply tcompe. simpl. apply hrefl.
  simpl. eauto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p p1 => exists p2, tconj T p1 p2 = p) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (prod (Omega T) (Omega T)) (fun _ => True) (fun p => pair (tconj T (fst p) (snd p)) (fst p))).
   intros [ p p1 ]. simpl. intros [ p2 ? ]. subst. exists (pair p1 p2); trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply hmconji. apply hconje1. apply tcompi. apply hrefl.
  simpl. eauto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p p2 => exists p1, tconj T p1 p2 = p) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (prod (Omega T) (Omega T)) (fun _ => True) (fun p => pair (tconj T (fst p) (snd p)) (snd p))).
   intros [ p p2 ]. simpl. intros [ p1 ? ]. subst. exists (pair p1 p2); trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply hmconji. apply hconje2. apply tcompi. apply hrefl.
  simpl. eauto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (fun r : sig (ReflectedAxiomSchema T) => exist _ (fun p p' => exists p1 : Omega T, exists2 pi : Omega T -> Prop, forall p2, pi p2 -> proj1_sig r (tconj T p p1) p2 & timp T p1 (tmeet T pi) = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (prod (Omega T) (prod (Omega T) (Omega T -> Prop))) (fun t => forall p2 : Omega T, (snd (snd t)) p2 -> proj1_sig r (tconj T (fst t) (fst (snd t))) p2) (fun t => pair (fst t) (timp T (fst (snd t)) (tmeet T (snd (snd t)))))).
   intros [ p p' ] e. simpl in e. destruct e as [ p1 [ pi ? ? ] ]. subst. exists (pair p (pair p1 pi)); trivial.
   apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. simpl. apply himpil. unfold timp. apply tholdssubste. apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. simpl. apply himpil. unfold tmeet. apply tholdssubste. apply tforallsubste. apply tforalladj. apply hmconji. apply himpl. apply tcompi. apply himpil. apply himpr. apply hmconji. apply himpl. apply tcompi. apply himpil. apply himpr. apply treflectsubsti. apply himpir. apply himpir. apply hmimpe. apply himpir. apply himpl. apply treflectsubsti. apply himpil. apply tcompe. simpl. apply himpr. apply hconjassoc. apply hconjsym. apply himpir. apply hconjassoc. apply himpl. apply htrans with (treflect T (prod (prod (Omega T) (prod (Omega T) (Omega T -> Prop))) (Omega T)) (fun t => proj1_sig r (tconj T (fst (fst t)) (fst (snd (fst t)))) (snd t))).
    apply treflectconji. apply treflectleq. intros [ [ p1 [ p2 pi ] ] p' ]. simpl. intros [ ? ? ]. auto.
    destruct r as [ r ias ]. unfold ReflectedAxiomSchema in ias. simpl. apply (hmleq (subst T (fun t : prod (prod (Omega T) (prod (Omega T) (Omega T -> Prop))) (Omega T) => pair (tconj T (fst (fst t)) (fst (snd (fst t)))) (snd t)))) in ias. apply tcompe in ias. apply hmconji in ias. apply himpil in ias. apply tcompi in ias. apply himpl in ias. apply himpir in ias. apply treflectsubsti in ias. simpl in ias. eapply htrans; [ apply ias | ]. clear ias. apply himpm; try apply hrefl. unfold tconj. apply tholdssubste. apply hmconje. apply hconji.
     apply tcompe. apply hconjp1.
     apply tcompe. apply hconjp2.
  simpl. eauto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p p' => exists p1, exists2 pi : Omega T -> Prop, tconj T p1 (timp T p1 (tmeet T pi)) = p & pi p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (prod (prod (Omega T) (Omega T -> Prop)) (Omega T)) (fun t => (snd (fst t)) (snd t)) (fun t => pair (tconj T (fst (fst t)) (timp T (fst (fst t)) (tmeet T (snd (fst t))))) (snd t))).
   intros [ p p' ] e. simpl in e. destruct e as [ p1 [ pi ? ? ] ]. subst. exists (pair (pair p1 pi) p'); trivial.
   apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. simpl. apply tholdssubsti. apply hmconji. apply himpl. apply tcompi. apply tholdssubsti. apply hmimpi. simpl. apply himpm.
    apply tcompi. apply tcompe. apply hrefl.
    apply tcompi. simpl. apply tholdssubsti. apply tforallsubsti. apply (tforallproji snd). apply tcompi. simpl. apply hmimpi. apply himpm.
     apply treflectsubste. apply hrefl.
     apply tcompi. apply hrefl.
  simpl. eauto.
Qed.


(** ** Functoriality of RAS *)


Program Definition RASMorphism (int : Prop) (T1 T2 : Tripos) (F : TriposMorphism int T1 T2) : EvidencedFrameMorphism int (RAS T1) (RAS T2)
:= evidenced_frame_morphism int (RAS T1) (RAS T2) (chi T2 (Map F (holds T1))) _ _ _ _ _.
Obligation Tactic := intros int T1 T2 F; simpl.
Next Obligation.
 intros [ r ias ]. simpl. simple refine (ex_intro _ (exist _ (fun p2 p2' => exists2 p1, chi T2 (Map F (holds T1)) p1 = p2 & exists2 p1', chi T2 (Map F (holds T1)) p1' = p2' & r p1 p1') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (prod (Omega T1) (Omega T1)) (fun p => r (fst p) (snd p)) (fun p => pair (chi T2 (Map F (holds T1)) (fst p)) (chi T2 (Map F (holds T1)) (snd p))).
   intros [ ? ? ]. simpl. intros [ p1 ? [ p1' ? ? ] ]. subst. exists (pair p1 p1'); trivial.
   apply himpir in ias. eapply htrans; [ apply (mapreflect F) | ]. apply (mapleq F) in ias. eapply htrans; [ apply ias | clear ias ]. apply hmimpe. apply himpir. apply tcompe. simpl. apply tholdssubste. apply mapsubste. apply himpl. apply tcompi. simpl. apply tholdssubsti. apply mapsubsti. apply himpir. apply himpl. apply mapimpi. apply hrefl.
  simpl. eauto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p2 p2' => ttop T2 = p2 /\ chi T2 (Map F (holds T1)) (ttop T1) = p2') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with unit (fun _ => True) (fun _ => pair (ttop T2) (chi T2 (Map F (holds T1)) (ttop T1))).
   intros [ ? ? ]. simpl. intros [ ? ? ]. subst. exists tt; trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tholdssubsti. apply hmtopi. apply mapsubste. apply (maptopi F). apply mapleq. apply tholdssubste. apply hmtop.
  simpl. auto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p2 p2' => exists p1, exists2 p1', tconj T2 (chi T2 (Map F (holds T1)) p1) (chi T2 (Map F (holds T1)) p1') = p2 & chi T2 (Map F (holds T1)) (tconj T1 p1 p1') = p2') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (prod (Omega T1) (Omega T1)) (fun _ => True) (fun p => pair (tconj T2 (chi T2 (Map F (holds T1)) (fst p)) (chi T2 (Map F (holds T1)) (snd p))) (chi T2 (Map F (holds T1)) (tconj T1 (fst p) (snd p)))).
   intros [ ? ? ]. simpl. intros [ p1 [ p1' ? ? ] ]. subst. exists (pair p1 p1'); trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. eapply htrans.
    apply hmconji. apply hconjm.
     apply tcompi. simpl. apply tholdssubsti. apply mapsubst.
     apply tcompi. simpl. apply tholdssubsti. apply mapsubst.
    apply mapconji. apply mapsubste. apply mapleq. apply tholdssubste. apply hmconje. apply hconjm.
     apply tcompe. simpl. apply tcompe. apply tid.
     apply tcompe. simpl. apply tcompe. apply tid.
  simpl. eauto.
Qed.
Next Obligation.
 simple refine (ex_intro _ (exist _ (fun p2 p2' => exists p1, exists2 s1, timp T2 (chi T2 (Map F (holds T1)) p1) (tmeet T2 (fun p2' => exists2 p1', s1 p1' & chi T2 (Map F (holds T1)) p1' = p2')) = p2 & chi T2 (Map F (holds T1)) (timp T1 p1 (tmeet T1 s1)) = p2') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (prod (Omega T1) (Omega T1 -> Prop)) (fun _ => True) (fun p => pair (timp T2 (chi T2 (Map F (holds T1)) (fst p)) (tmeet T2 (fun p2' => exists2 p1', (snd p) p1' & chi T2 (Map F (holds T1)) p1' = p2'))) (chi T2 (Map F (holds T1)) (timp T1 (fst p) (tmeet T1 (snd p))))).
   intros [ ? ? ]. simpl. intros [ p1 [ s1 ? ? ] ]. subst. exists (pair p1 s1); trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply mapsubste. eapply htrans; [ | apply mapleq ].
    apply hmimpi. apply mapimpe. apply himpm.
     apply tcompe. simpl. apply tholdssubste. apply mapsubst.
     apply tcompi. simpl. apply tholdssubsti. apply tforallsubsti. apply mapforalle. apply tforalladj. apply tforallsubsti. apply tforallproji with (fun p => chi T2 (Map F (holds T1)) (snd p)). apply tcompi. simpl. apply tcompi. simpl. apply hmimpi. apply mapimpe. apply himpm.
      apply treflectsubste. simpl. apply (mapreflect F).
      apply tcompi. simpl. apply tholdssubsti. apply mapsubst.
    apply tholdssubste. apply hmimpe. apply himpm.
     apply tcompi. simpl. apply tcompi. apply tid.
     apply tcompe. simpl. apply tmeeti. apply himpir. apply himpl. apply tforallsubsti. apply tforallproji with snd. apply tcompi. simpl. apply hmimpi. apply himpm.
      apply treflectsubste. apply treflectleq. intros [ [ p1 s1 ] p1' ] ?. simpl. exists p1'; trivial.
      apply tcompi. simpl. apply tcompi. apply tid.
  simpl. eauto.
Qed.
Next Obligation.
 destruct (mapomega F) as [ f mapomega mapint ]. exists f.
  simple refine (ex_intro _ (exist _ (fun p2 p2' => chi T2 (Map F (holds T1)) (f p2) = p2') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T2) (fun _ => True) (fun p2 => pair p2 (chi T2 (Map F (holds T1)) (f p2))).
    intros [ p2 ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tidi. apply mapomega.
   simpl. simple refine (ex_intro _ (exist _ (fun p2 p2' => chi T2 (Map F (holds T1)) (f p2') = p2) _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T2) (fun _ => True) (fun p2 => pair (chi T2 (Map F (holds T1)) (f p2)) p2).
     intros [ p2 ? ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tide. apply mapomega.
    simpl. auto.
  assumption.
Qed.

Program Definition RASFunctor (int : Prop) : Pseudofunctor (TriposCategory int) (EvidencedFrameCategory int)
:= pseudofunctor (TriposCategory int) (EvidencedFrameCategory int) RAS (@RASMorphism int) _ _ _.
Obligation Tactic := intro int; unfold Equiv; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
Next Obligation.
 intros T1 T2 F G ref. simple refine (ex_intro _ (exist _ (fun p2 p2' => exists2 p1, chi T2 (Map F (holds T1)) p1 = p2 & chi T2 (Map G (holds T1)) p1 = p2') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T1) (fun _ => True) (fun p1 => pair (chi T2 (Map F (holds T1)) p1) (chi T2 (Map G (holds T1)) p1)).
   intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tidi. apply tide. apply ref.
  simpl. eauto.
Qed.
Next Obligation.
 intro T. split.
  simple refine (ex_intro _ (exist _ (fun p p' => chi T (holds T) p = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T) (fun _ => True) (fun p => pair p (chi T (holds T) p)).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubst.
   simpl. auto.
  simple refine (ex_intro _ (exist _ (fun p p' => chi T (holds T) p' = p) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T) (fun _ => True) (fun p => pair (chi T (holds T) p) p).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubst.
   simpl. auto.
Qed.
Next Obligation.
 intros T1 T2 T3 F G. split.
  simple refine (ex_intro _ (exist _ (fun p3 p3' => exists2 p1, chi T3 (Map G (holds T2)) (chi T2 (Map F (holds T1)) p1) = p3 & chi T3 (Map G (Map F (holds T1))) p1 = p3') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T1) (fun _ => True) (fun p1 => pair (chi T3 (Map G (holds T2)) (chi T2 (Map F (holds T1)) p1)) (chi T3 (Map G (Map F (holds T1))) p1)).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tide. apply mapsubsti. apply mapleq. apply tholdssubsti. apply tid.
   simpl. eauto.
  simple refine (ex_intro _ (exist _ (fun p3 p3' => exists2 p1, chi T3 (Map G (Map F (holds T1))) p1 = p3 & chi T3 (Map G (holds T2)) (chi T2 (Map F (holds T1)) p1) = p3') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T1) (fun _ => True) (fun p1 => pair (chi T3 (Map G (Map F (holds T1))) p1) (chi T3 (Map G (holds T2)) (chi T2 (Map F (holds T1)) p1))).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tidi. apply mapsubste. apply mapleq. apply tholdssubste. apply tid.
   simpl. eauto.
Qed.





(** *  UFam <-> RAS Units/Counits *)

(** ** Natural Transformation:  Id => UFam ∘ RAS *)

Program Definition tripos_to_ras_ufam (int : Prop) : PseudonaturalTransformation (cat_id (TriposCategory int)) (cat_comp (RASFunctor int) (UFamFunctor int))
:= pseudonatural_transformation (cat_id (TriposCategory int)) (cat_comp (RASFunctor int) (UFamFunctor int)) (fun T => tripos_morphism int T (UFam (RAS T)) (@chi T) _ _ _ _ _ _ _) _.
Obligation Tactic := intro int; unfold Equiv; simpl (Refines _); unfold TriposRefines; simpl.
Next Obligation.
 intros. simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, chi T pa a = p & chi T pa' a = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T A (fun a => True) (fun a => pair (chi T pa a) (chi T pa' a))).
   intros [ p p' ]. simpl. intros [ ? ? ? ]. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tidi. apply tide. assumption.
  simpl. eauto.
Qed.
Next Obligation.
 intros. simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, tconj T (chi T pa1 a) (chi T pa2 a) = p & chi T (hconj (Pred T A) pa1 pa2) a = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T A (fun a => True) (fun a => pair (tconj T (chi T pa1 a) (chi T pa2 a)) (chi T (hconj (Pred T A) pa1 pa2) a))).
   intros [ p p' ]. simpl. intros [ ? ? ? ]. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tide. apply tholdssubsti. apply hmconji. apply hconjm.
    apply tcompi. simpl. apply tholdssubsti. apply tid.
    apply tcompi. simpl. apply tholdssubsti. apply tid.
  simpl. eauto.
Qed.
Next Obligation.
 intros. simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, timp T (chi T pai a) (tmeet T (eq (chi T pao a))) = p & chi T (himp (Pred T A) pai pao) a = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T A (fun a => True) (fun a => pair (timp T (chi T pai a) (tmeet T (eq (chi T pao a)))) (chi T (himp (Pred T A) pai pao) a))).
   intros [ p p' ]. simpl. intros [ ? ? ? ]. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tide. apply tholdssubsti. apply hmimpi. apply himpm.
    apply tcompe. simpl. apply tholdssubste. apply tid.
    apply tcompi. simpl. apply tholdssubsti. apply tforallsubsti. apply tforallproji with (chi T pao). apply tcompi. simpl. apply hmimpi. eapply htrans; [ | apply himppr ]. apply hconji; [ | apply himpm; [ apply treflectsubst | apply tcompi; apply tholdssubsti; apply tid ] ]. eapply htrans; [ apply htopi | ]. eapply htrans; [ apply treflecttop | ]. apply treflectleq. reflexivity.
  simpl. eauto.
Qed.
Next Obligation.
 intros. split.
  simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, chi T pb (f a) = p & chi T (carrier (subst T f) pb) a = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (chi T pb (f a)) (chi T (carrier (subst T f) pb) a)).
    intros [ ? ? ]. simpl. intros [ a ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tid.
   simpl. eauto.
  simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, chi T (carrier (subst T f) pb) a = p & chi T pb (f a) = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (chi T (carrier (subst T f) pb) a) (chi T pb (f a))).
    intros [ ? ? ]. simpl. intros [ a ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tid.
   simpl. eauto.
Qed.
Next Obligation.
 intros. simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, timp T (ttop T) (tmeet T (fun p => exists b, chi T pab (pair a b) = p)) = p & chi T (tforall T A B pab) a = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (timp T (ttop T) (tmeet T (fun p => exists b, chi T pab (pair a b) = p))) (chi T (tforall T A B pab) a)).
   intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tide. apply tholdssubsti. apply hmimpi. apply himpapp.
    apply tcompe. simpl. apply tholdssubste. apply hmtop.
    apply tcompi. simpl. apply tforalladj. apply tcompi. simpl. apply tmeete with (chi T pab).
     intros [ ? ? ]. eauto.
     apply tholdssubsti. apply tid.
  simpl. eauto.
Qed.
Next Obligation.
 split.
  simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, chi T (treflect T A sa) a = p & timp T (ttop T) (tmeet T (fun p => exists p', timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa a /\ ttop T = p''' & timp T p''' (tmeet T (eq p')) = p''))) (tmeet T (eq p')) = p)) = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. eapply treflectopcart with A (fun _ => True) (fun a => pair (chi T (treflect T A sa) a) (timp T (ttop T) (tmeet T (fun p => exists p', timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa a /\ ttop T = p''' & timp T p''' (tmeet T (eq p')) = p''))) (tmeet T (eq p')) = p)))).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tidi. apply tholdssubste. apply hmimpe. apply himpir. apply hconje1. apply tcompe. simpl. apply tmeeti. apply treflectopcart with (prod A (Omega T)) (fun p => True) (fun p => pair (fst p) (timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa (fst p) /\ ttop T = p''' & timp T p''' (tmeet T (eq (snd p))) = p''))) (tmeet T (eq (snd p))))).
     intros [ a ? ]. simpl. intros [ p ? ]. subst. exists (pair a p); trivial.
      apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. simpl. apply tholdssubsti. apply hmimpi. apply himpapp.
       apply tcompe. simpl. apply tholdssubste. apply hmtop.
       apply tcompi. simpl. apply himpir. apply himpl. apply treflectsubsti. apply himpil. apply tmeetreflecte with (fun p => timp T (ttop T) (tmeet T (eq (snd p)))).
        intros [ ? ? ] ?. eauto.
        apply tholdssubsti. apply hmimpi. apply himpapp.
         apply tcompe. apply tholdssubste. apply hmtop.
         apply tcompi. simpl. apply hrefl.
   simpl. eauto.
  simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, timp T (ttop T) (tmeet T (fun p => exists p', timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa a /\ ttop T = p''' & timp T p''' (tmeet T (eq p')) = p''))) (tmeet T (eq p')) = p)) = p & chi T (treflect T A sa) a = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. eapply treflectopcart with A (fun _ => True) (fun a => pair (timp T (ttop T) (tmeet T (fun p => exists p', timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa a /\ ttop T = p''' & timp T p''' (tmeet T (eq p')) = p''))) (tmeet T (eq p')) = p))) (chi T (treflect T A sa) a)).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tide. apply tholdssubsti. apply hmimpi. apply himpapp.
     apply tcompe. apply tholdssubste. apply hmtop.
     apply tcompi. simpl. apply tmeete with (fun a => timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa a /\ ttop T = p''' & timp T p''' (tmeet T (eq (chi T (treflect T A sa) a))) = p''))) (tmeet T (eq (chi T (treflect T A sa) a)))).
      eauto.
      apply tholdssubsti. apply hmimpi. apply himpapp.
       apply tcompe. simpl. apply tholdssubste. apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply hmtopi. apply tmeeti. apply treflectopcart with A sa (fun a => pair a (timp T (ttop T) (tmeet T (eq (chi T (treflect T A sa) a))))).
        intros [ a ? ]. simpl. intros [ ? [ ? ? ] ? ]. subst. eauto.
        apply hmimpe. apply himpir. apply hconje1. apply tcompe. simpl. apply tholdssubste. apply hmimpe. apply himpir. apply hconje1. apply tcompe. simpl. apply tmeeti. apply treflectopcart with A (fun _ => True) (fun a => pair a (chi T (treflect T A sa) a)).
         intros [ ? ? ]. simpl. intro. subst. eauto.
         apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubst.
       apply tcompi. simpl. apply tmeete with (chi T (treflect T A sa)); try reflexivity. apply tholdssubsti. apply tid.
   simpl. eauto.
Qed.
Next Obligation.
 intro. exists (fun p => p).
  split.
   simple refine (ex_intro _ (exist _ (fun p p' => chi T (holds T) p = p') _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (Omega T) (fun p => True) (fun p => pair p (chi T (holds T) p))).
     intros [ p p' ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply hrefl.
    simpl. eauto.
   simple refine (ex_intro _ (exist _ (fun p p' => chi T (holds T) p' = p) _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply (treflectopcart T (Omega T) (fun p => True) (fun p => pair (chi T (holds T) p) p)).
     intros [ p p' ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply hrefl.
    simpl. eauto.
  intros _. exists (fun p => p); reflexivity.
Qed.
Next Obligation.
 intros T1 T2 F. split; intros A pa.
  simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, chi T2 (Map F pa) a = p & chi T2 (Map F (holds T1)) (chi T1 pa a) = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (chi T2 (Map F pa) a) (chi T2 (Map F (holds T1)) (chi T1 pa a))).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tholdssubsti. apply tidi. apply mapsubste. apply mapleq. apply tholdssubste. apply tid.
   simpl. eauto.
  simple refine (ex_intro _ (exist _ (fun p p' => exists2 a, chi T2 (Map F (holds T1)) (chi T1 pa a) = p & chi T2 (Map F pa) a = p') _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (chi T2 (Map F (holds T1)) (chi T1 pa a)) (chi T2 (Map F pa) a)).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tholdssubste. apply tide. apply mapsubsti. apply mapleq. apply tholdssubsti. apply tid.
   simpl. eauto.
Qed.


(** ** Natural Transformation: UFam ∘ RAS ⇒ Id *)

Program Definition ras_ufam_to_tripos (int : Prop) : PseudonaturalTransformation (cat_comp (RASFunctor int) (UFamFunctor int)) (cat_id (TriposCategory int))
:= pseudonatural_transformation (cat_comp (RASFunctor int) (UFamFunctor int)) (cat_id (TriposCategory int)) (fun T => tripos_morphism int (UFam (RAS T)) T (fun A pa => carrier (subst T pa) (holds T)) _ _ _ _ _ _ _) _.
Obligation Tactic := intro int; unfold Equiv; simpl (Refines _); unfold TriposRefines; simpl.
Next Obligation.
 intros T A pa pa'. unfold ReflectedAxiomSchema. intros [ [ r ias ] ? ]. simpl in *. apply (hmleq (subst T (fun a => pair (pa a) (pa' a)))) in ias. apply tcompe in ias. apply hmconji in ias. simpl in ias. apply tcompe in ias. apply tide' in ias. eapply htrans; [ clear ias | apply ias ]. apply hconji.
  apply treflectsubste. simpl. eapply htrans; [ apply htopi | ]. apply treflecttopi. apply treflectleq. auto.
  apply tcompe. simpl. apply tcompe. apply tide. apply hrefl.
Qed.
Next Obligation.
 intros. apply tholdssubste. apply hmconje. apply hconjm.
  apply tcompe. simpl. apply tcompe. apply tid.
  apply tcompe. simpl. apply tcompe. apply tid.
Qed.
Next Obligation.
 intros. apply tholdssubste. apply hmimpe. apply himpm.
  apply tcompi. simpl. apply tcompi. apply tid.
  apply tcompe. simpl. apply tmeeti. apply treflectopcart with A (fun _ => True) (fun a => pair a (pao a)).
   intros [ b ? ]. simpl. intro. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompi. apply tcompe. simpl. apply hrefl.
Qed.
Next Obligation. split; apply tcomp. Qed.
Next Obligation.
 intros. apply tholdssubste. apply hmimpe. apply himpir. apply hconje1. apply tcompe. simpl. apply tmeeti. apply treflectopcart with (prod A B) (fun _ => True) (fun ab => pair (fst ab) (pab ab)).
  intros [ a p ]. simpl. intros [ b ? ]. subst. exists (pair a b); trivial.
  apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tforalladj. apply tforallm. apply tcompe. apply tid.
Qed.
Next Obligation.
 split.
  apply tholdssubsti. apply hmimpi. apply himpapp.
   apply tcompe. simpl. apply tholdssubste. apply hmtop.
   apply tcompi. simpl. eapply tmeete.
    intro a. eexists. reflexivity.
    apply tholdssubsti. apply hmimpi. apply himpapp.
     apply tcompe. simpl. apply tholdssubste. apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply hmtopi. apply tmeeti. eapply treflectopcart with A sa (fun a => pair a _).
      intros [ a ? ]. simpl. intros [ ? [ ? ? ] ? ]. subst. eauto.
      apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. simpl. apply hmtopi. apply himpir. apply hconje2. apply tholdssubste. apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. simpl. apply himpir. apply hconje2. apply tmeeti. apply treflectopcart with A (fun _ => True) (fun a => pair a (chi T (treflect T A sa) a)).
       intros [ a ? ]. simpl. intro. subst. eauto.
       apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubst.
     apply tcompi. simpl. apply tmeete with (chi T (treflect T A sa)).
      reflexivity.
      apply tholdssubsti. apply tid.
  apply tholdssubste. apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. apply himpil. simpl. apply hconje1. apply tmeeti. eapply treflectopcart with (prod A (Omega T)) (fun _ => True) (fun p => pair (fst p) (timp T (timp T (ttop T) (tmeet T (fun p'' => exists2 p''', sa (fst p) /\ ttop T = p''' & timp T p''' (tmeet T (eq (snd p))) = p''))) (tmeet T (eq (snd p))))).
   intros [ a ? ]. simpl. intros [ p ? ]. subst. exists (pair a p); trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply treflectsubsti. apply tholdssubste. apply hmimpe. apply himpir. apply tcompe. apply himpl. apply tcompi. apply himpil. simpl. apply tmeeti. apply treflectopcart with (prod A (Omega T)) (fun _ => True) (fun p => pair (pair (fst p) (snd p)) (snd p)).
    intros [ [ a ? ] p ]. simpl. intro. subst. exists (pair a p); trivial.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply hmconji. apply himpr. apply treflectsubsti. simpl. apply himpir. apply himpl. apply tcompi. apply tholdssubsti. apply hmimpi. apply himpapp.
      apply tcompe. simpl. apply tholdssubste. apply hmtop. apply tcompi. simpl. apply himpir. apply tmeetreflecte with (fun p => timp T (ttop T) (tmeet T (eq (snd p)))).
       intros [ a p ]. eauto.
       apply tholdssubsti. apply hmimpi. apply himpapp.
        apply tcompe. simpl. apply tholdssubste. apply hmtop.
        apply tcompi. simpl. apply tmeete with snd; try reflexivity. apply tcompe. apply tid.
Qed.
Next Obligation.
 intro T. exists (fun p => p).
  split.
   apply tide. apply tid.
   apply tidi. apply tid.
  intros _. exists (fun p => p); reflexivity.
Qed.
Next Obligation.
 intros T1 T2 F. split; intros A pa.
  apply tholdssubsti. apply mapsubst.
  apply tholdssubste. apply mapsubst.
Qed.


(** ** Natural Transformation: Id ⇒ RAS ∘ UFam  *)

Program Definition evidenced_frame_to_ufam_ras (int : Prop) : PseudonaturalTransformation (cat_id (EvidencedFrameCategory int)) (cat_comp (UFamFunctor int) (RASFunctor int))
:= pseudonatural_transformation (cat_id (EvidencedFrameCategory int)) (cat_comp (UFamFunctor int) (RASFunctor int)) (fun E => evidenced_frame_morphism int E (RAS (UFam E)) (fun p => p) _ _ _ _ _) _.
Obligation Tactic := intro int; unfold Equiv; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
Next Obligation.
 intros E e. simple refine (ex_intro _ (exist _ (fun p p' => Evidences E p e p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. simpl. destruct (ecut E) as [ ec ecut ]. destruct (econje2 E) as [ ece2 econje2 ]. destruct (eimpi E) as [ eii eimpi ]. destruct (ejoine E) as [ eje ejoine ]. eexists. intros [ p p' ]. simpl. apply ejoine. intros ? [ ? ? ]. subst. apply eimpi. eapply ecut; [ apply econje2 | ]. eassumption.
  simpl. trivial.
Qed.
Next Obligation.
 intro E. simple refine (ex_intro _ (exist _ (@eq (PROP E)) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E)) (fun _ => True) (fun p => pair p p).
   intros [ ? ? ]. simpl. intro. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
  simpl. reflexivity.
Qed.
Next Obligation.
 intro E. simple refine (ex_intro _ (exist _ (@eq (PROP E)) _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E)) (fun _ => True) (fun p => pair p p).
   intros [ ? ? ]. simpl. intro. subst. eauto.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
  simpl. reflexivity.
Qed.
Next Obligation.
 intro E. simple refine (ex_intro _ (exist _ (fun p p' => exists pi, exists2 s, eimp E pi (emeet E (fun p => exists p', eimp E (ejoin E (fun p'' => (exists2 p''', s p''' & p''' = p') /\ etop E = p'')) p' = p)) = p & euniimp E pi s = p') _) _).
  unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (prod (PROP E) (PROP E -> Prop)) (fun _ => True) (fun p => pair (eimp E (fst p) (emeet E (fun p' => exists p'', eimp E (ejoin E (fun p''' => (exists2 p'''', (snd p) p'''' & p'''' = p'') /\ etop E = p''')) p'' = p'))) (euniimp E (fst p) (snd p))).
   intros [ ? ? ]. simpl. intros [ pi [ s ? ? ] ]. subst. exists (pair pi s); trivial.
   apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. destruct (eaxiom E) as [ ea eaxiom ]. destruct (ecut E) as [ ec ecut ]. destruct (etopi E) as [ eti etopi ]. destruct (econji E) as [ eci econji ]. destruct (econje1 E) as [ ece1 econje1 ]. destruct (econje2 E) as [ ece2 econje2 ]. destruct (eimpe E) as [ eie eimpe ]. destruct (euniimpi E) as [ euii euniimpi ]. destruct (emeete E) as [ eme emeete ]. destruct (ejoini E) as [ eji ejoini ]. eexists. intros [ p s ]. simpl. apply euniimpi. intros p' ?. eapply ecut; [ apply econji; [ apply econje2 | apply econje1 ] | ]. eapply ecut; [ apply eimpe | ]. eapply ecut.
    apply emeete. exists p'. reflexivity.
    eapply ecut; [ apply econji; [ | apply eaxiom ] | apply eimpe ]. eapply ecut; [ apply etopi | ]. apply ejoini. eauto.
  simpl. eauto.
Qed.
Next Obligation.
 intro E. exists (fun p => p).
  simple refine (ex_intro _ (exist _ (@eq (PROP E)) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E)) (fun _ => True) (fun p => pair p p).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
   simpl. simple refine (ex_intro _ (exist _ (@eq (PROP E)) _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E)) (fun _ => True) (fun p => pair p p).
     intros [ ? ? ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
    simpl. auto.
  intros _. exists (fun p => p); reflexivity.
Qed.
Next Obligation.
 intros E1 E2 F. split.
  simple refine (ex_intro _ (exist _ (@eq (PROP E2)) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E2)) (fun _ => True) (fun p => pair p p).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
   simpl. reflexivity.
  simple refine (ex_intro _ (exist _ (@eq (PROP E2)) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E2)) (fun _ => True) (fun p => pair p p).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
   simpl. reflexivity.
Qed.

(** ** Natural Transformation: RAS ∘ UFam ⇒ Id *)

Program Definition ufam_ras_to_evidenced_frame (int : Prop) : PseudonaturalTransformation (cat_comp (UFamFunctor int) (RASFunctor int)) (cat_id (EvidencedFrameCategory int))
:= pseudonatural_transformation (cat_comp (UFamFunctor int) (RASFunctor int)) (cat_id (EvidencedFrameCategory int)) (fun E => evidenced_frame_morphism int (RAS (UFam E)) E (fun p => p) _ _ _ _ _) _.
Obligation Tactic := intro int; unfold Equiv; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
Next Obligation. intro E. intros [ r ias ]. unfold ReflectedAxiomSchema in ias. simpl in ias. destruct ias as [ e ias ]. simpl. specialize (fun p p' => ias (pair p p')). simpl in ias. destruct (eaxiom E) as [ ea eaxiom ]. destruct (ecut E) as [ ec ecut ]. destruct (etopi E) as [ eti etopi ]. destruct (econji E) as [ eci econji ]. destruct (ejoini E) as [ eji ejoini ]. eexists. intros p p' ?. eapply ecut; [ | apply ias ]. apply econji; [ | apply eaxiom ]. eapply ecut; [ apply etopi | ]. apply ejoini. auto. Qed.
Next Obligation. intro E. destruct (eaxiom E). eauto. Qed.
Next Obligation. intro E. destruct (eaxiom E). eauto. Qed.
Next Obligation.
 intro E. destruct (eaxiom E) as [ ea eaxiom ]. destruct (ecut E) as [ ec ecut ]. destruct (euniimpe E) as [ euie euniimpe ]. destruct (econji E) as [ eci econji ]. destruct (econje1 E) as [ ece1 econje1 ]. destruct (econje2 E) as [ ece2 econje2 ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. destruct (emeeti E) as [ emi emeeti ]. destruct (ejoine E) as [ eje ejoine ]. eexists. intros. apply eimpi. apply emeeti. intros ? [ ? ? ]. subst. apply eimpi. eapply ecut; [ apply econji; [ apply econje1 | ] | apply eimpe ]. eapply ecut; [ apply econje2 | ]. apply ejoine. intros ? [ ? ? ]. subst. apply eimpi. eapply ecut; [ apply econje2 | ]. eapply ecut; [ apply econji; [ apply econje2 | apply econje1 ] | ]. eapply ecut; [ apply euniimpe | ].
  eauto.
  apply eaxiom.
Qed.
Next Obligation.
 intro E. exists (fun p => p).
  destruct (eaxiom E). eauto.
  intros _. exists (fun p => p); reflexivity.
Qed.
Next Obligation. intros E1 E2 F. destruct (eaxiom E2). eauto. Qed.


(** ** Biadjoint Biequivalence: EF ≊ Trip *)

(** Completeness:  EF_ext and Trip_ext are equivalent, as are EF_int and Trip_int,
    in the sense that UFam and RAS extend to biadjoint biequivalences between them.
 *)

Program Definition evidenced_frame_tripos_equivalence (int : Prop) : BiadjointBiequivalence (EvidencedFrameCategory int) (TriposCategory int)
:= biadjoint_biequivalence (EvidencedFrameCategory int) (TriposCategory int) (UFamFunctor int) (RASFunctor int) (evidenced_frame_to_ufam_ras int) (ufam_ras_to_evidenced_frame int) (tripos_to_ras_ufam int) (ras_ufam_to_tripos int) _ _ _ _ _.
Obligation Tactic := intro int; unfold PseudonaturalTransformationEquiv; unfold Equiv; simpl (Refines _); unfold EvidencedFrameRefines; unfold TriposRefines; simpl.
Next Obligation. intro E. destruct (eaxiom E). eauto. Qed.
Next Obligation.
 intro E. split.
  simple refine (ex_intro _ (exist _ (@eq (PROP E)) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E)) (fun _ => True) (fun p => pair p p).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
   simpl. reflexivity.
  simple refine (ex_intro _ (exist _ (@eq (PROP E)) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega (UFam E)) (fun _ => True) (fun p => pair p p).
    intros [ ? ? ]. simpl. intro. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. apply hrefl.
   simpl. reflexivity.
Qed.
Next Obligation. intro T. split.
  intros. apply tholdssubsti. apply tid.
  intros. apply tholdssubste. apply tid.
Qed.
Next Obligation.
 intro T. split.
  intros A p. simple refine (ex_intro _ (exist _ (fun pi po => exists2 a, chi T (carrier (subst T p) (holds T)) a = pi & p a = po) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (chi T (carrier (subst T p) (holds T)) a) (p a)).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tcomp.
   simpl. eauto.
  intros A p. simple refine (ex_intro _ (exist _ (fun pi po => exists2 a, p a = pi & chi T (carrier (subst T p) (holds T)) a = po) _) _).
   unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with A (fun _ => True) (fun a => pair (p a) (chi T (carrier (subst T p) (holds T)) a)).
    intros [ ? ? ]. simpl. intros [ ? ? ? ]. subst. eauto.
    apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tcomp.
   simpl. eauto.
Qed.
Next Obligation.
 repeat apply conj.
  intro E. destruct (eaxiom E). eauto.
  intro E. destruct (eaxiom E). eauto.
  intro T. split.
   simple refine (ex_intro _ (exist _ (fun p p' => chi T (holds T) p' = p) _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T) (fun _ => True) (fun p => pair (chi T (holds T) p) p).
     intros [ ? ? ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubst.
    simpl. eauto.
   simple refine (ex_intro _ (exist _ (fun p p' => chi T (holds T) p = p') _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T) (fun _ => True) (fun p => pair p (chi T (holds T) p)).
     intros [ ? ? ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubst.
    simpl. eauto.
  intro T. split.
   simple refine (ex_intro _ (exist _ (fun p p' => chi T (carrier (subst T (fun p => p)) (holds T)) p' = p) _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T) (fun _ => True) (fun p => pair (chi T (carrier (subst T (fun p => p)) (holds T)) p) p).
     intros [ ? ? ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubsti. apply tid.
    simpl. eauto.
   simple refine (ex_intro _ (exist _ (fun p p' => chi T (carrier (subst T (fun p => p)) (holds T)) p = p') _) _).
    unfold ReflectedAxiomSchema. apply himpr. apply treflectopcart with (Omega T) (fun _ => True) (fun p => pair p (chi T (carrier (subst T (fun p => p)) (holds T)) p)).
     intros [ ? ? ]. simpl. intro. subst. eauto.
     apply hmimpe. apply himpir. apply hconje2. apply tcompi. apply tcompe. simpl. apply tholdssubste. apply tid.
    simpl. eauto.
Qed.


(** * Theorem V.13: Equivalence of Evidenced Frames and Set-Based Triposes *)

Definition evidenced_frame_set_tripos_equivalence (uip : UIP_SET) (int : Prop) : BiadjointBiequivalence (EvidencedFrameCategory int) (SurjSetTriposCategory int)
:= equivalence_comp (evidenced_frame_tripos_equivalence int) (tripos_set_tripos_equivalence uip int).
