Require Import Program.
Require Import EF.Categories.
Obligation Tactic := idtac.


(** * Evidenced Frames *)

(** ** Definition *)

Record EvidencedFrame : Class := evidenced_frame {
  PROP : SET;
  Evidence : Type;
  Evidences : PROP -> Evidence -> PROP -> Prop;
  etop : PROP;
  econj : PROP -> PROP -> PROP;
  euniimp : PROP -> (PROP -> Prop) -> PROP;
  eaxiom : exists ea : Evidence, forall p : PROP, Evidences p ea p;
  ecut : exists ec : Evidence -> Evidence -> Evidence, forall p1 p2 p3 : PROP, forall e12 e23 : Evidence, Evidences p1 e12 p2 -> Evidences p2 e23 p3 -> Evidences p1 (ec e12 e23) p3;
  etopi : exists et : Evidence, forall p : PROP, Evidences p et etop;
  econji : exists ec : Evidence -> Evidence -> Evidence, forall p p1 p2 : PROP, forall e1 e2 : Evidence, Evidences p e1 p1 -> Evidences p e2 p2 -> Evidences p (ec e1 e2) (econj p1 p2);
  econje1 : exists ec : Evidence, forall p1 p2 : PROP, Evidences (econj p1 p2) ec p1;
  econje2 : exists ec : Evidence, forall p1 p2 : PROP, Evidences (econj p1 p2) ec p2;
  euniimpi : exists eu : Evidence -> Evidence, forall p1 p2 : PROP, forall pi : PROP -> Prop, forall e : Evidence, (forall p' : PROP, pi p' -> Evidences (econj p1 p2) e p') -> Evidences p1 (eu e) (euniimp p2 pi);
  euniimpe : exists eu : Evidence, forall p : PROP, forall pi : PROP -> Prop, forall p' : PROP, pi p' -> Evidences (econj p (euniimp p pi)) eu p'
}.

Definition eimp (E : EvidencedFrame) (pi po : PROP E) : PROP E
:= euniimp E pi (eq po).
Definition emeet (E : EvidencedFrame) (pi : PROP E -> Prop) : PROP E
:= euniimp E (etop E) pi.
Definition ebot (E : EvidencedFrame) : PROP E
:= emeet E (fun _ => True).
Definition edisj (E : EvidencedFrame) (p1 p2 : PROP E) : PROP E
:= emeet E (fun p => exists p', eimp E (eimp E p1 p') (eimp E (eimp E p2 p') p') = p).
Definition ejoin (E : EvidencedFrame) (pi : PROP E -> Prop) : PROP E
:= emeet E (fun p => exists p', eimp E (emeet E (fun p'' => exists2 p''', pi p''' & eimp E p''' p' = p'')) p' = p).

Lemma eimpi (E : EvidencedFrame) : exists ei : Evidence E -> Evidence E, forall p pi po : PROP E, forall e : Evidence E, Evidences E (econj E p pi) e po -> Evidences E p (ei e) (eimp E pi po).
 destruct (euniimpi E) as [ eu ? ]. exists eu. intros. apply H. intros. subst. assumption.
Qed.
Lemma eimpe (E : EvidencedFrame) : exists ei : Evidence E, forall pi po : PROP E, Evidences E (econj E pi (eimp E pi po)) ei po.
 destruct (euniimpe E) as [ eu ? ]. exists eu. intros. apply H. reflexivity.
Qed.
Lemma emeeti (E : EvidencedFrame) : exists em : Evidence E -> Evidence E, forall p : PROP E, forall pi : PROP E -> Prop, forall e : Evidence E, (forall p' : PROP E, pi p' -> Evidences E p e p') -> Evidences E p (em e) (emeet E pi).
 destruct (euniimpi E) as [ eu euniimpi ]. destruct (ecut E) as [ ec ecut ]. destruct (econje1 E) as [ ec1 econje1 ]. eexists. intros. apply euniimpi. intros. apply ecut with p; eauto.
Qed.
Lemma emeete (E : EvidencedFrame) : exists em : Evidence E, forall pi : PROP E -> Prop, forall p' : PROP E, pi p' -> Evidences E (emeet E pi) em p'.
 destruct (euniimpe E) as [ eu euniimpe ]. destruct (ecut E) as [ ec ecut ]. destruct (econji E) as [ eci econji ]. destruct (etopi E) as [ et etopi ]. destruct (eaxiom E) as [ ea eaxiom ]. eexists. intros. apply ecut with (econj E (etop E) (emeet E pi)); eauto.
Qed.
Lemma ebote (E : EvidencedFrame) : exists eb : Evidence E, forall p : PROP E, Evidences E (ebot E) eb p.
 destruct (emeete E) as [ em emeete ]. eexists. eauto.
Qed.
Lemma edisji1 (E : EvidencedFrame) : exists ed : Evidence E, forall p1 p2 : PROP E, Evidences E p1 ed (edisj E p1 p2).
 destruct (emeeti E) as [ em emeeti ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. destruct (ecut E) as [ ec ecut ]. destruct (econje1 E) as [ ece1 econje1 ]. eexists. intros. apply emeeti. intros p' [ p'' ? ]. subst. apply eimpi. apply eimpi. apply ecut with (econj E p1 (eimp E p1 p'')); eauto.
Qed.
Lemma edisji2 (E : EvidencedFrame) : exists ed : Evidence E, forall p1 p2 : PROP E, Evidences E p2 ed (edisj E p1 p2).
 destruct (emeeti E) as [ em emeeti ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. destruct (ecut E) as [ ec ecut ]. destruct (econje1 E) as [ ece1 econje1 ]. eexists. intros. apply emeeti. intros p' [ p'' ? ]. subst. apply eimpi. apply ecut with p2; eauto.
Qed.
Lemma edisje (E : EvidencedFrame) : exists ed : Evidence E -> Evidence E -> Evidence E, forall p1 p2 p' : PROP E, forall e1 e2 : Evidence E, Evidences E p1 e1 p' -> Evidences E p2 e2 p' -> Evidences E (edisj E p1 p2) (ed e1 e2) p'.
 destruct (emeete E) as [ eme emeete ]. destruct (ecut E) as [ ec ecut ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. destruct (econji E) as [ eci econji ]. destruct (econje2 E) as [ ece2 econje2 ]. destruct (eaxiom E) as [ ea eaxiom ]. eexists. intros. eapply ecut; [ apply emeete; eauto | ]. apply ecut with (eimp E (eimp E p2 p') p').
  eapply ecut; [ | apply eimpe ]. apply econji; [ | apply eaxiom ]. apply eimpi. eapply ecut; [ apply econje2 | ]. eassumption.
  eapply ecut; [ | apply eimpe ]. apply econji; [ | apply eaxiom ]. apply eimpi. eapply ecut; [ apply econje2 | ]. eassumption.
Qed.
Lemma ejoini (E : EvidencedFrame) : exists ej : Evidence E, forall pi : PROP E -> Prop, forall p : PROP E, pi p -> Evidences E p ej (ejoin E pi).
 destruct (emeeti E) as [ emi emeeti ]. destruct (emeete E) as [ eme emeete ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. destruct (ecut E) as [ ec ecut ]. destruct (econji E) as [ eci econji ]. destruct (econje1 E) as [ ece1 econje1 ]. destruct (econje2 E) as [ ece2 econje2 ]. eexists. intros. apply emeeti. intros p' [ p'' e ]. destruct e. apply eimpi. apply ecut with (econj E p (eimp E p p'')); try apply eimpe. apply econji; try apply econje1. eapply ecut; [ apply econje2 | ]. apply emeete. eauto.
Qed.
Lemma ejoine (E : EvidencedFrame) : exists ej : Evidence E -> Evidence E, forall p' : PROP E, forall pi : PROP E -> Prop, forall e : Evidence E, (forall p : PROP E, pi p -> Evidences E p e p') -> Evidences E (ejoin E pi) (ej e) p'.
 destruct (emeeti E) as [ emi emeeti ]. destruct (emeete E) as [ eme emeete ]. destruct (ecut E) as [ ec ecut ]. destruct (econji E) as [ eci econji ]. destruct (econje2 E) as [ ece2 econje2 ]. destruct (eaxiom E) as [ ea eaxiom ]. destruct (eimpi E) as [ eii eimpi ]. destruct (eimpe E) as [ eie eimpe ]. eexists. intros. eapply ecut; [ apply emeete; eauto | ]. eapply ecut; [ apply econji; [ | apply eaxiom ] | apply eimpe ]. apply emeeti. intros ? [ p ? ? ]. subst. apply eimpi. eapply ecut; [ apply econje2 | auto ].
Qed.


(** ** Morphisms *)

Record EvidencedFrameMorphism {int : Prop} {E1 E2 : EvidencedFrame} : Type := evidenced_frame_morphism {
  Convert : PROP E1 -> PROP E2;
  conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, Evidences E1 p1 e1 p1' -> Evidences E2 (Convert p1) e2 (Convert p1');
  contop : exists e2 : Evidence E2, Evidences E2 (etop E2) e2 (Convert (etop E1));
  conconj : exists e2 : Evidence E2, forall p1 p1' : PROP E1, Evidences E2 (econj E2 (Convert p1) (Convert p1')) e2 (Convert (econj E1 p1 p1'));
  conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, Evidences E2 (euniimp E2 (Convert p1) (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')) e2 (Convert (euniimp E1 p1 s1));
  conprop : exists2 f : PROP E2 -> PROP E1, exists e2 e2' : Evidence E2, forall p2 : PROP E2, Evidences E2 p2 e2 (Convert (f p2)) /\ Evidences E2 (Convert (f p2)) e2' p2 & int -> exists2 finv : PROP E1 -> PROP E2, (fun p1 : PROP E1 => p1) = (fun p1 : PROP E1 => f (finv p1)) & (fun p2 : PROP E2 => p2) = (fun p2 : PROP E2 => finv (f p2))
}.
Arguments EvidencedFrameMorphism : clear implicits.
Arguments evidenced_frame_morphism : clear implicits.

Lemma conimp' {E1 E2 : EvidencedFrame}
  (Convert : PROP E1 -> PROP E2)
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, Evidences E2 (euniimp E2 (Convert p1) (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')) e2 (Convert (euniimp E1 p1 s1)))
  : exists e2 : Evidence E2, forall pi1 po1 : PROP E1, Evidences E2 (eimp E2 (Convert pi1) (Convert po1)) e2 (Convert (eimp E1 pi1 po1)).
 destruct conuniimp as [ cui conuniimp ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (econji E2) as [ eci2 econji2 ]. destruct (econje1 E2) as [ ece12 econje12 ]. destruct (econje2 E2) as [ ece22 econje22 ]. destruct (euniimpi E2) as [ euii2 euniimpi2 ]. destruct (eimpe E2) as [ eie2 eimpe2 ]. eexists. intros. eapply ecut2; [ | apply conuniimp ]. apply euniimpi2. intros ? [ p1 ? ? ]. subst. eapply ecut2; [ apply econji2; [ apply econje22 | apply econje12 ] | ]. apply eimpe2.
Qed.
Lemma conmeet' {E1 E2 : EvidencedFrame}
  (Convert : PROP E1 -> PROP E2)
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, Evidences E2 (euniimp E2 (Convert p1) (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')) e2 (Convert (euniimp E1 p1 s1)))
  : exists e2 : Evidence E2, forall s1 : PROP E1 -> Prop, Evidences E2 (emeet E2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')) e2 (Convert (emeet E1 s1)).
 destruct conuniimp as [ cui conuniimp ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (econje1 E2) as [ ece12 econje12 ]. destruct (euniimpi E2) as [ euii2 euniimpi2 ]. destruct (emeete E2) as [ eme2 emeete2 ]. eexists. intros. eapply ecut2; [ | apply conuniimp ]. apply euniimpi2. intros ? [ p1 ? ? ]. subst. eapply ecut2; [ apply econje12 | ]. apply emeete2. eauto.
Qed.
Lemma conjoin' {E1 E2 : EvidencedFrame}
  (Convert : PROP E1 -> PROP E2)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, Evidences E1 p1 e1 p1' -> Evidences E2 (Convert p1) e2 (Convert p1'))
  (conconj : exists e2 : Evidence E2, forall p1 p1' : PROP E1, Evidences E2 (econj E2 (Convert p1) (Convert p1')) e2 (Convert (econj E1 p1 p1')))
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, Evidences E2 (euniimp E2 (Convert p1) (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')) e2 (Convert (euniimp E1 p1 s1)))
  (conprop_weak : exists e2 e2' : Evidence E2, forall p2 : PROP E2, exists2 p1 : PROP E1, Evidences E2 p2 e2 (Convert p1) & Evidences E2 (Convert p1) e2' p2)
  : exists e2 : Evidence E2, forall s1 : PROP E1 -> Prop, Evidences E2 (Convert (ejoin E1 s1)) e2 (ejoin E2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')).
 destruct conconj as [ cc conconj ]. destruct (conimp' Convert) as [ ci conimp ]; try assumption. destruct (conmeet' Convert) as [ cm conmeet ]; try assumption. destruct conprop_weak as [ e2 [ e2' conprop_weak ] ]. destruct (ecut E1) as [ ec1 ecut1 ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (econji E1) as [ eci1 econji1 ]. destruct (econje1 E1) as [ ece11 econje11 ]. destruct (econje2 E1) as [ ece21 econje21 ]. destruct (econji E2) as [ eci2 econji2 ]. destruct (econje1 E2) as [ ece12 econje12 ]. destruct (econje2 E2) as [ ece22 econje22 ]. destruct (eimpe E1) as [ eie1 eimpe1 ]. destruct (eimpi E2) as [ eii2 eimpi2 ]. destruct (eimpe E2) as [ eie2 eimpe2 ]. destruct (emeete E1) as [ eme1 emeete1 ]. destruct (emeeti E2) as [ emi2 emeeti2 ]. destruct (emeete E2) as [ eme2 emeete2 ]. edestruct conevidence as [ ce' conevidence' ]. edestruct conevidence as [ ce'' conevidence'' ]. eexists. intro. unfold ejoin at 2. apply emeeti2. intros ? [ p2 ? ]. subst. destruct conprop_weak with p2 as [ p1 e21 e12 ]. eapply ecut2.
  apply conevidence'. apply emeete1. exists p1. reflexivity.
  apply ecut2 with (eimp E2 (Convert (emeet E1 (fun p'' => exists2 p''', s1 p''' & eimp E1 p''' p1 = p''))) (Convert p1)).
   apply eimpi2. eapply ecut2; [ apply conconj | ]. apply conevidence''. eapply ecut1; [ apply econji1; [ apply econje21 | apply econje11 ] | apply eimpe1 ].
   apply eimpi2. apply ecut2 with (Convert p1); try eassumption. eapply ecut2; [ apply econji2; [ | apply econje12 ] | apply eimpe2 ]. eapply ecut2; [ apply econje22 | ]. eapply ecut2; [ | apply conmeet ]. apply emeeti2. intros ? [ ? [ p1' ? ? ] ? ]. subst. eapply ecut2.
    apply emeete2.
     eexists; try reflexivity. exists p1'; eauto.
     eapply ecut2; [ | apply conimp ]. apply eimpi2. apply ecut2 with p2; try eassumption. eapply ecut2; [ apply econji2; [ apply econje22 | apply econje12 ] | ]. apply eimpe2.
Qed.

Lemma conimp {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) : exists e2 : Evidence E2, forall pi1 po1 : PROP E1, Evidences E2 (eimp E2 (Convert F pi1) (Convert F po1)) e2 (Convert F (eimp E1 pi1 po1)).
 apply conimp'. apply conuniimp.
Qed.
Lemma conmeet {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) : exists e2 : Evidence E2, forall s1 : PROP E1 -> Prop, Evidences E2 (emeet E2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert F p1' = p2')) e2 (Convert F (emeet E1 s1)).
 apply conmeet'. apply conuniimp.
Qed.
Lemma conjoin {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) : exists e2 : Evidence E2, forall s1 : PROP E1 -> Prop, Evidences E2 (Convert F (ejoin E1 s1)) e2 (ejoin E2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert F p1' = p2')).
 apply conjoin'.
  apply conevidence.
  apply conconj.
  apply conuniimp.
  destruct (conprop F) as [ f [ e2 [ e2' ef ] ] ? ]. exists e2. exists e2'. intro p2. exists (f p2); apply ef.
Qed.

Program Definition evidenced_frame_morphism_extensional (E1 E2 : EvidencedFrame)
  (Convert : PROP E1 -> PROP E2)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, Evidences E1 p1 e1 p1' -> Evidences E2 (Convert p1) e2 (Convert p1'))
  (contop : exists e2 : Evidence E2, Evidences E2 (etop E2) e2 (Convert (etop E1)))
  (conconj : exists e2 : Evidence E2, forall p1 p1' : PROP E1, Evidences E2 (econj E2 (Convert p1) (Convert p1')) e2 (Convert (econj E1 p1 p1')))
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, Evidences E2 (euniimp E2 (Convert p1) (fun p2' => exists2 p1' : PROP E1, s1 p1' & Convert p1' = p2')) e2 (Convert (euniimp E1 p1 s1)))
  (conprop : exists e2 e2' : Evidence E2, forall p2 : PROP E2, exists2 p1 : PROP E1, Evidences E2 p2 e2 (Convert p1) & Evidences E2 (Convert p1) e2' p2)
  : EvidencedFrameMorphism False E1 E2
:= evidenced_frame_morphism False E1 E2 Convert conevidence contop conconj conuniimp _.
Obligation Tactic := intros E1 E2 Convert conevidence contop conconj conuniimp conprop_weak.
Next Obligation.
 destruct (conjoin' Convert) as [ cj conjoin ]; try assumption. destruct conprop_weak as [ e2 [ e2' conprop_weak ] ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (ejoini E1) as [ eji1 ejoini1 ]. destruct (ejoine E2) as [ eje2 ejoine2 ]. exists (fun p2 => ejoin E1 (fun p1 => Evidences E2 p2 e2 (Convert p1) /\ Evidences E2 (Convert p1) e2' p2)); [ | intros [] ]. edestruct conevidence as [ ce' conevidence' ]. eexists. eexists. intro p2. destruct conprop_weak with p2 as [ p1 e21 e12 ]. split.
  eapply ecut2; try eassumption. apply conevidence'. apply ejoini1. auto.
  eapply ecut2; [ apply conjoin | ]. apply ecut2 with (Convert p1); try eassumption. apply ejoine2. intros ? [ p1' [ ? ? ] ? ]. subst. apply ecut2 with p2; eassumption.
Qed.

Lemma conimp'' {E1 E2 : EvidencedFrame}
  (Relate : PROP E1 -> PROP E2 -> Prop)
  (contotal : forall p1 : PROP E1, exists p2 : PROP E2, Relate p1 p2)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, forall p2 p2' : PROP E2, Relate p1 p2 -> Relate p1' p2' -> Evidences E1 p1 e1 p1' -> Evidences E2 p2 e2 p2')
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, exists2 p2 : PROP E2, Relate p1 p2 & exists2 puniimp : PROP E2, Relate (euniimp E1 p1 s1) puniimp & Evidences E2 (euniimp E2 p2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')) e2 puniimp)
  : exists e2 : Evidence E2, forall pi1 po1 : PROP E1, exists2 pi2 : PROP E2, Relate pi1 pi2 & exists2 po2 : PROP E2, Relate po1 po2 & exists2 pimp : PROP E2, Relate (eimp E1 pi1 po1) pimp & Evidences E2 (eimp E2 pi2 po2) e2 pimp.
 destruct conuniimp as [ cui conuniimp ]. destruct (eaxiom E1) as [ ea1 eaxiom1 ]. destruct conevidence with ea1 as [ ca conaxiom ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (econji E2) as [ eci2 econji2 ]. destruct (econje1 E2) as [ ece12 econje12 ]. destruct (econje2 E2) as [ ece22 econje22 ]. destruct (euniimpi E2) as [ euii2 euniimpi2 ]. destruct (eimpe E2) as [ eie2 eimpe2 ]. eexists. intros pi1 po1. destruct (conuniimp pi1 (eq po1)) as [ pi2 ? [ pimp ? ? ] ]. exists pi2; try assumption. destruct contotal with po1 as [ po2 ? ]. exists po2; try assumption. exists pimp; try assumption. eapply ecut2; [ | eassumption ]. apply euniimpi2. intros ? [ p1 ? ? ]. subst. eapply ecut2; [ apply econji2; [ apply econje22 | apply econje12 ] | ]. apply ecut2 with po2; [ apply eimpe2 | ]. eapply conaxiom; eauto.
Qed.
Lemma conmeet'' {E1 E2 : EvidencedFrame}
  (Relate : PROP E1 -> PROP E2 -> Prop)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, forall p2 p2' : PROP E2, Relate p1 p2 -> Relate p1' p2' -> Evidences E1 p1 e1 p1' -> Evidences E2 p2 e2 p2')
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, exists2 p2 : PROP E2, Relate p1 p2 & exists2 puniimp : PROP E2, Relate (euniimp E1 p1 s1) puniimp & Evidences E2 (euniimp E2 p2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')) e2 puniimp)
  : exists e2 : Evidence E2, forall s1 : PROP E1 -> Prop, exists2 pmeet : PROP E2, Relate (emeet E1 s1) pmeet & Evidences E2 (emeet E2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')) e2 pmeet.
 destruct conuniimp as [ cui conuniimp ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (econje1 E2) as [ ece12 econje12 ]. destruct (euniimpi E2) as [ euii2 euniimpi2 ]. destruct (emeete E2) as [ eme2 emeete2 ]. eexists. intros. destruct conuniimp with (etop E1) s1 as [ ptop ? [ pmeet ? ? ] ]. exists pmeet; try assumption. eapply ecut2; [ | eassumption ]. apply euniimpi2. intros ? [ p1 ? ? ]. subst. eapply ecut2; [ apply econje12 | ]. apply emeete2. eauto.
Qed.
Lemma conjoin'' {E1 E2 : EvidencedFrame}
  (Relate : PROP E1 -> PROP E2 -> Prop)
  (contotal : forall p1 : PROP E1, exists p2 : PROP E2, Relate p1 p2)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, forall p2 p2' : PROP E2, Relate p1 p2 -> Relate p1' p2' -> Evidences E1 p1 e1 p1' -> Evidences E2 p2 e2 p2')
  (conconj : exists e2 : Evidence E2, forall p1 p1' : PROP E1, exists2 p2 : PROP E2, Relate p1 p2 & exists2 p2' : PROP E2, Relate p1' p2' & exists2 pconj : PROP E2, Relate (econj E1 p1 p1') pconj & Evidences E2 (econj E2 p2 p2') e2 pconj)
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, exists2 p2 : PROP E2, Relate p1 p2 & exists2 puniimp : PROP E2, Relate (euniimp E1 p1 s1) puniimp & Evidences E2 (euniimp E2 p2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')) e2 puniimp)
  (conprop : forall p2 : PROP E2, exists p1 : PROP E1, Relate p1 p2)
  : exists e2 : Evidence E2, forall s1 : PROP E1 -> Prop, exists2 pjoin : PROP E2, Relate (ejoin E1 s1) pjoin & Evidences E2 pjoin e2 (ejoin E2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')).
 destruct conconj as [ cc conconj ]. destruct (conimp'' Relate) as [ ci conimp ]; try assumption. destruct (conmeet'' Relate) as [ cm conmeet ]; try assumption. destruct (eaxiom E1) as [ ea1 eaxiom1 ]. destruct conevidence with ea1 as [ ca conaxiom ]. destruct (ecut E1) as [ ec1 ecut1 ]. destruct (ecut E2) as [ ec2 ecut2 ]. destruct (econji E1) as [ eci1 econji1 ]. destruct (econje1 E1) as [ ece11 econje11 ]. destruct (econje2 E1) as [ ece21 econje21 ]. destruct (econji E2) as [ eci2 econji2 ]. destruct (econje1 E2) as [ ece12 econje12 ]. destruct (econje2 E2) as [ ece22 econje22 ]. destruct (eimpe E1) as [ eie1 eimpe1 ]. destruct (eimpi E2) as [ eii2 eimpi2 ]. destruct (eimpe E2) as [ eie2 eimpe2 ]. destruct (emeete E1) as [ eme1 emeete1 ]. destruct (emeeti E2) as [ emi2 emeeti2 ]. destruct (emeete E2) as [ eme2 emeete2 ]. edestruct conevidence as [ ce' conevidence' ]. edestruct conevidence as [ ce'' conevidence'' ]. eexists. intro. unfold ejoin at 1. destruct conmeet with (fun p => exists p', eimp E1 (emeet E1 (fun p'' => exists2 p''', s1 p''' & eimp E1 p''' p' = p'')) p' = p) as [ pjoin ? ? ]. exists pjoin; try assumption. unfold ejoin. apply emeeti2. intros ? [ p2 ? ]. subst. destruct conprop with p2 as [ p1 ? ]. destruct conimp with (emeet E1 (fun p'' => exists2 p''', s1 p''' & eimp E1 p''' p1 = p'')) p1 as [ pmeet ? [ p2' ? [ pimp ? ? ] ] ]. eapply ecut2.
  eapply conevidence'; [ eassumption | | apply emeete1; exists p1; reflexivity ]. eassumption.
  apply ecut2 with (eimp E2 pmeet p2).
   apply eimpi2. destruct conconj with (eimp E1 (emeet E1 (fun p'' => exists2 p''', s1 p''' & eimp E1 p''' p1 = p'')) p1) (emeet E1 (fun p'' => exists2 p''', s1 p''' & eimp E1 p''' p1 = p'')) as [ pimp1 ? [ pmeet1 ? [ pconj ? ? ] ] ]. apply ecut2 with pconj.
    eapply ecut2; [ | eassumption ]. apply econji2.
     eapply ecut2; [ apply econje12 | ]. eapply conaxiom; eauto.
     eapply ecut2; [ apply econje22 | ]. eapply conaxiom; eauto.
    eapply conevidence''; try eassumption. eapply ecut1; [ apply econji1; [ apply econje21 | apply econje11 ] | apply eimpe1 ].
   apply eimpi2. eapply ecut2; [ apply econji2; [ | apply econje12 ] | apply eimpe2 ]. eapply ecut2; [ apply econje22 | ]. destruct conmeet with (fun p'' => exists2 p''', s1 p''' & eimp E1 p''' p1 = p'') as [ pmeet' ? ? ]. apply ecut2 with pmeet'; [ | eapply conaxiom; eauto ]. eapply ecut2; [ | eassumption ]. apply emeeti2. intros ? [ ? [ p1' ? ? ] ? ]. subst. destruct contotal with p1' as [ p2'' ? ]. eapply ecut2.
    apply emeete2.
     eexists; try reflexivity. exists p1'; eauto.
     destruct conimp with p1' p1 as [ ? ? [ ? ? [ pimp' ? ? ] ] ].
     apply ecut2 with pimp'; [ | eapply conaxiom; eauto ]. eapply ecut2; [ | eassumption ]. apply eimpi2. apply ecut2 with p2; [ | eapply conaxiom; eauto ]. apply ecut2 with (econj E2 p2'' (eimp E2 p2'' p2)); [ | apply eimpe2 ]. apply econji2; [ | apply econje12 ]. eapply ecut2; [ apply econje22 | ]. eapply conaxiom; eauto.
Qed.

Program Definition evidenced_frame_morphism_relational_exists (int : bool) (E1 E2 : EvidencedFrame)
  (Relate : PROP E1 -> PROP E2 -> Prop)
  (contotal : forall p1 : PROP E1, exists p2 : PROP E2, Relate p1 p2)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, forall p2 p2' : PROP E2, Relate p1 p2 -> Relate p1' p2' -> Evidences E1 p1 e1 p1' -> Evidences E2 p2 e2 p2')
  (contop : exists e2 : Evidence E2, exists2 ptop : PROP E2, Relate (etop E1) ptop & Evidences E2 (etop E2) e2 ptop)
  (conconj : exists e2 : Evidence E2, forall p1 p1' : PROP E1, exists2 p2 : PROP E2, Relate p1 p2 & exists2 p2' : PROP E2, Relate p1' p2' & exists2 pconj : PROP E2, Relate (econj E1 p1 p1') pconj & Evidences E2 (econj E2 p2 p2') e2 pconj)
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, exists2 p2 : PROP E2, Relate p1 p2 & exists2 puniimp : PROP E2, Relate (euniimp E1 p1 s1) puniimp & Evidences E2 (euniimp E2 p2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')) e2 puniimp)
  (conprop : if int then (exists2 f : PROP E2 -> PROP E1, (forall p1 : PROP E1, forall p2 : PROP E2, Relate p1 p2 <-> f p2 = p1) & (exists2 finv : PROP E1 -> PROP E2, (fun p1 : PROP E1 => p1) = (fun p1 : PROP E1 => f (finv p1)) & (fun p2 : PROP E2 => p2) = (fun p2 : PROP E2 => finv (f p2)))) else (forall p2 : PROP E2, exists p1 : PROP E1, Relate p1 p2))
  : EvidencedFrameMorphism (if int then True else False) E1 E2
:= evidenced_frame_morphism (if int then True else False) E1 E2 (fun p1 => ejoin E2 (Relate p1)) _ _ _ _ _.
Obligation Tactic := intros int E1 E2 Relate contotal conevidence contop conconj conuniimp conprop; destruct (eaxiom E1) as [ ea1 eaxiom1 ]; destruct (eaxiom E2) as [ ea2 eaxiom2 ]; destruct (ecut E2) as [ ec2 ecut2 ]; destruct (econji E2) as [ eci2 econji2 ]; destruct (econje1 E2) as [ ece12 econje12 ]; destruct (euniimpi E2) as [ euii2 euniimpi2 ]; destruct (euniimpe E2) as [ euie2 euniimpe2 ]; destruct (econje2 E2) as [ ece22 econje22 ]; destruct (ejoini E1) as [ eji1 ejoini1 ]; destruct (ejoine E1) as [ eje1 ejoine1 ]; destruct (ejoini E2) as [ eji2 ejoini2 ]; destruct (ejoine E2) as [ eje2 ejoine2 ].
Next Obligation. intro e1. destruct conevidence with e1 as [ ce' conevidence' ]. eexists. intros. apply ejoine2. intros p2 ?. destruct contotal with p1' as [ p2' ? ]. eapply ecut2; [ eapply conevidence'; eassumption | ]. apply ejoini2. assumption. Qed.
Next Obligation.
 destruct contop as [ ct [ ptop ? contop ] ]. eexists. apply ecut2 with ptop.
  apply contop.
  apply ejoini2. assumption.
Qed.
Next Obligation.
 destruct conconj as [ cc conconj ]. destruct conevidence with ea1 as [ ca conaxiom ]. eexists. intros p1 p1'. destruct conconj with p1 p1' as [ p2 ? [ p2' ? [ pconj ? ? ] ] ]. apply ecut2 with pconj.
  apply ecut2 with (econj E2 p2 p2').
   apply econji2.
    eapply ecut2; [ apply econje12 | ]. apply ejoine2. intros. apply conaxiom with p1 p1; try assumption. apply eaxiom1.
    eapply ecut2; [ apply econje22 | ]. apply ejoine2. intros. apply conaxiom with p1' p1'; try assumption. apply eaxiom1.
   eassumption.
  apply ejoini2. assumption.
Qed.
Next Obligation.
 destruct conuniimp as [ cui conuniimp ]. destruct conevidence with ea1 as [ ca conaxiom ]. eexists. intros p1 s1. destruct conuniimp with p1 s1 as [ p2 ? [ puniimp ? ? ] ]. apply ecut2 with puniimp.
  apply ecut2 with (euniimp E2 p2 (fun p2' => exists2 p1', s1 p1' & Relate p1' p2')).
   apply euniimpi2. intros p2' [ p1' ? ? ]. apply ecut2 with (ejoin E2 (Relate p1')).
    eapply ecut2; [ apply econji2; [ | apply econje12 ] | apply euniimpe2; try eauto ]. eapply ecut2; [ apply econje22 | ]. apply ejoini2. assumption.
    apply ejoine2. intros. apply conaxiom with p1' p1'; try assumption. apply eaxiom1.
   eassumption.
  apply ejoini2. assumption.
Qed.
Next Obligation.
 destruct int.
  destruct conprop as [ f fr [ finv finvf ffinv ] ]. exists f; try eauto. destruct conevidence with ea1 as [ ca conaxiom ]. eexists. eexists. intro. split.
   apply ejoini2. apply fr. reflexivity.
   apply ejoine2. intros p2' r. apply fr in r. change p2 with ((fun p => p) p2). change p2' with ((fun p => p) p2'). rewrite ffinv. rewrite r. apply eaxiom2.
  destruct (conjoin'' Relate) as [ cj conjoin ]; try assumption. destruct conevidence with ea1 as [ ca conaxiom ]. edestruct conevidence as [ ce' conevidence' ]. exists (fun p2 => ejoin E1 (fun p1 => Relate p1 p2)); [ | intros [ ] ]. eexists. eexists. intro p2. destruct conjoin with (fun p1 => Relate p1 p2) as [ pjoin ? ? ]. destruct conprop with p2 as [ p1 ? ]. split.
   apply ecut2 with pjoin.
    apply conevidence' with p1 (ejoin E1 (fun p1 => Relate p1 p2)); try assumption. apply ejoini1. assumption.
    apply ejoini2. assumption.
   apply ejoine2. intros p2' ?. apply ecut2 with pjoin.
    eapply conaxiom; try eassumption. apply eaxiom1.
    eapply ecut2; try eassumption. apply ejoine2. intros p2'' [ p1'' ? ? ]. eapply conaxiom; try eassumption. apply eaxiom1.
Qed.

Program Definition evidenced_frame_morphism_relational_forall (int : bool) (E1 E2 : EvidencedFrame)
  (Relate : PROP E1 -> PROP E2 -> Prop)
  (contotal : forall p1 : PROP E1, exists p2 : PROP E2, Relate p1 p2)
  (conevidence : forall e1 : Evidence E1, exists e2 : Evidence E2, forall p1 p1' : PROP E1, forall p2 p2' : PROP E2, Relate p1 p2 -> Relate p1' p2' -> Evidences E1 p1 e1 p1' -> Evidences E2 p2 e2 p2')
  (contop : exists e2 : Evidence E2, forall ptop : PROP E2, Relate (etop E1) ptop -> Evidences E2 (etop E2) e2 ptop)
  (conconj : exists e2 : Evidence E2, forall p1 p1' : PROP E1, forall p2 p2' pconj : PROP E2, Relate p1 p2 -> Relate p1' p2' -> Relate (econj E1 p1 p1') pconj -> Evidences E2 (econj E2 p2 p2') e2 pconj)
  (conuniimp : exists e2 : Evidence E2, forall p1 : PROP E1, forall s1 : PROP E1 -> Prop, forall p2 puniimp : PROP E2, Relate p1 p2 -> Relate (euniimp E1 p1 s1) puniimp -> Evidences E2 (euniimp E2 p2 (fun p2' => exists2 p1' : PROP E1, s1 p1' & Relate p1' p2')) e2 puniimp)
  (conprop : if int then (exists2 f : PROP E2 -> PROP E1, (forall p1 : PROP E1, forall p2 : PROP E2, Relate p1 p2 <-> f p2 = p1) & (exists2 finv : PROP E1 -> PROP E2, (fun p1 : PROP E1 => p1) = (fun p1 : PROP E1 => f (finv p1)) & (fun p2 : PROP E2 => p2) = (fun p2 : PROP E2 => finv (f p2)))) else (forall p2 : PROP E2, exists p1 : PROP E1, Relate p1 p2))
  : EvidencedFrameMorphism (if int then True else False) E1 E2
:= evidenced_frame_morphism_relational_exists int E1 E2 Relate contotal conevidence _ _ _ conprop.
Obligation Tactic := intros int E1 E2 Relate contotal _ contop conconj conuniimp conprop.
Next Obligation. destruct contop as [ ct contop ]. exists ct. destruct contotal with (etop E1) as [ ptop ? ]. exists ptop; auto. Qed.
Next Obligation. destruct conconj as [ cc conconj ]. exists cc. intros p1 p1'. destruct contotal with p1 as [ p2 ? ]. destruct contotal with p1' as [ p2' ? ]. destruct contotal with (econj E1 p1 p1') as [ pconj ? ]. exists p2; try assumption. exists p2'; try assumption. exists pconj; eauto. Qed.
Next Obligation. destruct conuniimp as [ cui conuniimp ]. exists cui. intros p1 s1. destruct contotal with p1 as [ p2 ? ]. destruct contotal with (euniimp E1 p1 s1) as [ puniimp ? ]. exists p2; try assumption. exists puniimp; eauto. Qed.

Program Definition ef_id (int : Prop) (E : EvidencedFrame) : EvidencedFrameMorphism int E E
:= evidenced_frame_morphism int E E (fun p => p) _ _ _ _ _.
Obligation Tactic := intros int E.
Next Obligation. eauto. Qed.
Next Obligation. destruct (eaxiom E) as [ ea eaxiom ]. eauto. Qed.
Next Obligation. destruct (eaxiom E) as [ ea eaxiom ]. eauto. Qed.
Next Obligation. destruct (ecut E) as [ ec ecut ]. destruct (econji E) as [ eci econji ]. destruct (econje1 E) as [ ece1 econje1 ]. destruct (econje2 E) as [ ece2 econje2 ]. destruct (euniimpi E) as [ euii euniimpi ]. destruct (euniimpe E) as [ euie euniimpe ]. eexists. intros. apply euniimpi. intros. eapply ecut; [ apply econji; [ apply econje2 | apply econje1 ] | ]. apply euniimpe. eauto. Qed.
Next Obligation.
 exists (fun p => p).
  destruct (eaxiom E) as [ ea eaxiom ]. eauto.
  intros _. exists (fun p => p); reflexivity.
Qed.

Program Definition ef_comp {int : Prop} {E1 E2 E3 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) (G : EvidencedFrameMorphism int E2 E3) : EvidencedFrameMorphism int E1 E3
:= evidenced_frame_morphism int E1 E3 (fun p => Convert G (Convert F p)) _ _ _ _ _.
Obligation Tactic := intros int E1 E2 E3 F G.
Next Obligation. intro. edestruct (conevidence F) as [ cef conevidencef ]. edestruct (conevidence G) as [ ceg conevidenceg ]. eauto. Qed.
Next Obligation. destruct (contop F) as [ ctf contopf ]. destruct (contop G) as [ ctg contopg ]. destruct (ecut E3) as [ ec3 ecut3 ]. edestruct (conevidence G) as [ ceg conevidenceg ]. eexists. eapply ecut3; [ apply contopg | ]. eauto. Qed.
Next Obligation. destruct (conconj F) as [ ccf conconjf ]. destruct (conconj G) as [ ccg conconjg ]. destruct (ecut E3) as [ ec3 ecut3 ]. edestruct (conevidence G) as [ ceg conevidenceg ]. eexists. intros. eapply ecut3; [ apply conconjg | ]. eauto. Qed.
Next Obligation. destruct (conuniimp F) as [ cuif conuniimpf ]. destruct (conuniimp G) as [ cuig conuniimpg ]. destruct (ecut E3) as [ ec3 ecut3 ]. destruct (econji E3) as [ eci3 econji3 ]. destruct (econje1 E3) as [ ece13 econje13 ]. destruct (econje2 E3) as [ ece23 econje23 ]. destruct (euniimpi E3) as [ euii3 euniimpi3 ]. destruct (euniimpe E3) as [ euie3 euniimpe3 ]. edestruct (conevidence G) as [ ceg conevidenceg ]. eexists. intros. eapply ecut3; [ | apply conevidenceg; apply conuniimpf ]. eapply ecut3; [ | apply conuniimpg ]. apply euniimpi3. intros ? [ ? [ ? ? ? ] ? ]. subst. eapply ecut3; [ apply econji3; [ apply econje23 | apply econje13 ] | ]. apply euniimpe3. eauto. Qed.
Next Obligation.
 destruct (conprop F) as [ f [ e2 [ e2' ef ] ] conpropf ]. destruct (conprop G) as [ g [ e3 [ e3' eg ] ] conpropg ]. destruct (ecut E3) as [ ec3 ecut3 ]. exists (fun p3 => f (g p3)).
  edestruct (conevidence G) as [ ceg conevidenceg ]. edestruct (conevidence G) as [ ceg' conevidenceg' ]. eexists. eexists. intro. split.
   eapply ecut3; [ apply eg | ]. apply conevidenceg. apply ef.
   eapply ecut3; [ | apply eg ]. apply conevidenceg'. apply ef.
  intro i. destruct conpropf as [ finv finvf ffinv ]; try assumption. destruct conpropg as [ ginv ginvg gginv ]; try assumption. clear i. exists (fun p => ginv (finv p)).
   change ((fun p => p) = (fun p => f ((fun p => g (ginv p)) (finv p)))). rewrite <- ginvg. assumption.
   change ((fun p => p) = (fun p => ginv ((fun p => finv (f p)) (g p)))). rewrite <- ffinv. assumption.
Qed.

Definition EvidencedFrameRefines {int : Prop} {E1 E2 : EvidencedFrame} (F G : EvidencedFrameMorphism int E1 E2) : Prop
:= exists e2 : Evidence E2, forall p1 : PROP E1, Evidences E2 (Convert F p1) e2 (Convert G p1).


(** Categories EF_int / EF_ext *)


Program Definition EvidencedFrameCategory (int : Prop) : LocallyPreorderedBicategory
:= locally_preordered_bicategory EvidencedFrame (EvidencedFrameMorphism int) (@EvidencedFrameRefines int) (ef_id int) (@ef_comp int) _ _ _ _ _ _.
Obligation Tactic := intros int; unfold EvidencedFrameRefines.
Next Obligation. intros E1 E2 F. destruct (eaxiom E2) as [ ea2 eaxiom2 ]. eauto. Qed.
Next Obligation. intros E1 E2 F G H [ ? ? ] [ ? ? ]. destruct (ecut E2) as [ ec2 ecut2 ]. eexists. intro p1. apply ecut2 with (Convert G p1); auto. Qed.
Next Obligation. simpl. intros E1 E2 E3 F F' G G' [ ? ? ] [ ? ? ]. destruct (ecut E3) as [ ec3 ecut3 ]. edestruct (conevidence G) as [ ceg conevidenceg ]. eexists. intro p1. apply ecut3 with (Convert G (Convert F' p1)); auto. Qed.
Next Obligation. simpl. intros E1 E2 F. destruct (eaxiom E2) as [ ea2 eaxiom2 ]. eauto. Qed.
Next Obligation. simpl. intros E1 E2 F. destruct (eaxiom E2) as [ ea2 eaxiom2 ]. eauto. Qed.
Next Obligation. simpl. intros E1 E2 E3 E4 F G H. destruct (eaxiom E4) as [ ea4 eaxiom4 ]. eauto. Qed.

