Set Implicit Arguments.
Set Contextual Implicit.

Require Import Utf8.
Require Export Relation_Definitions.
Require Import Sets.Ensembles.
Require Import EF.Categories.
Require Import EF.EvidencedFrames.
Require Import EF.ImplicativeAlgebras.

(** * UEF: From Implicative Algebras to Evidenced Frames *)

(** ** Definition *)
Section UEF.
  Context `{IA:ImplicativeAlgebra}.

  (** *** Structure *)
  
  Definition IAPROP:=X.
  Definition IAEvidence:= {x :X | separator x }.
  Definition GetEvidence:IAEvidence -> X:=fun x => proj1_sig x. 
  Coercion GetEvidence: IAEvidence >-> X.
  Notation "ι( x )":=(GetEvidence x).
  
  Definition realizes:  IAPROP -> IAEvidence -> IAPROP -> Prop:=
    fun φ e θ => ι(e) ≤ arrow φ θ.

  
  Notation "e ⊩ φ1 ⇒ φ2":=(realizes φ1 e φ2) (at level 50).

  Lemma beta_sep: forall f a, (λ- f) ∈ʆ → a∈ʆ → f a ∈ʆ.
  Proof.
    intros f a Hf Ha.
    eapply up_closed.
    apply betarule.
    apply app_closed;assumption.
  Qed.

  (** Notations from IAs *)


  Notation "[ t ] u":= (@trm_app X (t) u ) (at level 69, right associativity).
  Notation "$ n":= (@trm_bvar X n) (at level 69, right associativity).
  Notation "λ+ t":= (@lam X 0 t) (at level 69, right associativity).

  Notation "[ n ~> a ] t":=(@sub X t n a) (at level 69).
  

  Notation "a × b":=(prodt a b) (at level 69).
  Notation "[∀] a":=(forallt a) (at level 69).


  (** Tactics *)
  
   Ltac autoev:=
    repeat(
        match goal with
          | x:Evidence |- _ =>  destruct x as (x,?H)
        end
      );simpl.

  Ltac trm_sep:=  repeat apply app_closed;try apply sep_S;try apply sep_K.
  Ltac realizer t:=
        apply up_closed with (translate t);[|trm_sep]. 

  Ltac rw_sub:=repeat (repeat rewrite sub_lam;repeat rewrite sub_app);
    repeat rewrite sub_eq; repeat (rewrite sub_neq;[|auto]);repeat rewrite sub_cste.

  Ltac rw_translate:=
    repeat (repeat rewrite translate_app;repeat rewrite translate_cvar).
  
  Ltac try_beta:= auto_meet_intro;
                  try (apply adj_imp; eapply ord_trans;[apply translate_beta|]; rw_sub;rw_translate).

  Ltac auto_real:=  repeat try_beta; simpl; adjunction_mon.

  Ltac insep a:= destruct a; simpl;assumption.
  
  (** *** Components *)

  (** **** Reflexivity *)
  Definition id:IAEvidence:=
    exist _ Id sep_Id.
  
  Lemma ax_id: forall (φ:IAPROP), id ⊩ φ ⇒ φ.
  Proof.
    intros φ.
    auto_meet_elim_trans.
  Qed.


  (** **** Transitivity *)
  Program Definition comp (a b:IAEvidence):IAEvidence := exist _ (λ- (fun (x:X) => ι(b) @(ι(a)@x))) _.
  Obligation Tactic := intros a b.
  Next Obligation.
    apply (beta_sep (fun y => λ- (fun x => ι(b)@(y@x))) a);try assumption.
    apply (beta_sep (fun z => λ- (fun y => λ- (fun x => z@(y@x)))) b);try assumption.
    realizer (λ+ λ+ λ+ ([$2] ([$1] $0))).
    auto_real. intros. now apply adjunction.
    insep b. insep a. 
  Qed.
    
  Lemma ax_comp: forall φ1 φ2 φ3 : IAPROP, forall e12 e23 : IAEvidence,
        e12 ⊩ φ1 ⇒ φ2  ->  e23 ⊩ φ2 ⇒ φ3  → (comp e12 e23) ⊩ φ1 ⇒ φ3.
  Proof.
    intros φ1 φ2 φ3 e12 e23 H12 H23.
    apply adjunction,beta_red,adjunction.
    transitivity (arrow φ2 φ3).
    exact H23. 
    apply arrow_mon_l.
    now apply adjunction.
  Qed.

  
  (** **** Top *)
  Definition top_φ:IAPROP:=top.
  Definition tt:IAEvidence:=id.
  
  Lemma ax_true : forall φ : IAPROP, tt ⊩ φ ⇒ top_φ.
  Proof.
    intros φ.
    auto_meet_elim_trans.
    apply arrow_mon_r.
    apply top_max.
  Qed.

  (** **** Bottom *)
  Definition bot_φ : IAPROP:=bot.
  Definition ff : IAEvidence:=id.

  Lemma ax_false : forall φ : IAPROP, ff ⊩ bot_φ ⇒ φ.
  Proof.
    intros φ.
    auto_meet_elim_trans.
    apply arrow_mon_l.
    apply bot_min.
  Qed.
  
    
  (** **** Conjunction *)

  Definition and_φ := fun x y =>  x × y. 
  Program Definition paire (a b : IAEvidence) : IAEvidence := exist _ (λ- (fun z:X => pair (ι(a)@z) (ι(b)@z))) _.
  Next Obligation.
    apply (beta_sep (fun y=>λ- (λ z : X, pair (ι(a) @ z) (y @ z))) ι(b));intuition.
    apply (beta_sep (fun x => λ-(fun y=>λ- (λ z : X, pair (x @ z) (y @ z)))) a);intuition.
    realizer (λ+ λ+ λ+ λ+ ([[$0] ([$3] $1)] ([$2] $1))).
    auto_real. intros; now apply adjunction. 
    insep a. insep b.
  Qed.
  
  Obligation Tactic := idtac.
  Program Definition fste : IAEvidence := exist _ (λ-(fun x => x @ proj1)) _.
  Next Obligation.
    realizer (λ+ [$0] (λ+ λ+ $1)).
    try_beta. apply app_mon_r;auto_real. 
  Qed.
    
  Program Definition snde : IAEvidence := exist _ (λ-(fun x => x @ proj2)) _.
  Next Obligation.
    realizer (λ+ [$0] (λ+ λ+ $0)).
    try_beta. apply app_mon_r;auto_real. 
  Qed.

  Lemma intro_and : forall φ φ1 φ2 e1 e2,
        e1 ⊩ φ ⇒ φ1  ->  e2 ⊩ φ ⇒ φ2  → (paire e1 e2) ⊩ φ ⇒ (and_φ φ1 φ2).
  Proof.
    intros φ φ1 φ2 (e1,S1) (e2,S2) H1 H2.
    apply adjunction,beta_red,type_pair;now apply adjunction.
  Qed.
    
  Lemma elim1_and : forall φ1 φ2 : IAPROP, fste ⊩ (and_φ φ1 φ2) ⇒ φ1 .
  Proof.
    intros φ1 φ2.
    now apply adjunction,beta_red,(type_proj1  _ φ2).
  Qed.    
    
  Lemma elim2_and : forall φ1 φ2 : IAPROP, snde ⊩ (and_φ φ1 φ2) ⇒ φ2 .
  Proof.
    intros φ1 φ2.
    now apply adjunction,beta_red,(type_proj2 φ1).
  Qed.
    

  (** **** Implication *)

  Definition imp_φ : IAPROP -> (IAPROP -> Prop) -> IAPROP:=
    fun x y => arrow x (meet_set y).

  (* a x b ↦ e   => a ↦ b ↦ c*)
  Program Definition lambdae (x : IAEvidence) : IAEvidence := exist _ (λ- (fun x1 => λ- (fun x2 => (proj1_sig x)@(pair x1 x2)))) _.
  Next Obligation.
   intros (x,Hx).
   apply (beta_sep (fun x =>  λ- (λ x1 : X, λ- (λ x2 : X, x @ pair x1 x2))) x);intuition.
   realizer (λ+ λ+ λ+ ([$2] (λ+ [[$0] $2] $1 ))).
   do 3 try_beta;subst. apply app_mon_r;auto_real. intros;now apply adjunction. 
  Qed.

  (* ((a↦b) x a)↦ b*)
  Program Definition evale : IAEvidence := exist _ (λ- (fun x => x@(λ- (fun y => λ- (fun z => z@y))))) _.
  Next Obligation.
    realizer (λ+ [$0] λ+ λ+ [$0] $1).
    try_beta;subst. apply app_mon_r;auto_real. intros;now apply adjunction. 
  Qed.

  
  Lemma intro_imp : forall (φ φ1: IAPROP) (φ':IAPROP → Prop), forall e : IAEvidence,
        (forall (φ2:IAPROP), φ' φ2 → e ⊩ (and_φ φ φ1) ⇒ φ2) -> lambdae e ⊩ φ ⇒ (imp_φ φ1 φ').
  Proof.
    intros φ φ1 φ' (e,S) H.
    apply adjunction,beta_red; auto_meet_elim_trans.
    apply arrow_mon_r. apply meet_intro.
    intros ψ Phi; apply adjunction.
    transitivity (arrow (and_φ φ φ1) ψ).
    - now apply H.
    - now apply arrow_mon_l, type_pair.
  Qed.
  
  Lemma elim_imp : forall (φ1:IAPROP) (φ:IAPROP→Prop) (φ2 : IAPROP),
      φ φ2 → evale ⊩ (and_φ φ1 (imp_φ φ1 φ)) ⇒ φ2.
  Proof.
    intros φ φ1 φ2 Phi.
    apply adjunction,beta_red,adjunction.
    auto_meet_elim_trans.
    apply arrow_mon_l.
    do 2 (apply adjunction,beta_red).
    apply adjunction,arrow_mon_r.
    now apply meet_elim.
  Qed.

  
  (** *** Theorem VI.5 : UEF is an evidenced frame *)
  
  Definition UEF :=
    evidenced_frame IAPROP IAEvidence realizes top_φ and_φ imp_φ
            (ex_intro _ id ax_id) (ex_intro _ comp ax_comp) (ex_intro _ tt ax_true)
            (ex_intro _ paire intro_and) (ex_intro _ fste elim1_and) (ex_intro _ snde elim2_and)
            (ex_intro _ lambdae intro_imp) (ex_intro _ evale elim_imp).

  

End UEF.


(** ** Functoriality of UEF *)

Definition uef (A : ImplicativeAlgebraObject) : EvidencedFrame
:= @UEF (IASet A) (IAOrder A) (IALattice A) (IAStructure A) (IAAlgebra A).

Program Definition uef_morphism {int : Prop} {A1 A2 : ImplicativeAlgebraObject} (F : ImplicativeAlgebraMorphism int A1 A2) : EvidencedFrameMorphism int (uef A1) (uef A2)
  := evidenced_frame_morphism int (uef A1) (uef A2) (IAMap F) _ _ _ _ _.
Next Obligation.
  destruct F;simpl in *. rename IAMap into F.
  destruct e1 as (e,He).
  pose (id:=(@Id _ _  _ (IAStructure A1)) ).
  specialize (iambinary id sep_Id).
  pose (s:=(IAapp ( ⊓ (λ a2 : IASet A2,
                    ∃ a1 a1' a1'' : IASet A1,
                      IAOrd A1 id (a1 ↦ a1' ↦ a1'') ∧ F a1 ↦ F a1' ↦ F a1'' = a2)) (F e))).
  assert (Hs:IASeparator A2 s).
  apply app_closed;[apply iambinary|apply (iamsep _ He)].
  exists (exist _ s Hs).
  intros a b H.
  unfold realizes in *;simpl in *.
  apply adj_app.
  apply meet_elim.
  exists e;exists a;exists b;split;trivial.
  transitivity  (e ↦ e);[apply meet_elim;exists e;trivial|  apply arrow_mon_r,H].
Qed.
Next Obligation.
  pose (top:= (@top _ _ (IALattice A1))).
  assert (unary:=(iamunary F (⊓ emptyset ↦ top))).
  destruct F;simpl in *. rename IAMap into F.
  pose (a:= ⊓ (λ a2 : IASet A2,
              ∃ a1 a1' : IASet A1,
                IAOrd A1 ((⊓ emptyset) ↦ top) (a1 ↦ a1') ∧ F a1 ↦ F a1' = a2)).

  pose (b:= (⊓ (λ a2 : IASet A2,
                  ∃ as1 : IASet A1 → Prop,
                    (⊓ (λ a3 : IASet A2, exists2 a1 : IASet A1, as1 a1 & F a1 = a3)) ↦ F (⊓ as1) = a2))).
  pose (s:=(IAapp (IAapp (IAabs (fun y => IAabs (fun z => IAabs (fun x:IASet A2 => IAapp y (IAapp z x))))) a ) b)).
  pose (id:=(@Id _ _  _ (IAStructure A1)) ).
  assert (Hs: IASeparator _ s).
  1:{
    repeat (apply app_closed);trivial.
    realizer (λ[A2]+ λ+ λ+ ([$2] ([$1] $0))).
    apply unary. apply up_closed with id;[|apply sep_Id].
    transitivity (top ↦ top);[apply meet_elim;exists top;reflexivity|apply arrow_mon_l,top_max].
  }
  exists (exist _ s Hs).
  do 3 (apply adjunction, beta_red).
  apply adjunction.
  transitivity ((F (⊓ emptyset)) ↦ (F top)).
  apply meet_elim. do 2 eexists;split;reflexivity.
  apply arrow_mon_l,adjunction.
  transitivity  ((⊓ (λ a3 : IASet A2, exists2 a1 : IASet A1,emptyset a1 & F a1 = a3)) ↦ F (⊓ emptyset)).
  apply meet_elim. exists emptyset;split;reflexivity.
  apply arrow_mon_l.
  apply meet_intro. intros x (z,Ha,Hx). contradict Ha.
Qed.
Next Obligation.
  simpl.
  assert (Unary:=iamunary_real F).
  destruct F;simpl in *. rename IAMap into F.
  pose (sarr:= (⊓ (λ a2 : IASet A2, ∃ a1 a1' : IASet A1, (F a1 ↦ F a1') ↦ F (a1 ↦ a1') = a2))).
  pose (sarr':=(⊓ (λ a2 : IASet A2, ∃ a1 a1' : IASet A1, F (a1 ↦ a1') ↦ F a1 ↦ F a1' = a2))).
  pose (smeet:=( (⊓ (λ a2 : IASet A2, ∃ as1 : IASet A1 → Prop,
    (⊓ (λ a3 : IASet A2, exists2 a1 : IASet A1, as1 a1 & F a1 = a3)) ↦ F (⊓ as1) =        a2)))).
  pose (t:= IAapp (IAapp (IAapp (IAabs (fun sarr => (IAabs (fun smeet => IAabs (fun sarr'=> IAabs (fun x => IAapp x (IAabs (fun x1 => IAabs (fun x2 => IAapp smeet (IAapp sarr(IAabs (fun x =>
             (IAapp (IAapp sarr' (IAapp (IAapp sarr' x) x1 )) x2))))))))))))) sarr) smeet) sarr').
  assert (IASeparator A2 t).
  - repeat (apply app_closed);try assumption.
    realizer (λ[A2]+ λ+ λ+ λ+ ([$0] (λ+ λ+ ([$4] ([$5]  (λ+ ([[$4] ([([$4] $0)] $2)] $1 ))))))).
  - exists (exist _ t H). intros p1 p2.
    do 2 (apply adj_app).
    do 3 (apply beta_red,adj_imp).
    apply beta_red.
    apply adj_app. auto_meet_elim_risky.
    apply arrow_mon_l.
    apply adj_imp,beta_red,adj_imp,beta_red.
    apply adj_app.  auto_meet_elim_trans. apply arrow_mon_l. 
    auto_meet_intro. intros y (a,(c,Hc),Ha);subst.
    apply adj_app.
    transitivity (( F (p1 ↦ p2 ↦ c) ↦ F c) ↦ (F ((p1 ↦ p2 ↦ c )↦  c))).
    auto_meet_elim_risky. eexists;reflexivity.
    apply arrow_mon_l.
    apply adj_imp,beta_red,adj_app,adj_app. 
    transitivity ((F ( p2 ↦  c)) ↦ ((F p2)↦ (F c))).
    apply meet_elim;eexists;eexists. reflexivity.
    apply arrow_mon_l,adj_app,adj_app.
    apply meet_elim;eexists;eexists;reflexivity.
Qed.
Next Obligation.
  assert (unary:=iamunary F _ sep_Id).
  destruct F;simpl in *. rename IAMap into F.
  pose (sarr:= (⊓ (λ a2 : IASet A2, ∃ a1 a1' : IASet A1, (F a1 ↦ F a1') ↦ F (a1 ↦ a1') = a2))).
  pose (sunary:=(⊓ (λ a2 : IASet A2, ∃ a1 a1' : IASet A1, IAOrd A1 (@Id _ _ _ (IAStructure A1)) (a1 ↦ a1') ∧ F a1 ↦ F a1' = a2))).
  pose (smeet:=( (⊓ (λ a2 : IASet A2, ∃ as1 : IASet A1 → Prop,
    (⊓ (λ a3 : IASet A2, exists2 a1 : IASet A1, as1 a1 & F a1 = a3)) ↦ F (⊓ as1) =        a2)))).
  pose (t:= IAapp (IAapp (IAapp (IAabs (fun sunary =>  IAabs (fun smeet => IAabs (fun sarr => IAabs (fun x => IAapp sunary (IAapp smeet (IAapp sarr  x) )))))) sunary) smeet) sarr).
  assert (IASeparator A2 t).
  - repeat (apply app_closed);trivial.
    realizer (λ[A2]+ λ+ λ+ λ+ ([$3] ([$2] ([$1] $0)))).
  - exists (exist _ t H). intros p1 S.
    do 2 (apply adj_app).
    do 3 (apply beta_red,adj_imp).
    apply  beta_red.
    apply adj_app.
    transitivity ((F (@meet_set _ _ (IALattice A1) (fun a => exists p2, S p2 /\ a = p1 ↦ p2)))↦ (F (@imp_φ _ _ _ (IAStructure A1) p1 S))) .
    + apply meet_elim;eexists;eexists;split;[|reflexivity].
      apply adj_imp,beta_red. apply arrow_meet.
    + apply arrow_mon_l. apply adj_app.
      auto_meet_elim_trans. apply arrow_mon_l.
      auto_meet_intro. intros x (a,(x2,(H2,H1)),Hx);subst.
      apply adj_app.
      transitivity ((F p1 ↦ F x2) ↦ F(p1 ↦ x2)).
      apply meet_elim;exists p1;exists x2;reflexivity.
      apply arrow_mon_l.
      unfold imp_φ.
      eapply ord_trans;[apply arrow_meet|].
      apply meet_elim.
      eexists;split. exists x2;trivial. reflexivity.
Qed.
Next Obligation.
  simpl.
  destruct F;simpl;rename IAMap into F.
  destruct iamdense as (f,(Hf1,Hf2),Hint).
  exists f.
  - exists (exist _ _ Hf1). exists (exist _ _ Hf2).
    intros p. split;apply meet_elim;exists p;reflexivity.
  - intro Hi. destruct (Hint Hi) as (finv, Hinv1,Hinv2).
    exists finv;assumption. 
Qed.


(** UEF extends to a pseudofunctor between IA_int/IA_ext and EF_int/EF_ext *)

Program Definition UEFFunctor (int : Prop) : Pseudofunctor (ImplicativeAlgebraCategory int) (EvidencedFrameCategory int)
  := pseudofunctor (ImplicativeAlgebraCategory int) (EvidencedFrameCategory int) uef (@uef_morphism int) _ _ _.
Next Obligation.
  simpl in *;unfold EvidencedFrameRefines,ImplicativeAlgebraRefines in *.
  pose (e:=(⊓ (λ a2 : IASet o1', ∃ a1 : IASet o1, IAMap f1 a1 ↦ IAMap f1' a1 = a2))).
  exists (exist _ e H).
  intros;simpl.
  apply meet_elim;eexists;reflexivity.
Qed.
Next Obligation.
  split; exists (exist _ _ sep_Id);intros;  apply meet_elim;eexists;reflexivity.
Qed.
Next Obligation.
  split; exists (exist _ _ sep_Id);intros;  apply meet_elim;eexists;reflexivity.
Qed.
Arguments UEFFunctor : clear implicits.




(** * FIA: from Evidenced Frames to Implicative Algebras *)

(** ** Definition *)

Section FIA.
  Context `{EF:EvidencedFrame}.
  
  Definition PHI:=PROP EF.
  Definition E:=Evidence EF.
  Definition real:=Evidences EF.
  
  Ltac destructuniimp :=
    destruct (euniimpi EF) as (elam,Hlam);
    destruct (euniimpe EF) as (eeval,Heval).

  Ltac destructconj :=
    destruct (econji EF) as (epair,Hpair);
    destruct (econje1 EF) as (efst,Hfst);
    destruct (econje2 EF) as (esnd,Hsnd).
  
  Ltac destructbase :=
    destruct (eaxiom EF) as (eax,Hax);
    destruct (ecut EF) as (ecut,Hcut);
    destruct (etopi EF) as (ett,Htop).

  Ltac destructEF :=
    destructuniimp;destructconj;destructbase.
  

  Definition Pi (P:PHI -> Prop):PHI := euniimp EF (etop EF) P.
  Lemma ePi: exists e, forall (P:PHI -> Prop) p, P p -> real (Pi P) e p.
  Proof.
    destructEF.
    eexists. intros P p Hp.
    eapply Hcut;[|apply Heval].
    2:{exact Hp. }
    apply Hpair;[apply Htop|apply Hax].
  Qed.
  
  Lemma eforall: exists (efa:E -> E), forall p (P:PHI -> Prop) e, (forall p', P p' -> real p e p') -> real p (efa e) (Pi P).
  Proof.
    destructEF.
    eexists. intros p P e He.
    apply Hlam. intros p' Hp'.
    eapply Hcut;[apply Hfst|].
    now apply He.
  Qed.

  Ltac destructforall:=
    destruct ePi as (ePi, HPi);
    destruct eforall as (efa,Hfa).

  Lemma Pi_mon : exists e, forall P P', P ⊆ P'->  real (Pi P') e (Pi P).
  Proof.
    destructforall;destructbase.
    eexists;intros P P' H.
    apply Hfa;intros p' Hp'.
    apply HPi. now apply H.
  Qed.

  Notation " 'Π[' a ']' p " := ( Pi (fun x => ∃ a, x= p)) (at level 60).
  
  

  

  
  Lemma swap:  exists e, forall a b, real (econj _ a b) e (econj _ b a).
  Proof.
    destructEF. eexists.
    intros a b. apply Hpair;[apply Hsnd|apply Hfst].
  Qed.

  Lemma conj_mon: ∃ f, forall a a' b b' ea eb, real a ea  a' -> real b  eb  b' -> real (econj EF a b) (f ea eb) (econj EF a' b').
    destructbase;destructconj.
    eexists;intros a a' b b' ea eb Ha Hb.
    apply Hpair. eapply Hcut;[apply Hfst|apply Ha].
    eapply Hcut;[apply Hsnd|apply Hb].
  Qed.

  
  Definition singleton: PHI -> (PHI -> Prop):=
    fun a b => a = b.
  Definition imp a b:=euniimp _ a (singleton b).

  Infix "⊃":=imp (right associativity, at level 25).
  Lemma impeval: exists e, forall p1 p2 : PHI, real (econj EF p1 (imp p1 p2)) e p2.
  Proof.
    destructuniimp.
    exists eeval. intros. 
    apply Heval. reflexivity.
  Qed.


  Lemma implam: exists f, forall (p1 p2 p3: PHI) e, (real (econj EF p1 p2) e p3)
        → real p1 (f e) (imp p2 p3).
  Proof.
    destructuniimp.
    exists elam. intros. 
    apply Hlam. intros. rewrite <- H0. assumption. 
  Qed.
  
  Ltac destructimp :=
    destruct (implam) as (elam,Hlam);
    destruct (impeval) as (eeval,Heval).

  
   Lemma impPi: exists e, forall a B, real (Pi (λ x : PHI, ∃ b , B b ∧ x = a ⊃ b)) 
    e (a ⊃ Pi (λ x : PHI, ∃ b , B b ∧ x = b)).
   Proof.
     destructbase; destructimp; destructforall.
     destruct conj_mon as (f,Hmon).
     destruct swap as (swap,Hswap).
     eexists; intros a B.
     apply Hlam,Hfa; intros p (b,(Hb,Hp));subst.
     eapply Hcut;[|apply Heval].
     eapply Hcut;[apply Hswap|].
     apply Hmon;[apply Hax|].
     apply HPi. exists b;split;trivial.
   Qed.

   Lemma imp_mon: ∃ f, forall a a' b b' ea eb, real a' ea  a -> real b  eb  b' -> real (a ⊃ b) (f ea eb) (a' ⊃ b').
     destructbase;destructimp;destruct conj_mon as (emon,Hmon);destruct swap as (swap,Hswap).
     eexists;intros a a' b b' ea eb Ha Hb.
     eapply Hlam,Hcut;[|apply Hb].
     eapply Hcut;[apply Hmon;[apply Hax|apply Ha]|].
     eapply Hcut;[apply Hswap|apply Heval].
   Qed.


  (*******************************************)
  (* Definition of the Implicative structure *)
  (*******************************************)


  
  (* Infix "⊆":=(Included X) (at level 75). *)

  Definition subset_refl `{X:SET}:= λ (x : Ensemble X) (x0 : X) (H : In X x x0), H.
  Definition subset_antisym `{X:SET}: forall x y,  x ⊆ y ->  y ⊆ x -> x = y  :=
    λ (x y : Ensemble X) (H : x ⊆ y) (H0 : y ⊆ x), Extensionality_Ensembles X x y (conj H H0).
  Definition subset_trans `{X:SET}: forall x y z,  x ⊆ y ->  y ⊆ z -> x ⊆ z  :=
    λ (x y z : Ensemble X) (H : x ⊆ y) (H0 : y ⊆ z) (x0 : X) (H1 : In X x x0), H0 x0 (H x0 H1).

  
  Definition supset_refl `{X:SET}:= λ (x : Ensemble X) (x0 : X) (H : In X x x0), H.
  Definition supset_antisym `{X:SET} : forall x y,  x ⊇ y ->  y ⊇ x -> x = y :=
    λ (x y : Ensemble X) (H : y ⊆ x) (H0 : x ⊆ y), Extensionality_Ensembles X x y (conj H0 H).
  Definition supset_trans `{X:SET}: forall x y z,  x ⊇ y ->  y ⊇ z -> x ⊇ z  := 
    λ (x y z : Ensemble X) (H : x ⊇ y) (H0 : y ⊇ z) (x0 : X) (H1 : In X z x0), H x0 (H0 x0 H1).

     
  Inductive A0:=
  |ax_phi : PHI -> A0
  |ax_arrow : (PHI -> Prop) -> A0 -> A0.

  Notation " P ⇀ a" := (ax_arrow P a) (at level 72).

  Inductive ord0 : A0 -> A0 -> Prop:=
  |ord0_phi : forall p, ord0 (ax_phi p) (ax_phi p)
  |ord0_arrow : forall a a' (p p':Ensemble PHI), ord0 a a' -> p ⊆ p' -> ord0 (p ⇀ a) (p' ⇀ a').

  Notation " a <0< b" := (ord0 a b) (at level 72).

  Lemma ord0_trans:
    forall a b c, a <0<b -> b<0<c -> a<0<c.
  Proof.
    intros a;induction a;intros b c Ha Hb.
    inversion Ha;subst;trivial.
    inversion Hb;subst;trivial.
    inversion Ha;subst;trivial.
    apply ord0_arrow. now apply IHa with a0.
    now apply subset_trans with p.
  Qed.
    
  Fixpoint injec0 (a0 : A0): PHI:=
      match a0 with
      | ax_phi p => p
      | ax_arrow P a0 => imp (Pi P) (injec0 a0)
      end.

  
  Definition up_closed0 (P: A0 -> Prop) :=
    forall a b, P a -> a <0< b -> P b.

  Definition A:= { P : A0 -> Prop | up_closed0 P }.

  Definition proj:A -> (A0 -> Prop):=
    fun x => proj1_sig x.

  Coercion proj: A >-> Funclass.


  Definition ordA :  A → A → Prop:= supset.
  

  Definition injec (a:A):=
    fun x:PHI => exists y:A0, a y /\ x = injec0 y.

  Definition closure (P:PHI -> Prop):=
    fun Q:PHI-> Prop => P ⊆ Q.

  Definition prearrow0 (a b:A):A0 -> Prop :=
    fun x => exists s ß, x = (s ⇀ ß) /\ (closure (injec a)) s /\ b ß.


  Lemma prearrow0_upclosed0: forall (a b:A),
      up_closed0 (prearrow0 a b).
  Proof.
    intros (A,Ha) (B,Hb) x y (s,(ß,(Hx,(Hs,Hß)))) Hord.
    unfold prearrow0 in *.
    rewrite Hx in *.
    inversion Hord;subst.
    exists p'; exists a'; repeat split;trivial.
    - unfold closure,injec;simpl.
      apply subset_trans with s;[apply Hs|trivial].
    - simpl; now apply (Hb ß a').
  Qed.

(** *** (A,⊇) is a complete lattice *)
  
  
  #[refine] Global Instance  Powerset_Rev_Order : @Order A:=
    { ord := supset}.
  Proof.
    - intros P Q H. assumption.
    - intros a b c. apply supset_trans.
  Defined.

   
  Definition preintersection_set (B:Ensemble (A)):=
    fun (x:A0) => ∀ b, B b → b x.

  Program Definition intersection_set (S : Ensemble A) : A := exist _ (preintersection_set S) _.
  Obligation Tactic := idtac.
  Next Obligation.
    intro S.
    unfold preintersection_set in *.
    intros a b Ha Hb c H. specialize (Ha c H).
    destruct c as (c,Hc);simpl in *.
    now apply (Hc a).
  Qed.

  
  Definition preunion_set  (B:Ensemble A) :=
    fun (x:A0) =>  ∃ b, B b ∧ b x.    

  Program Definition union_set (S : Ensemble A) : A := exist _ (preunion_set S) _.
  Next Obligation.
    intro S.
    unfold preunion_set in *.
    intros a b (c,(Hc,Ha)) Hb. 
    exists c. split;trivial.
    destruct c as (c,H);simpl in *.
    now apply (H a).
  Qed.
  

  Lemma intersection_set_lb :
    ∀ (S:Ensemble A) b , S b → (intersection_set S) ⊆ b.
  Proof.
    intros S b H x Hx.
    apply Hx,H.
  Qed.

  Lemma intersection_set_glb: 
    ∀ (S : Ensemble A) b , (∀ c , S c → b ⊆ c) → b ⊆ (intersection_set S).
  Proof.
    intros S b H x Hx c Hc.
    apply H;assumption.
  Qed.

  Lemma union_set_ub :
    ∀ (S:Ensemble A) b , S b → b ⊆ (union_set S).    
  Proof.
    intros S b H x Hx.
    exists b;split;assumption.
  Qed.
  
  Lemma union_set_lub :
    ∀ (S : Ensemble A) b , (∀ c , S c → c ⊆ b) → (union_set S) ⊆ b.
  Proof.
    intros S b H x [c [Hc Hx]].
    apply (H c Hc). assumption.
  Qed.


  Hint Resolve intersection_set_lb intersection_set_glb union_set_ub union_set_lub : sets.


  
  Global Instance  Powerset_CompleteLattice: @CompleteLattice _ (Powerset_Rev_Order)
    := {meet_set:=union_set ;join_set:=intersection_set;
        meet_elim:=union_set_ub; meet_intro:=union_set_lub;
        join_elim:=intersection_set_lb; join_intro:=intersection_set_glb;
       }. 
  
   (********************************)


  #[refine] Global Instance A_IS: 
    @ImplicativeStructure _ (Powerset_Rev_Order) (Powerset_CompleteLattice):=
    { arrow :=  λ a b : A, exist _  (prearrow0 a b) (prearrow0_upclosed0 (b:=b))}.
  Proof.
    - intros a a' b H x (s,(ß,(Hx,(Hs,Hß)))).
      exists s;exists ß; repeat split;trivial.
      eapply subset_trans;[|apply Hs].
      intros p (y,(Hy,Hp));subst. exists y;split;trivial; now apply H. 
    - intros a b b' H x (s,(ß,(Hx,(Hs,Hß)))).
      exists s; exists ß;repeat split;trivial; now apply H.
    - intros a B. split;intros x H;unfold In,prearrow0,preunion_set in *.
      + destruct H as (c,((d,(Hd,H)),Hc));subst.
        destruct Hc as (s,(ß,(Hx,(Hs,Hß)))).
        exists s;exists ß; repeat split; trivial.
        exists d;split;trivial.
      +  destruct H as (s,(ß,(Hx,(Hs,(b,(Hb,Hß)))))).
         exists (exist _  (prearrow0 a b) (prearrow0_upclosed0 (b:=b)));split.
         * exists b;auto.
         * rewrite Hx;simpl. exists s;exists ß; repeat split; trivial.
  Defined.

                                         


  Definition phi: A -> PHI :=
    fun a => Pi (injec a).

  Definition valid (p:PHI) := exists e:E, real (etop EF) e p.
  
  
  Definition impval a b:= valid a -> valid b.

  Definition is_evd a b:=exists e, real a e b.
  Infix "⊢ ":=is_evd (at level 27).

  Lemma entails_impval: forall a b, a ⊢ b -> impval a b.
  Proof.
    intros a b (e,H) (ea,Ha).
    destructbase. 
    exists (ecut ea e).
    eapply Hcut;[apply Ha|apply H].
  Qed.

  Ltac step Hcut a:= eapply (Hcut _ a).


  Lemma injec0_mon: forall a b, a <0< b -> ∃ e,real (injec0 a) e (injec0 b).
  Proof.
    destructEF. destruct imp_mon as (emon,Hmon),Pi_mon as (ePi,HPi).
    intros.
    induction H.
    eexists;intros.
    - apply Hax.
    - destruct IHord0. eexists. simpl. 
      apply Hmon. now apply HPi.
      apply H1.
  Qed.

  
  Lemma injec_mon: forall a b, a ≤ b -> (injec b) ⊆ (injec a).
  Proof.
     intros a b H x (y,(Hy,Hx)).
     exists y. split;trivial.
     apply (H y Hy).
  Qed.

   Lemma phi_mon: exists e, forall a b, a ≤ b ->  real (phi a) e (phi b).
     destructuniimp. destructbase. destruct swap as (eswap,Hswap).
     eexists. intros a b H.
     apply Hlam. intros.
     eapply Hcut. apply Hswap. apply Heval.
     now apply (injec_mon H).
   Qed.

 
  Lemma phi_Pi: ∃ e, forall B , real (phi (meet_set B)) e (Pi (fun x=> exists a, B a /\ x=phi a )).
  Proof.
    destructEF;destructforall;destruct phi_mon as (emon,Hmon).
    eexists. intros;apply Hfa;intros p [a [Ha Hp]];subst.
    apply Hmon. now apply meet_elim.
  Qed.


  Definition presing a:=fun (x:A0) => a <0< x.
  Program Definition sing (a0:A0): A := exist _ (presing a0) _.
  Next Obligation. intros a0 a b Ha H0. now apply ord0_trans with a. Qed.
    
  Lemma Pi_phi: ∃ e, forall B , real (Pi (fun x=> exists a, B a /\ x=phi a )) e (phi (meet_set B)).  
  Proof.
    destructEF;destructforall;destruct phi_mon as (emon,Hmon).
    eexists;intros;apply Hfa;intros p [x [Hx Hp]];subst.
    destruct Hx as [a [Ha Hx]].
    apply Hcut with (phi a);[apply HPi;exists a;split;trivial|].
    apply HPi. exists x;now split.
  Qed.    
    
  Lemma phi_arrow: ∃ e, forall a b, real (phi (arrow a  b)) e (imp (phi a) (phi b)).                           
  Proof.
    destructbase; destructimp; destructforall.
    destruct conj_mon as (f,Hmon).
    destruct swap as (swap,Hswap).
    unfold phi at 1,injec;unfold A_IS,arrow,prearrow0,impval;simpl.
    eexists;intros.
    eapply (Hcut _ (Pi (λ x, ∃ s ß (c:A), closure (injec a) s ∧ b ß ∧ x = injec0 (s ⇀ ß)))); simpl.
    - apply Hfa; intros p (P, (w,(HP,(Hw,(Hb,Hp)))));subst.
      apply HPi. exists (P ⇀ w). split;[|reflexivity]. exists P;exists w; repeat split;trivial. 
    - eapply (Hcut _ (Pi (λ x : PHI, ∃ (ß : A0), b ß ∧ x = imp (Pi (injec a)) ((injec0 ß))))).
      + apply Hfa;intros p (x, (w,Hw));subst.
        apply HPi. exists (injec a);exists x;repeat split;trivial. intros p H;exact H. 
      + eapply (Hcut _ (imp (Pi (injec a)) (Pi (λ x, ∃ ß : A0, b ß ∧ x =(injec0 ß)))));[|apply Hax].
        apply Hlam,Hfa; intros p (c,(Hc,Hp));subst.
        eapply Hcut;[|apply Heval]; eapply Hcut;[apply Hswap|];apply Hmon;[apply Hax|];
        apply HPi;exists c;split;trivial.
   Qed.

  
  
  Lemma arrow_phi: exists e, forall a b, real (phi a ⊃ phi b) e (phi (arrow a b)).
    destructbase; destructimp; destructforall;
    destruct imp_mon as (f,Hmon); destruct Pi_mon as (f',Hmon'); destruct swap as (swap,Hswap).
    eexists. intros.
    eapply (Hcut _ (Pi (λ x : PHI, (∃ s ß, closure (injec a) s ∧ b ß ∧ x = injec0 (s ⇀ ß))))); simpl.
    - eapply (Hcut _ (Pi (λ x : PHI, ∃ (ß : A0), b ß ∧ x = imp (Pi (injec a)) ((injec0 ß))))).
      + eapply (Hcut _ (imp (Pi (injec a)) (Pi (λ x, ∃ ß : A0, b ß ∧ x =(injec0 ß)))));[apply Hax|].
        apply Hfa; intros p (c,(Hc,Hp));subst.
        apply Hmon;[apply Hax|].
        apply HPi;exists c;split;trivial.
      + apply Hfa; intros p (P, (x,(HP,(Hx,Hp)))); subst.
        eapply (Hcut _ (Pi (λ x0 : PHI, ∃ ß : A0, b ß ∧ x0 = Pi P ⊃ injec0 ß)));
          [|apply HPi;exists x; split;trivial].
         eapply Hfa; intros p' (z,(Hz,Hp')); subst.
          eapply (Hcut _ (Pi (injec a) ⊃ injec0 z));[apply HPi;exists z;repeat split;trivial|].
          apply Hmon;[now apply Hmon'|apply Hax]. 
    - apply Hfa;intros p (P, ((s,(ß,(HP,(Hs,Hß)))),Hw)); subst. 
      apply HPi. exists s;exists ß; repeat split;trivial.
  Qed.
  
   
Lemma phiK:
     impval (Pi (fun x => exists a:A, x= Pi (fun y => exists b, y = (phi a) ⊃ (phi b) ⊃ (phi a)))) (phi K).
   Proof.
     apply entails_impval.
     destructEF. destructforall.
     destruct imp_mon as (emon,Hmon).
     destruct Pi_mon as (emon',Hmon').
     eexists.
     apply Hfa.
     intros. destruct H as (y,(Hy,Hp')). subst.
     unfold K in Hy. simpl in Hy.
     destruct Hy as (P,((a,Ha),Hy)).
     rewrite Ha in Hy. destruct Hy as (z,((b,Hz),Hy)). subst.
     destruct Hy as (s, (ß,(Hy,(Hs,Hß)))). subst.
     destruct Hß as (s', (ß',(Hß,(Hs',Hß')))). subst.
     simpl.
     eapply (Hcut _ (phi a ⊃ phi b ⊃ phi a)).
     - eapply (Hcut _  (Pi (λ y : PHI, ∃ b0 : A, y = phi a ⊃ phi b0 ⊃ phi a))).
       apply HPi;exists a;reflexivity.
       apply HPi;exists b;reflexivity.
     - apply Hmon. now apply Hmon'.
       apply Hmon. now apply Hmon'.
       apply HPi. exists ß';split;trivial.
   Qed.

   Lemma phiK_aux:
     valid (Pi (fun x => exists a, x= Pi (fun y => exists b, y = a ⊃ b ⊃  a))).
   Proof.
     destructEF. destructforall.
     exists (efa (efa (elam (elam (ecut efst esnd))))).
     apply Hfa. intros ?p' (?a,?Ha). subst. 
     apply Hfa. intros ?p' (?a,?Ha). subst. 
     apply Hlam. intros ?p' ?Ha. rewrite <- Ha. 
     apply Hlam. intros ?p' ?Ha. rewrite <- Ha0. 
     eapply Hcut. apply Hfst. apply Hsnd.
   Qed.

   
   Lemma validK: valid (phi K).
   Proof.
     apply phiK.
     destructimp. destructforall. destructbase.
     destruct phiK_aux as (eK,HK).
     eexists.
     apply Hfa. intros p' (a,Ha). subst.
     apply Hfa. intros p' (b,Hb). subst.
     eapply Hcut;[apply HK|].
     eapply Hcut. apply HPi. exists (phi a). reflexivity.
     apply HPi. exists (phi b). reflexivity. 
   Qed.

   Lemma phiS:
     (Π[ a] (Π[ b] (Π[ c] (phi a ⊃ phi b ⊃ phi c) ⊃ (phi a ⊃ phi b) ⊃ phi a ⊃ phi c))) ⊢ phi S.
   Proof.
     destructEF. destructforall.
     destruct imp_mon as (emon,Hmon).
     destruct Pi_mon as (emon',Hmon').
     destruct phi_arrow as (ephi,Hphi).
     destruct arrow_phi as (earr,Harr).
     eexists.
     apply Hfa.
     intros. destruct H as (y,(Hy,Hp')). subst.
     unfold S in Hy. simpl in Hy.
     destruct Hy as (P,((a,Ha),Hy)). rewrite Ha in Hy.
     destruct Hy as (z,((b,Hz),Hy)). subst.
     destruct Hy as (w,((c,Hw),Hz)). subst.
     destruct Hz as (s1, (ß1,(Hz,(Hs1,Hß1)))). subst.
     destruct Hß1 as (s2, (ß2,(Hß1,(Hs2,Hß2)))). subst.
     destruct Hß2 as (s3, (ß3,(Hß2,(Hs3,Hß3)))). subst.
     simpl.
     eapply (Hcut _ ((phi a ⊃ phi b ⊃ phi c) ⊃ (phi a ⊃ phi b) ⊃ phi a ⊃ phi c)).
     - eapply (Hcut _  (Π[b0] (Π[c0] (phi a ⊃ phi b0 ⊃ phi c0) ⊃ (phi a ⊃ phi b0) ⊃ phi a ⊃ phi c0))).
       apply HPi;exists a;reflexivity.
       eapply (Hcut _  (Π[c0] (phi a ⊃ phi b ⊃ phi c0) ⊃ (phi a ⊃ phi b) ⊃ phi a ⊃ phi c0)).
       apply HPi;exists b;reflexivity.
       apply HPi;exists c;reflexivity.
     - apply Hmon. eapply (Hcut _ (phi (arrow a (arrow b c)))). now apply Hmon'.
       eapply Hcut;[apply Hphi|].
       apply Hmon;[apply Hax |apply Hphi].
       eapply (Hcut _ ((phi (arrow a b)) ⊃ phi a ⊃ phi c)).
       eapply Hcut.
       apply Hmon. apply Hphi. apply Harr.
       apply Hmon;[apply Hax|apply Hphi].
       apply Hmon.
       + apply Hfa. intros p' (w, (Hw,Hp')). subst.
         apply HPi. apply Hs2. exists w;split;trivial.
       + apply Hmon.
         * apply Hfa. intros p' (w, (Hw,Hp')). subst.
           apply HPi. apply Hs3. exists w;split;trivial.
         * apply HPi. exists ß3;split;trivial.
   Qed.
     
     
   Lemma phiS_aux:
     valid (Pi (fun x => exists a, x= Pi (fun y => exists b, y =  Pi (fun z => exists c, z = (a ⊃ b ⊃ c) ⊃ (a ⊃ b) ⊃ a ⊃ c)))).
   Proof.
     destructEF. destructforall.   destruct impeval as (eval,Hev).
     exists (efa (efa (efa (elam (elam (elam (ecut
       (epair
           (ecut (epair esnd (ecut efst esnd)) eval)
          (ecut (epair esnd (ecut efst (ecut efst esnd))) eval)
       ) eval))))))). 
     do 3 (apply Hfa; intros ?p' (?a,?Ha); subst). 
     do 3 (apply Hlam; intros ?p' Hp'; unfold singleton in *; subst). 
     eapply Hcut. 2: { apply Hev. }
     apply Hpair.
     - eapply Hcut. 2: { apply Hev. }
       apply Hpair.
       + apply Hsnd.
       + eapply Hcut;[apply Hfst|apply Hsnd].
     - eapply Hcut. 2: { apply Hev. }
       apply Hpair.
         + apply Hsnd.
         + eapply Hcut;[apply Hfst|].
           eapply Hcut;[apply Hfst|apply Hsnd].
   Qed.

   
   
   Lemma validS: valid (phi S).
   Proof.
     destructimp. destructforall. destructbase.
     destruct phiS as (ephi,Hphi).
     destruct phiS_aux as (eS,HS).
     eexists.
     eapply Hcut;[|apply Hphi]. 
     apply Hfa. intros p' (a,Ha). subst.
     apply Hfa. intros p' (b,Hb). subst.
     apply Hfa. intros p' (c,Hc). subst.
     eapply Hcut;[apply HS|].
     eapply Hcut. apply HPi. exists (phi a). reflexivity.
     eapply Hcut. apply HPi. exists (phi b). reflexivity.
     apply HPi. exists (phi c). reflexivity. 
   Qed.
 

   
 (** *** Theorem VI.9 : FIA defines an implicative algebra *)
     
  #[refine] Global Instance FIA: 
    @ImplicativeAlgebra _ _  (Powerset_CompleteLattice) A_IS:=
    { separator := fun a => valid (phi a); sep_K:=validK; sep_S:=validS }.
  Proof.
    - intros a b (ea,Ha) (eab,Hab).
      destruct  (impeval) as (eval,Himpe),(econji EF) as (pair,Hconji),(ecut EF) as (comp,Hcut).
      assert (valid (phi (arrow a b))).
      exists eab;assumption.
      destruct H as (e,He).
      assert (valid (phi a ⊃ phi b)).
      destruct phi_arrow as (earr,Harr). 
      eexists. eapply (Hcut _ (phi (arrow a b)) _ _ _ He).
      apply Harr.
      destruct H as (eimp,Himp);
      specialize (Hconji _ _ _ _ _ Ha Himp);
      specialize (Himpe (phi a) (phi b));
      specialize (Hcut _ _ _ _ _ Hconji Himpe).
      exists (comp (pair ea eimp) eval);exact Hcut.
    - intros a b H (e,He);destructbase;destruct phi_mon as (f,Hf).
      eexists. apply (Hcut _ _ _ _ _ He (Hf a b H)).
  Defined.


  

  Lemma valid_imp: ∃ f, forall a b e, real (etop EF) e (a ⊃ b) -> real a (f e) b.
  Proof.
    destructbase; destructconj; destructimp;destruct conj_mon as (emon,Hmon). 
    eexists; intros a b e He.
    eapply Hcut;[|apply (Heval a)].
    apply Hpair;trivial. eapply Hcut;[|apply He] ;trivial.
  Qed.
 
  Lemma unif_entailment_IA_E: exists f,forall X (I:X-> Prop) (a b:X->A) s e,
      (real (etop EF) e (phi s) /\ forall i, I i -> s ≤ arrow (a i) (b i) )
      -> ( forall i, I i -> real (phi (a i)) (f e) (phi (b i))).
  Proof.
    destructbase;
      destruct phi_mon as (emon,Hmon), valid_imp as (evimp,Hvimp),phi_arrow as (ephi,Hphi).
    eexists.
    intros X I a b s e [He   Hs] i Hi; specialize (Hmon _ _ (Hs i Hi)) .
    apply Hvimp. eapply Hcut;[|apply Hphi]. eapply Hcut;[apply He|apply Hmon].
  Qed.

      
  Lemma entailment_IA_E:
     exists f, forall a b s e, (real (etop EF) e (phi s) /\ s ≤ arrow a b )
      -> ( real (phi (a)) (f e) (phi (b))).
  Proof.
    destructbase;
      destruct phi_mon as (emon,Hmon), valid_imp as (evimp,Hvimp),phi_arrow as (ephi,Hphi),
    unif_entailment_IA_E as (eunif,Hunif).
    exists eunif.
    intros a b s e [ He Hs]; specialize (Hmon _ _ Hs).
    apply (Hunif E (fun _=> True) (λ _, a) (λ _ , b) s e);trivial.
    split;intros;trivial.
  Qed.
  
  Lemma unif_entailment_E_IA:  exists f, forall I (a b:I->A) e,
        ( forall i, real (phi (a i))  e (phi (b i)))
    -> forall (i:I),  (separator (f I e a b i) /\ f I e a b i ≤ arrow (a i) (b i)).
  Proof.
    destructbase;destructimp;destructconj;
      destruct arrow_phi as (ephi,Hphi).
    exists (fun I e (a b:I → A) i=> (arrow (a i)  (b i))).
    intros. split;try reflexivity.
    unfold separator,FIA,valid.
    eexists.
    eapply Hcut;[|apply Hphi].
    eapply Hlam, Hcut;[apply Hsnd|apply H].
  Qed.  
    
    
  Lemma entailment_E_IA: exists f, forall a b e, (real (phi a) e (phi b ))
                                       ->  (separator (f e a b) /\ f e a b≤ arrow a b ).
  Proof.
    destructbase;destructimp;destructconj;
      destruct arrow_phi as (ephi,Hphi),unif_entailment_E_IA as (eunif,Hunif).
    exists (fun e a b =>  eunif E e (fun _ => a) (fun _ => b) ett).
    intros;apply Hunif. intro. apply H.
  Qed.

  Program Definition phi_to_A (p:PHI):A := exist _ (fun x => x = ax_phi p) _.
  Next Obligation. intros p a b H Ord;subst; now inversion Ord. Qed.

  Lemma phi_surj: ∃ e, forall p, real p e (phi (phi_to_A p)).
  Proof.
    destructbase;destructforall.
    eexists;intros p.
    apply Hfa;intros p' [a [Ha Hp']];subst.
      cbv in Ha;subst. simpl. apply Hax.
  Qed.

  Lemma surj_phi: ∃ e,forall p, real (phi (phi_to_A p)) e p.
  Proof.
    destructbase;destructforall.
    eexists; intros p.
    apply HPi. exists (ax_phi p);split;reflexivity.
  Qed.

  Lemma conev: forall e1,
    ∃ e2 : Evidence EF,
    ∀ p1 p1' : PROP UEF, Evidences UEF p1 e1 p1' → Evidences EF (phi p1) e2 (phi p1').
  Proof.
    destructEF;destruct entailment_IA_E as (fentails,Hentails);intros.
    destruct e1 as (s,(e,He));simpl.
    eexists;intros. eapply Hentails.
    split;[apply He|apply H]. 
  Qed.

  Lemma phi_rel: ∀ p1 : PROP UEF, ∃ p2 : PROP EF, phi p1 = p2.
  Proof.  intros;now exists (phi p1). Qed.



  (** Given any evidenced frame EF₁, if we write EF₂ for the 
      evidenced frame induced from the implicative algebra induced by EF
      (i.e. EF^{IA(EF₁)}), then phi defines a morphism from EF2 to EF₁. *)
  
  Obligation Tactic:=destructEF;intros.
  Program Definition UEF_FIA_to_EF :  EvidencedFrameMorphism False (@UEF _ _ _ _ (FIA)) (EF)
    := evidenced_frame_morphism False  (@UEF _ _ _ _ (FIA)) (EF) (phi)  (@conev)  _ _ _ _.
  Next Obligation.
    destruct entailment_IA_E as (fentails,Hentails),phi_surj as (ephi,Hphi),(etopi UEF) as (ia_top,ia_Htop).
    destruct (@conev ia_top) as (econ,Hcon).
    eexists.  eapply Hcut;[apply Hphi|]. eapply Hcon. apply ia_Htop. Qed.
  Next Obligation.
      destruct entailment_IA_E as (fentails,Hentails),phi_surj as (ephi,Hphi), Pi_phi as (ePiphi,HPiphi), arrow_phi as (ephiarr,Hphiarr), phi_arrow as (earrphi,Harrphi), surj_phi as (esurj,Hsurj), (econji UEF) as (ia_conj,ia_Hconj), imp_mon as (eimpmon,Himpmon),Pi_mon as (epimon,Hpimon), (implam) as (eimplam,Himplam), (impeval) as (eimpeval,Himpeval).
      destructforall.
      eexists.  intros. subst.
      apply Hfa;intros p [y [[c [[d Hd] Hc]] Hp ]];subst. (* ;simpl in *. *)
      destruct Hc as [s [ß [Hy [Hs Hß]]]];subst;simpl.
      eapply Hcut with ((phi p1 ⊃ ((phi p1') ⊃ (phi d)))⊃ phi d).
      - apply Hlam;intros p2 Hp2;destruct Hp2.
        apply Hcut with (econj EF (phi p1') (phi p1' ⊃ phi d));[|apply Heval].
        apply Hpair.
        + eapply Hcut;[apply Hfst|apply Hsnd].
        + eapply Hcut with (econj EF (phi p1) (phi p1 ⊃ phi p1' ⊃ phi d));[|apply Heval].
          apply Hpair;[|apply Hsnd]. eapply Hcut;[apply Hfst|apply Hfst]. reflexivity.
        + reflexivity.
      - apply Himpmon. 
        eapply Hcut with ((phi p1 ⊃ phi (arrow p1' d))).
        + eapply Hcut;[|apply Harrphi].
          apply Hfa;intros. apply HPi.
          destruct H as [a0 [H1 H2]];subst.
          apply Hs. exists a0;split;trivial.
        + apply Himpmon;[apply Hax|apply Harrphi].
        + apply HPi; exists ß;split;trivial.
  Qed.
  Notation "a ↦ b " := (arrow a b).
  Next Obligation.
    destruct conj_mon as (f,Hmon),swap as (swap,Hswap);destructforall.
    eexists;intros.
    apply Hfa; intros p (P, ((s,(ß,(Hx,(Hs,(a,(Ha,Hß)))))),H));subst; simpl.
    apply Hlam;intros p2 H2;destruct H2.
    eapply Hcut;[apply Hswap|].
    apply Hcut with (econj EF (phi p1) (euniimp EF (phi p1) (λ p2' : PROP EF, exists2 p1' : IAPROP, s1 p1' & phi p1' = p2'))).
    - apply Hmon;[|apply Hax].
      apply Hfa;intros;apply HPi. apply Hs. apply H.
    - eapply Hcut;[apply Heval|].
      exists a; trivial.
      apply HPi. exists ß;split;trivial.
  Qed.
  Next Obligation.
    destruct phi_surj as (ephisurj,Hphisurj),surj_phi as (esurjphi,Hsurjphi).
    exists phi_to_A.
    eexists;eexists;intros;split;[apply Hphisurj|apply Hsurjphi].
    intro H;destruct H. 
  Qed.

  
  Definition preinv:=fun (p:PHI) (x:A0) => x = ax_phi p.
  Program Definition inv (p : PHI) : A := exist _ (preinv p) _.
  Next Obligation. intros a b Ha H0. inversion Ha;subst. now inversion H0. Qed.
 

  
  Definition premap_ev: E -> A0 -> Prop
    := fun (e:E)  (x:A0) => exists P p1 p2, P p1 /\ real p1 e p2 /\ x = ax_arrow P (ax_phi p2).
  Program Definition map_ev (e : E) : A := exist _ (premap_ev e) _.
  Next Obligation.
    intros a b [P [p1 [p2 [HP [He Ha]]]]] H;subst.
    inversion H;subst. exists p'. exists p1. exists p2;repeat split;trivial.
    - apply H4. assumption.
    - inversion H2; reflexivity.
  Qed.

  Lemma sep_map_ev: forall e, (map_ev e)∈ʆ.
  Proof.
    intro. simpl;unfold phi,injec,map_ev;simpl; destructbase; destructconj; destructforall;destructuniimp. 
    eexists.  apply Hfa;intros p [x [[P [p1 [p2 [HP [He H2]]]]] Hp]];subst.
    apply Hlam;intros p' H. destruct H.
    eapply Hcut;[apply Hsnd|];eapply Hcut;[apply HPi|apply He];trivial.
  Qed.
    

   Lemma inv_phi_l:exists e, forall p, Evidences UEF (inv (phi p)) e p.
   Proof.
     destructbase;destructconj;destructforall;destructimp;destruct Pi_mon as (emon,Hmon). 
     pose (C:= fun a:A0 => exists p1 s ß, closure (injec (inv (Pi (injec p1)))) s /\  p1 ß /\ a = (s ⇀ ß)).
     assert (up_closed0 C).
     1: {
      intros a b (p1,(s,(ß,(Hs,(Hß,Hb))))) H;subst.
      inversion H;subst.
      exists p1;exists p';exists a';repeat split;trivial.
      intros x Hx. apply H4,Hs,Hx.
      destruct p1. simpl. now apply u with ß. 
    }
    assert (separator (exist _ _ H)).
    1: {
      eexists. apply Hfa.
      intros p' (x,(Hx,H'));subst.
      destruct Hx as (p1,(s,(ß,(Hs,(Hß,Hb)))));subst.
      simpl. apply Hlam;intros.
      eapply Hcut;[apply Hsnd|].
      eapply Hcut;[apply Hmon,Hs|].
      eapply Hcut;[apply HPi|].
      eexists.
      split. simpl. unfold preinv. reflexivity.
      simpl. reflexivity.
      apply HPi. exists ß;split;trivial.
    }
    exists (exist _ _ H0).
    intros p1 x (s,(ß,(Hs,(Hß,Hx))));subst.
    exists p1;exists s;exists ß;repeat split;trivial.
   Qed.


   Lemma inv_phi_r:exists e, forall p, Evidences UEF p e (inv (phi p)).
   Proof.
     pose (C:= fun a:A0 => exists p1 s ß, closure (injec p1) s /\ inv (Pi (injec p1)) ß  /\ a = (s ⇀ ß)).
     assert (up_closed0 C).
     1: {
       intros a b (p1,(s,(ß,(Hs,(Hß,Hb))))) H;subst.
       inversion H;subst.
       exists p1;exists p';exists a';repeat split;trivial.
       intros x Hx. apply H4,Hs,Hx.
       simpl in Hß. unfold preinv in Hß. subst.
       inversion H2. reflexivity.
     }
     assert (separator (exist _ _ H)).
     1: {
       destructbase;destructconj;destructforall;destructimp; destruct Pi_mon as (emon,Hmon).
       eexists. apply Hfa.
       intros p' (x,(Hx,H'));subst.
       destruct Hx as (p1,(s,(ß,(Hs,(Hß,Hb)))));subst.
       simpl. apply Hlam;intros.
       eapply Hcut;[apply Hsnd|].
       eapply Hcut;[apply Hmon,Hs|].
       simpl in Hß;unfold preinv in Hß.
       rewrite Hß. apply Hax.
     }
     exists (exist _ _ H0).
     intros p1 x (s,(ß,(Hs,(Hß,Hx))));subst.
     exists p1;exists s;exists ß;repeat split;trivial.
   Qed.

   
  Obligation Tactic:=destructEF;intros.
  Program Definition EF_to_UEF_FIA :  EvidencedFrameMorphism False (EF) (@UEF _ _ _ _ (FIA))
    := evidenced_frame_morphism False  (EF) (@UEF _ _ _ _ (FIA)) inv _  _ _ _ _.
  Next Obligation.
    exists (exist _  _ (@sep_map_ev e1));intros.
      simpl. intros x (s,(ß,(Hx,(Hs,Hß))));subst. exists (s). exists p1. exists p1'.
      repeat split;trivial. apply Hs.
      exists (ax_phi p1);split;trivial. reflexivity.
      now rewrite Hß.
  Qed.
  Next Obligation.
    pose (x:=(prearrow0 (intersection_set (λ _ : IAPROP, True)) (inv (etop EF)))).
    assert (up_closed0 x).
    1:{  intros a b (s,(ß,(Hx,(Hs,Hß)))) H;subst.
      simpl.
      inversion H;subst.
      exists p'. exists a'; repeat split;trivial.
      intros z (y,(Hy,Hz));subst.
      apply H4. apply Hs. exists y. split;trivial.
      rewrite Hß in H2. inversion H2;subst. reflexivity.
    }
    - pose (e:= exist _ x H).
      assert (separator e).
      + simpl. unfold phi. destructforall;destruct implam as (eimplam,Himplam).
        eexists. apply Hfa. intros p (z,((s,(ß,(Hz,(Hs,Hß)))),H'));subst.
        simpl. apply Hlam;intros. unfold singleton in H0;subst.
        rewrite Hß. simpl. apply Htop.
      + exists (exist _ _ H0).  simpl. 
        intros z (s,(ß,(Hx,(Hs,Hß))));subst.
        exists s. exists ß. repeat split;trivial.
  Qed.
  Next Obligation.
    pose (B:=fun a:A0 => exists (P : PROP EF → Prop) (p1 p2 : PROP EF), closure (injec (econj UEF (inv p1) (inv p2))) P /\ a =  (P ⇀ (ax_phi (econj EF p1 p2)))).
    assert (up_closed0 B).
    1:{
      intros a b (s,(p1,(p2,(Hs,Ha)))) H;subst.
      inversion H;subst.
      exists p'; exists p1;exists p2;repeat split;trivial.
      intros x Hx. apply H4,Hs,Hx.
      inversion H2;subst;reflexivity.
    }
    assert (separator (exist _ _ H)).
    1:{
      simpl. unfold phi. destructforall;destruct impeval as (eimpeval,Himpeval),implam as (eimplam,Himplam),Pi_mon as (emon,Hmon).
      eexists.
      apply Hfa;intros p (a,((s,(p1,(p2,(Hs,Hß)))),Hp));subst.
      simpl.
      apply Hlam;intros. destruct H0.
      eapply Hcut;[apply Hsnd|].
      eapply Hcut;[apply Hmon;apply Hs|].
      eapply Hcut.
      - apply HPi.  unfold injec.
        eexists.  split;[|reflexivity].
        pose (c:= inv (econj _ p1 p2)).
        exists ((inv p1 ↦ inv p2 ↦ c) ↦ c).
        split. exists c. reflexivity.
        exists (fun x=> exists t ß,  closure (injec (inv p1)) t /\  (inv p2 ↦ c) ß /\ x = injec0 (t ⇀ ß)). 
        eexists. split. reflexivity.
        split;[|reflexivity].
        intros x (b,((t,(ß,(Ht,(Hß,Hb)))),H'));subst.
        exists t;exists ß;repeat split;trivial.
      - simpl.
        eapply Hcut;[|apply Himpeval].
        apply Hpair;[|apply Hax].
        eapply Hcut;[apply Htop|].
        eapply Hfa. intros p [t [ß [Ht [Hß Hp]]]];subst.
        destruct Hß as (v,(γ,(Hγ,(Hv,H'))));subst. simpl.
        unfold closure in Ht,Hs.
        do 2 (apply Himplam). rewrite H'. simpl.
        apply Hpair.
        + eapply Hcut;[apply Hfst|];eapply Hcut;[apply Hsnd|].
          apply HPi. apply Ht. exists (ax_phi p1);split;trivial.
          reflexivity.
        + eapply Hcut;[apply Hsnd|].
          apply HPi. apply Hv. exists (ax_phi p2);split;trivial.
          reflexivity.                    
    }
    exists (exist _ _ H0);intros. 
    intros x (s,(ß,(Hx,(Hs,Hß))));subst. 
    exists s. exists p1. exists p1';split;[trivial|now rewrite Hß].
  Qed.
  Next Obligation.
     destructforall;destruct Pi_mon as (emon,Hmon). 
     pose (C:= fun a:A0 => exists P p1 s ß,
         closure (injec (euniimp UEF (inv p1) (λ p2' : PROP UEF, exists2 p1' : PROP EF, P p1' & inv p1' = p2'))) s /\ inv (euniimp EF p1 P) ß /\ a = (s ⇀ ß)).
     assert (up_closed0 C).
     1: {
      intros a b (P,(p1,(s,(ß,(Hs,(Hß,Hb)))))) H;subst.
      inversion H;subst.
      exists P;exists p1;exists p';exists a';repeat split;trivial.
      intros x Hx. apply H4,Hs,Hx.
      cbn in Hß;unfold preinv in Hß;subst.
      inversion H2. reflexivity. 
    }
    assert (separator (exist _ _ H)).
    1: {
      destruct (eimpi EF) as (eimplam,Himplam), (eimpe EF) as (eimpeval,Himpeval),
      swap as (eswap,Hswap),conj_mon as (ecmon,Hcmon),imp_mon as (eimon,Himon).
      eexists. apply Hfa.
      intros p' (x,(Hx,H'));subst.
      destruct Hx as (P,(p1,(s,(ß,(Hs,(Hß,Hb))))));subst.
      unfold inv,preinv in Hß;simpl in Hß. subst.
      simpl. apply Hlam;intros.
      eapply Hcut;[apply Hsnd|]. destruct H0.
      eapply Hcut;[apply Hmon,Hs|].
      apply Hlam. intros p Hp.
      eapply Hcut;[apply Hswap|].
      eapply Hcut with (econj _ p1 (p1 ⊃ p));[|apply Himpeval].
      apply Hcmon. apply Hax.
      eapply Hcut;[apply HPi|].
      eexists. 
      split. simpl. exists (singleton p1).  exists (ax_phi p). split. reflexivity.
      split. intros x (y,(Hx,Hy));subst.
      rewrite Hx. reflexivity.
      exists (inv p). split;trivial. now exists p.
      reflexivity. reflexivity.
      simpl.
      apply Himon;[|apply Hax].
      apply Hfa;intros x Hx;rewrite Hx.
      apply Hax.
    }
    exists (exist _ _ H0).
    intros p1 P a (s,(ß,(Hs,(Hß,Ha))));subst.
    exists P;exists p1;exists s;exists ß;repeat split;trivial.
  Qed.  
  Next Obligation.
    exists phi. destruct inv_phi_r as (e1,H1),inv_phi_l as (e2,H2).
    exists e1;exists e2;split;intros;trivial.
    intro H;contradict H.
  Qed.


  
   (** Given any evidenced frame EF₁, if we write EF₂ for the 
      evidenced frame induced from the implicative algebra induced by EF
      (i.e. EF^{IA(EF₁)}), then EF₁ and EF₂ are *extensionnaly*  equivalent. *)
 
  Theorem equiv1: Equiv (EvidencedFrameCategory False) (ef_comp EF_to_UEF_FIA UEF_FIA_to_EF) (ef_id False EF).
  Proof.
    destructEF;destructforall;split;eexists;intros p1; simpl.
      - apply HPi. exists (ax_phi p1);repeat split;trivial.
      - apply Hfa;intros x (y,(Hx,Hy));subst;rewrite Hx. apply Hax.
  Qed.
  Theorem equiv2: Equiv (EvidencedFrameCategory False) (ef_comp UEF_FIA_to_EF EF_to_UEF_FIA) (ef_id False UEF).
  Proof.
    destruct inv_phi_r as (e1,H1),inv_phi_l as (e2,H2).
    split. 
    - exists e2;intros p1.
    replace (Convert (ef_comp UEF_FIA_to_EF EF_to_UEF_FIA) p1) with (inv (phi p1)) by reflexivity.
    unfold ef_id,Convert,phi. apply H2.
    - exists e1;intros p1.
    replace (Convert (ef_comp UEF_FIA_to_EF EF_to_UEF_FIA) p1) with (inv (phi p1)) by reflexivity.
    unfold ef_id,Convert,phi. apply H1.
  Qed.
  

End FIA.


(** ** Functoriality of FIA *)

Definition fia (E : EvidencedFrame) : ImplicativeAlgebraObject
  := @implicative_algebra_object _ _ _ _ (@FIA E).


Fixpoint fia_map_atoms {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) a:=
  match a with
  |ax_phi x => ax_phi (Convert F x)
  |ax_arrow s b => ax_arrow (fun x=> exists y, s y /\ x = Convert F y) (fia_map_atoms F b)
  end.

Lemma inv_fia_map  {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) :
  forall a p, fia_map_atoms F a = ax_phi p -> exists x, a = ax_phi x /\ p = Convert F x.
Proof.
  intro a. induction a. intros.
  - exists p;split;trivial. simpl in H. now inversion H.
  - intros. simpl in H. inversion H.
Qed.


Definition fia_map {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) (a : IASet (fia E1)) : IASet (fia E2)
:= inv (Convert F (phi a)).

Lemma fia_map_phi  {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) :
  forall a, exists e, real  (phi (fia_map F a)) e ((Convert F (phi a))).
Proof.
  unfold phi. intro. destruct (@ePi E2) as [ ep2 ePi2 ]. eexists. apply ePi2. unfold injec. eexists (ax_phi (Convert F _)). split; reflexivity.
Qed.



Lemma phi_fia_map  {int : Prop} {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism int E1 E2) :
  forall a, exists e, real  ((Convert F (phi a))) e (phi (fia_map F a)).
Proof.
  unfold phi. intro. destruct (eaxiom E2) as [ ea2 eaxiom2 ]. destruct (@eforall E2) as [ ip2 iPi2 ]. eexists. apply iPi2. intros ? [ ? [ ? ? ] ]. subst. unfold fia_map in H. unfold inv in H. simpl in H. unfold preinv in H. subst. simpl. apply eaxiom2.
Qed.



Lemma top_imp {E:EvidencedFrame}:
  ∃ f, forall e a b, Evidences _ (a) e (b)
                -> Evidences _ (etop E) (f e) (imp a b).
Proof.
  destruct (@implam E) as (elam,Hlam);
  destruct (econje2 E) as (esnd,Hsnd);
  destruct (ecut E) as (ecut,Hcut).
  eexists. intros.
  apply  Hlam.
  eapply Hcut;[apply Hsnd|apply H].
Qed.



Program Definition fia_morphism {E1 E2 : EvidencedFrame} (F : EvidencedFrameMorphism False E1 E2) : ImplicativeAlgebraMorphism False (fia E1) (fia E2)
  := implicative_algebra_morphism False (fia E1) (fia E2) (fia_map F) _ _ _ _ _.
Next Obligation.
  destruct (ecut E2) as (ecut,Hcut).
  destruct (contop F) as (eFtop,HFtop).
  destruct (phi_fia_map F s1) as (ephi,Hphi).
  destruct H as (s,Hs).
  destruct (conevidence F s) as (eFev,HFev).
  destruct (@eforall  E2) as (efa,Hfa).
  unfold phi,injec in Hs;simpl in Hs.
  unfold separator.
  eexists.
  eapply Hcut;[|apply Hphi].
  eapply Hcut;[apply HFtop|]. 
  apply HFev.
  apply Hs.
Qed.
Next Obligation.
  destruct H as [ es1 sep1 ].
  destruct (eaxiom E1) as [ ea1 eaxiom1 ].
  destruct (ecut E1) as [ ec1 ecut1 ].
  destruct (ecut E2) as [ ec2 ecut2 ].
  destruct (etopi E1) as [ eti1 etopi1 ].
  destruct (econji E1) as [ eci1 econji1 ].
  destruct (econje1 E1) as [ ece11 econje11 ].
  destruct (econje2 E1) as [ ece21 econje21 ].
  destruct (econji E2) as [ eci2 econji2 ].
  destruct (econje1 E2) as [ ece12 econje12 ].
  destruct (econje2 E2) as [ ece22 econje22 ].
  destruct (eimpi E1) as [ eii1 eimpi1 ].
  destruct (eimpe E1) as [ eie1 eimpe1 ].
  destruct (eimpi E2) as [ eii2 eimpi2 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  destruct (conconj F) as [ cc conconj ].
  destruct (@phi_mon E1) as [ pm1 phi_mon1 ].
  destruct (@phi_arrow E1) as [ pa1 phi_arrow1 ].
  edestruct (conevidence F) as [ ce' conevidence' ].
  eexists.
  unfold phi. apply emeeti2. unfold injec. simpl. unfold preunion_set. intros ? [ a0 [ [ a [ [ a1 [ a1' [ a1'' [ ? ? ] ] ] ] ? ] ] ? ] ]. subst. simpl in *. unfold prearrow0 in H1. simpl in H1. destruct H1 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. unfold prearrow0 in H2. destruct H2 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl. unfold closure in *. apply eimpi2. eapply ecut2; [ apply econje22 | ]. apply eimpi2. unfold fia_map in H3. unfold inv in H3. simpl in H3. unfold preinv in H3. subst. simpl. unfold fia_map in *. apply ecut2 with (econj E2 (injec0 (ax_phi (Convert F (phi a1)))) (injec0 (ax_phi (Convert F (phi a1'))))).
  - apply econji2.
    + eapply ecut2; [ apply econje12 | ]. apply emeete2. apply H1. exists (ax_phi (Convert F (phi a1))). split; reflexivity.
    + eapply ecut2; [ apply econje22 | ]. apply emeete2. apply H2. exists (ax_phi (Convert F (phi a1'))). split; reflexivity.
  - simpl. eapply ecut2; [ apply conconj | ]. apply conevidence'. clear x H1 x1 H2. eapply ecut1; [ apply econji1; [ apply econje21 | ] | apply eimpe1 ]. eapply ecut1; [ apply econje11 | ]. eapply ecut1; [ apply econji1; [ apply eaxiom1 | ] | apply eimpe1 ]. eapply ecut1; [ apply etopi1 | ]. eapply ecut1; [ apply sep1 | ]. apply phi_mon1 in H. eapply ecut1; [ apply H | ]. eapply ecut1; [ apply phi_arrow1 | ]. apply eimpi1. eapply ecut1; [ apply econji1; [ apply econje21 | apply econje11 ] | ]. eapply ecut1; [ apply eimpe1 | ]. apply phi_arrow1.
Qed.
Next Obligation.
  destruct (ecut E2) as [ ec2 ecut2 ].
  destruct (econje2 E2) as [ ece22 econje22 ].
  destruct (eimpi E2) as [ eii2 eimpi2 ].
  destruct (emeete E1) as [ eme1 emeete1 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  destruct (conmeet F) as [ cm conmeet ].
  edestruct (conevidence F) as [ ce' conevidence' ].
  eexists.
  apply emeeti2. unfold injec. simpl. unfold preunion_set. intros ? [ ? [ [ ? [ [ as1 ? ] ? ] ] ? ] ]. subst. simpl in *. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. unfold fia_map in H1. unfold inv in H1. simpl in H1. unfold preinv in H1. subst. simpl. apply eimpi2. eapply ecut2; [ apply econje22 | ]. eapply ecut2; [ | apply conmeet ]. apply emeeti2. intros ? [ p1 ? ? ]. subst. unfold injec in H. destruct H as [ a0 [ ? ? ] ]. subst. unfold IAmeet in H. unfold meet_set in H. simpl in H. unfold preunion_set in H. destruct H as [ a1 [ ? ? ] ]. eapply ecut2.
  - apply emeete2. apply H0. eexists. split; try reflexivity. simpl. unfold preunion_set. eexists. split.
    + exists a1; try assumption. reflexivity.
    + reflexivity.
  - simpl. apply conevidence'. apply emeete1. unfold injec. exists a0. auto.
Qed.
Next Obligation.
  destruct (eaxiom E2) as [ ea2 eaxiom2 ].
  destruct (ecut E2) as [ ec2 ecut2 ].
  destruct (econji E2) as [ eci2 econji2 ].
  destruct (econje1 E2) as [ ece12 econje12 ].
  destruct (econje2 E2) as [ ece22 econje22 ].
  destruct (eimpi E2) as [ eii2 eimpi2 ].
  destruct (eimpe E2) as [ eie2 eimpe2 ].
  destruct (emeete E1) as [ eme1 emeete1 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  destruct (conimp F) as [ ci conimp ].
  destruct (@arrow_phi E1) as [ ap1 arrow_phi1 ].
  edestruct (conevidence F) as [ ce' conevidence' ].
  eexists.
  apply emeeti2. unfold injec. simpl. unfold preunion_set. intros ? [ ? [ [ ? [ [ ? [ ? ? ] ] ? ] ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. unfold fia_map in H1. unfold inv in H1. simpl in H1. unfold preinv in H1. subst. simpl. apply eimpi2. eapply ecut2; [ apply econje22 | ]. eapply ecut2.
   apply emeete2. apply H0. unfold injec. eexists. split.
    simpl. unfold prearrow0. eexists (eq (Convert F (phi x1))). eexists. split; try reflexivity. split; try reflexivity. intros ? ?. unfold injec in H. destruct H as [ ? [ ? ? ] ]. subst. unfold fia_map in H. unfold inv in H. simpl in H. unfold preinv in H. subst. reflexivity.
    simpl. reflexivity.
   apply ecut2 with (eimp E2 (Convert F (phi x1)) (Convert F (phi x2))).
    apply eimpi2. eapply ecut2; [ apply econji2; [ | apply econje12 ] | apply eimpe2 ]. eapply ecut2; [ apply econje22 | ]. apply emeeti2. intros. subst. apply eaxiom2.
    eapply ecut2; [ apply conimp | ]. apply conevidence'. apply arrow_phi1.
Qed.
Next Obligation.
  destruct (eaxiom E1) as [ ea1 eaxiom1 ].
  destruct (ecut E2) as [ ec2 ecut2 ].
  destruct (econje2 E2) as [ ece22 econje22 ].
  destruct (eimpi E2) as [ eii2 eimpi2 ].
  destruct (emeeti E1) as [ emi1 emeeti1 ].
  destruct (emeete E1) as [ eme1 emeete1 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  (*destruct (fia_map_phi F) as [ fmp fia_map_phi ].*)
  destruct (conmeet F) as [ cm conmeet ].
  destruct (conprop F) as [ f [ e2 [ e2' fe ] ] conprop ].
  edestruct (conevidence F) as [ ce' conevidence' ].
  edestruct (conevidence F) as [ ce'' conevidence'' ].
  simpl.
  exists (fun a2 => @inv E1 (f (phi a2))); [ split | intros [ ] ].
  - eexists. apply emeeti2. unfold injec. intros ? [ ? [ ? ? ] ]. subst. unfold IAmeet in H. unfold meet_set in H. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. unfold fia_map in H1. unfold inv at 1 in H1. simpl in H1. unfold preinv in H1. subst. simpl. apply eimpi2. eapply ecut2; [ apply econje22 | ]. apply ecut2 with (Convert F (f (phi x1))).
    * eapply ecut2; [ | apply (fun p2 => let (p, _) := fe p2 in p) ]. apply emeeti2. intros. apply emeete2. apply H0. assumption.
    * apply conevidence'. apply emeeti1. intros. unfold injec in H. destruct H as [ ? [ ? ? ] ]. subst. simpl in H. unfold preinv in H. subst. apply eaxiom1.
  - eexists. apply emeeti2. unfold injec. intros ? [ ? [ ? ? ] ]. subst. unfold IAmeet in H. unfold meet_set in H. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl. apply eimpi2. eapply ecut2; [ apply econje22 | ].
    eapply ecut2. apply emeete2. apply H0. unfold In. unfold injec. unfold fia_map. simpl. unfold preinv. eauto. simpl. clear H0 x0.
    apply ecut2 with (Convert F (f (phi x1))).
    * apply conevidence''. apply emeete1. unfold injec. simpl. unfold preinv. eauto.
    * eapply ecut2; [ apply (fun p2 => let (_, p) := fe p2 in p) | ]. apply emeete2. unfold injec. eauto.
Qed.


 Lemma phi_inv_l {EF: EvidencedFrame}: ∃ e, ∀ p , Evidences _ (@phi EF (inv(p))) e p.
   Proof.
     destruct (@implam EF) as (elam,Hlam).
     destruct (@Pi_phi EF) as (epph,Hpph).
     destruct (@arrow_phi EF) as (eap,Hap).
     destruct (eaxiom EF) as (eax,Hax);
       destruct (ecut EF) as (ecut,Hcut);
       destruct (@ePi EF) as (ePi, HPi);
       destruct (@eforall EF) as (efa,Hfa).
     destruct (@top_imp EF) as (ftop,Hftop).
     eexists. intros.
     unfold phi,inv,injec,preinv;simpl.
     apply HPi. eexists;split;reflexivity. 
   Qed.
  
  

   Lemma phi_inv_r {EF: EvidencedFrame}: ∃ e, ∀ p , Evidences _ p e (@phi EF (inv(p))).
   Proof.
     destruct (@implam EF) as (elam,Hlam).
     destruct (@Pi_phi EF) as (epph,Hpph).
     destruct (@arrow_phi EF) as (eap,Hap).
     destruct (eaxiom EF) as (eax,Hax);
       destruct (ecut EF) as (ecut,Hcut);
       destruct (@ePi EF) as (ePi, HPi);
       destruct (@eforall EF) as (efa,Hfa).
     destruct (@top_imp EF) as (ftop,Hftop).
     eexists. intros.
     unfold phi,inv,injec,preinv;simpl.
     apply Hfa. intros p' [y [Hy Hp]];subst.
     simpl. apply Hax.
   Qed.


(** FIA extends to a pseudofunctor between EF_int/EF_ext and IA_int/IA_ext*)
   

Program Definition FIAFunctor : Pseudofunctor (EvidencedFrameCategory False) (ImplicativeAlgebraCategory False)
  := pseudofunctor (EvidencedFrameCategory False) (ImplicativeAlgebraCategory False) fia (@fia_morphism) _ _ _.
Next Obligation.
  (* destruct f1, f1';rename Convert into f,Convert0 into f0. *)
  unfold EvidencedFrameRefines,ImplicativeAlgebraRefines in *;simpl in *.
  destruct H as (e,He).
  apply up_closed with (map_ev e);[|apply sep_map_ev].
  auto_meet_intro.
  unfold fia_morphism,fia_map,prearrow0 in *;simpl in *.
  intros x [s [ß [Hx [Hs Hß]]]];subst.
  unfold premap_ev.
  exists s. unfold closure,injec,inv,preinv in  Hs. simpl in Hs.
  exists (Convert f1 (phi a)). exists (Convert f1' (phi a)). inversion Hß;subst.
  repeat split;trivial.
  apply Hs;eexists;auto_refl.
  apply He.
Qed.
Next Obligation.
  split. unfold Refines,EvidencedFrameRefines,ImplicativeAlgebraRefines in *;simpl in *.
  unfold ImplicativeAlgebraRefines.
  - unfold fia_morphism,fia_map,ef_id,ia_id. simpl.
    simpl.
    destruct (@Pi_phi o1) as (epph,Hpph).
    destruct (@arrow_phi o1) as (eap,Hap).
    destruct (ecut o1) as (ecut,Hcut);
    destruct (eaxiom o1) as (eax,Hax);
    destruct (@ePi o1) as (ePi, HPi);
    destruct (@eforall o1) as (efa,Hfa).
    destruct (@top_imp o1) as (ftop,Hftop).
    destruct (@phi_inv_r o1) as (epir,Hpir).
    eexists.
    eapply Hcut;[|apply Hpph].
    apply Hfa. intros p [z [[a Ha]  Hp]];subst.
    eapply Hcut;[|apply Hap]. apply Hftop.  eapply Hcut;[|apply Hpir]. apply Hax.
  - unfold fia_morphism,fia_map,ef_id,ia_id. simpl.
    destruct (@Pi_phi o1) as (epph,Hpph).
    destruct (@arrow_phi o1) as (eap,Hap).
    destruct (ecut o1) as (ecut,Hcut);
    destruct (eaxiom o1) as (eax,Hax);  
    destruct (@ePi o1) as (ePi, HPi);
    destruct (@eforall o1) as (efa,Hfa).
    destruct (@top_imp o1) as (ftop,Hftop).
    destruct (@phi_inv_l o1) as (epil,Hpil).
    eexists.
    eapply Hcut;[|apply Hpph].
    apply Hfa.
    intros p [z [[a Ha]  Hp]];subst.
    eapply Hcut;[|apply Hap]. apply Hftop. simpl.  eapply Hcut;[apply Hpil|]. apply Hax.
Qed.
Next Obligation.
  rename o1 into E1. rename o1' into E2. rename o1'' into E3. rename f1 into F. rename f1' into G.
  destruct (eaxiom E2) as [ ec2 eaxiom2 ].
  destruct (ecut E3) as [ ec3 ecut3 ].
  destruct (econje2 E3) as [ ece23 econje23 ].
  destruct (eimpi E3) as [ eii3 eimpi3 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  destruct (emeeti E3) as [ emi3 emeeti3 ].
  destruct (emeete E3) as [ eme3 emeete3 ].
  edestruct (conevidence G) as [ ceg conevidenceg ].
  edestruct (conevidence G) as [ ceg' conevidenceg' ].
  split; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl; unfold fia_map; simpl.
  - eexists.
    apply emeeti3. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl in H1. unfold preinv in H1. subst. simpl.
    apply eimpi3. eapply ecut3; [ apply econje23 | ].
    eapply ecut3 . apply emeete3. apply H0. unfold In. unfold injec. eexists (ax_phi _). split; reflexivity. clear x0 H0.
    apply conevidenceg.
    apply emeete2. unfold injec. eexists (ax_phi _). split; reflexivity.
  - eexists.
    apply emeeti3. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl in H1. unfold preinv in H1. subst. simpl.
    apply eimpi3. eapply ecut3; [ apply econje23 | ].
    eapply ecut3. apply emeete3. apply H0. unfold In. unfold injec. eexists (ax_phi _). split; reflexivity. clear x0 H0.
    apply conevidenceg'.
    apply emeeti2. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preinv in H. subst. simpl. apply eaxiom2.
Qed.
Arguments FIAFunctor : clear implicits.

Lemma phi_sep {IA:ImplicativeAlgebraObject}:
  forall s1,  IASeparator (fia (uef IA)) s1 -> IASeparator IA (phi s1).
Proof.
  intros s1 H.
  unfold IASeparator,valid in *;simpl in *.
  destruct H as ((e,sep_e),He). unfold real,realizes,uef,UEF,Evidences,realizes in He.
  simpl in He.
  eapply (@up_closed _ _ _ _ (IAAlgebra IA) (IAapp e K)).
  apply adj_app. eapply ord_trans;[apply He|].
  apply arrow_mon_l. apply top_max.
  apply app_closed;trivial;apply sep_K.
Qed.



Lemma imp_arrow {IA:ImplicativeAlgebraObject}:
  forall a b, IAOrd IA (@imp (uef IA) a b) (a ↦  b).
Proof.   intros. apply arrow_mon_r. apply meet_elim. eexists;reflexivity. Qed.  



(** * Equivalence btw IA_ext and EF_ext *)

(** ** φ defines an IA-morphism: FIA (UEF (IA))→ IA *)

Program Definition FIA_UEF_to_IA {IA:ImplicativeAlgebraObject}:  ImplicativeAlgebraMorphism False (fia (uef IA)) (IA)
    := implicative_algebra_morphism False  (fia (uef IA)) (IA) phi  phi_sep  _ _ _ _.
Next Obligation.
  destruct (@phi_arrow (uef IA)) as ((e,sep_e),He).
  destruct (@phi_mon (uef IA)) as ((emon,sep_mon),Hmon).
  (* unfold  real,realizes,uef,IA_EF,Evidences,realizes in Hmon;simpl in Hmon. *)
  eapply up_closed with (IAapp (IAapp (IAapp (IAabs (fun p => IAabs (fun e => IAabs (fun emon => IAabs (fun x => IAapp e (IAapp (IAapp e (IAapp emon p)) x)))))) (phi s1)) e) emon).
  - auto_meet_intro.
    apply adj_app,adj_app,beta_red,adj_imp,beta_red,adj_imp,beta_red,adj_imp,beta_red,adj_app.
    eapply ord_trans;[apply He|]. 
    apply arrow_mon;[|apply imp_arrow].
    eapply adj_app,adj_app,ord_trans;[apply He|]. 
    apply arrow_mon;[|apply imp_arrow].
    apply adj_app,Hmon,H2.
  - repeat (apply app_closed);trivial.
    realizer (λ[IA]+  (λ+ λ+ λ+ ([$2] ([[$2] ([$1] $3)]$0)))).
    now apply phi_sep.
Qed.
Next Obligation.
  destruct (@Pi_phi (uef IA)) as ((e,sep_e),He).
  eapply up_closed with (IAapp (IAabs (fun e => (IAabs (fun x => IAapp e (IAabs (fun _ => x)))))) e).
  - auto_meet_intro.
    apply beta_red,adj_imp,beta_red,adj_app.
    eapply ord_trans;[apply He|].
    apply arrow_mon_l.
    unfold Pi, uef,UEF. simpl.
    apply adj_imp,beta_red.
    auto_meet_intro.
    apply meet_elim.
    exists a0;trivial.
  - apply app_closed.
    realizer (λ[IA]+ λ+ [$1] (λ+ $1)).
    apply sep_e.
Qed.
Next Obligation.
  destruct (@arrow_phi (uef IA)) as ((e,sep_e),He).
  apply up_closed with e;[|apply sep_e].
  auto_meet_intro.
  eapply ord_trans;[apply He|].
  apply arrow_mon_l.
  apply arrow_mon_r.
  auto_meet_intro.
  intros. now rewrite H0.
Qed.
Next Obligation.
  exists (@inv (uef IA)); [ | intros [ ] ].
  split.
  - destruct (@phi_inv_r (uef IA)) as ((e,sep_e),He).
    eapply up_closed;[|apply sep_e].
    auto_meet_intro. apply He.
  - destruct (@phi_inv_l (uef IA)) as ((e,sep_e),He).
    eapply up_closed;[|apply sep_e].
    auto_meet_intro. apply He.
Qed.


  Ltac destconj EF:=
    destruct (econji EF) as (epair,Hpair);
    destruct (econje1 EF) as (efst,Hfst);
    destruct (econje2 EF) as (esnd,Hsnd).
  
  Ltac destbase EF:=
    destruct (eaxiom EF) as (eax,Hax);
    destruct (ecut EF) as (ecut,Hcut);
    destruct (etopi EF) as (ett,Htop).


  Ltac destforall E:=
    destruct (@ePi E) as (ePi, HPi);
    destruct (@eforall E) as (efa,Hfa).

   Ltac destimp E:=
    destruct (@implam E) as (elam,Hlam);
    destruct (@impeval E) as (eeval,Heval).

  

Lemma inv_sep {IA:ImplicativeAlgebraObject}:
  forall s1,  IASeparator IA (s1) -> IASeparator (fia (uef IA)) (@inv (uef IA) s1).
Proof.
  intros s1 H. 
  unfold IASeparator,valid,top_φ,imp_φ,injec,inv,preinv,injec in *;simpl in *.
  unfold injec.
  destforall (uef IA).
  destimp (uef IA).
  destruct (@top_imp (uef IA)) as (etop,Htop).
  pose (t:=IAapp (IAabs (fun s => (IAabs (fun y => IAabs (fun x => s))))) s1).
  assert (IASeparator IA t).
  apply app_closed;trivial.
  realizer (λ[IA]+ λ+ λ+  ($2)).
  exists (exist _ t H0). 
  unfold real,realizes,uef. unfold UEF,realizes. simpl. 
  apply beta_red,adj_imp,beta_red,adj_imp,beta_red.
  auto_meet_intro. reflexivity.
Qed.

Lemma Pi_meet {IA:ImplicativeAlgebraObject}:
  exists e:(Evidence (uef IA)), forall S, realizes (@Pi (uef IA) S) e (@meet_set _ _ (IALattice IA) S) .
Proof.
  pose (t:=IAabs (fun x => IAapp x (@Id  _ _ _ (IAStructure IA)))).
  assert (IASeparator IA t). unfold t,Id.
  realizer (λ[IA]+  ([$0] (λ+ $0))).
  exists (exist _ t H);intro S.
  unfold realizes. simpl.
  apply adj_imp,beta_red,adj_app.
  apply arrow_mon_l,top_max.
Qed.


Lemma imp_arrow_id  {IA:ImplicativeAlgebraObject}:
  exists e,  forall (b c:IASet IA), @Evidences (uef IA) (@imp (uef IA) b c) e (b ↦ c).
Proof.
  exists (exist _ _  sep_Id).
  intros. apply adj_imp,beta_red,imp_arrow.
Qed.


(** ** inv defines an IA-morphism: IA → FIA(UEF(IA)) *)

Program Definition IA_to_FIA_UEF {IA:ImplicativeAlgebraObject}:  ImplicativeAlgebraMorphism False IA (fia (uef IA)) 
    := implicative_algebra_morphism False IA (fia (uef IA)) (@inv (uef IA))  inv_sep  _ _ _ _.
Next Obligation.
  unfold IASeparator,valid,top_φ,imp_φ,injec,inv,preinv,injec in *;simpl in *.
  unfold injec.
  destforall (uef IA).
  destimp (uef IA).
  pose (id:=@Id _ _ _ (IAStructure IA)).
  pose (t:=IAapp (IAabs (fun s1 => IAabs (fun y => IAabs (fun x => IAabs (fun b=> (IAabs (fun c => (IAapp (IAapp s1 (IAapp b id)) (IAapp c id))))))))) s1).
  assert (Ht:IASeparator IA t).
  apply app_closed.
  unfold id,Id.
  realizer (λ[IA]+ λ+ λ+ λ+ λ+ ([[$4] ([$1] (λ+ $0))] ([$0] (λ+ $0)))).
  apply H.
  exists (exist _ t Ht).
  unfold real,realizes,uef. unfold UEF,realizes. simpl. 
  do 2 (apply beta_red,adj_imp). apply beta_red. 
  auto_meet_intro.
  destruct H0 as [A [[b [c [d [Hs1 Ha]]]] HA]];subst.
  destruct HA as [s [ß [Ha [Hß Hs]]]];subst;simpl.
  apply adj_imp,beta_red. 
  auto_meet_intro.
  intros x Hx.  rewrite <- Hx.
  destruct Hs as [s' [ß' [Ha' [Hß' Hs']]]];subst;simpl.
  apply adj_imp,beta_red. 
  auto_meet_intro.
  intros y Hy.  rewrite <- Hy.
  simpl in Hs';subst;simpl.
  apply adj_app,adj_app.
  eapply ord_trans;[apply Hs1|].
  apply arrow_mon.
  + apply adj_app,arrow_mon;try apply top_max.
    apply meet_elim, Hß.
    eexists. split;reflexivity.
  + apply arrow_mon_l.
    apply adj_app,arrow_mon;try apply top_max.
    apply meet_elim, Hß'.
    eexists. split;reflexivity.
Qed. 
Next Obligation.
  Opaque phi.
  unfold IASeparator,separator,fia;simpl.
  destforall (uef IA).
  destimp (uef IA).
  destconj (uef IA).
  destbase (uef IA).
  destruct (@Pi_phi (uef IA)) as (epph,Hpph).
  destruct (@phi_Pi (uef IA)) as (ephp,Hphp).
  destruct (@arrow_phi (uef IA)) as (eap,Hap).
  destruct (@phi_inv_r (uef IA)) as (epi,Hpi).
  destruct (@phi_inv_l (uef IA)) as (epil,Hpil).
  destruct (@Pi_meet IA) as (epim,Hpim).
  eexists.
  eapply Hcut;[|apply Hpph].
  apply Hfa.
  intros x [a [[S HS] Hx]];subst.
  eapply Hcut;[|apply Hap].
  apply Hlam.
  eapply Hcut;[apply Hsnd|].
  eapply Hcut;[|apply Hpi].
  eapply Hcut;[apply Hphp|].
  apply Hcut with (@Pi (uef IA) (λ x:IASet IA , S x)).
  apply Hfa.
  intros.
  eapply Hcut;[|apply Hpil].
  apply HPi. exists (inv p'). split;trivial. exists p';trivial.
  apply Hpim.
Qed.
Next Obligation.
  unfold IASeparator,separator,fia;simpl.
  destforall (uef IA).
  destimp (uef IA).
  destconj (uef IA).
  destbase (uef IA).
  destruct (@Pi_phi (uef IA)) as (epph,Hpph).
  destruct (@phi_Pi (uef IA)) as (ephp,Hphp).
  destruct (@arrow_phi (uef IA)) as (eap,Hap).
  destruct (@phi_arrow (uef IA)) as (epa,Hpa).
  destruct (@phi_inv_r (uef IA)) as (epi,Hpi).
  destruct (@phi_inv_l (uef IA)) as (epil,Hpil).
  destruct (@imp_mon (uef IA)) as (eimon,Himon).
  destruct (@imp_arrow_id IA) as (eia,Hia).
  eexists.
  eapply Hcut;[|apply Hpph].
  apply Hfa.
  intros x [a [[b [c Hb]] Hx]];subst.
  eapply Hcut;[|apply Hap].
  apply Hlam.
  eapply Hcut;[apply Hsnd|].
  eapply Hcut;[|apply Hpi].
  eapply Hcut;[apply Hpa|].
  eapply Hcut;[apply Himon|].
  apply Hpi. apply Hpil.
  apply Hia.
Qed.
Next Obligation.
  unfold IASeparator,separator;simpl;unfold valid,realizes; simpl.
  destforall (uef IA).
  destimp (uef IA).
  destbase (uef IA).
  destconj (uef IA).
  destruct (@top_imp (uef IA)) as (eti,Hti).
  destruct (@imp_mon (uef IA)) as (emon,Hmon).
  destruct (@Pi_phi (uef IA)) as (epp,Hpp).
  destruct (@phi_inv_r (uef IA)) as (epir,Hpir).
  destruct (@phi_inv_l (uef IA)) as (epil,Hpil).
  destruct (@arrow_phi (uef IA)) as (eap,Hap).
  exists phi. split.
  - eexists.  eapply Hcut;[|apply Hpp].
    apply Hfa. intros x [a [[b  Ha]]] ;subst.
    eapply Hcut;[|apply Hap].
    apply Hti,Hpir.
  - eexists.  eapply Hcut;[|apply Hpp].
    apply Hfa. intros x [a [[b  Ha]]] ;subst.
    eapply Hcut;[|apply Hap].
    apply Hti, Hpil.
  - intros H;contradict H.
Qed.



(** ** Biadjoint Biequivalence : IA_ext ≊ EF_ext *)

(** Theorem VI.12  -
    EF_ext and IA_ext are equivalent in the sense that UEF and FIA 
    extend to a biadjoint biequivalence between them.
 *)



Program Definition implicative_algebra_evidenced_frame_equivalence : BiadjointBiequivalence (ImplicativeAlgebraCategory False) (EvidencedFrameCategory False)
:= biadjoint_biequivalence (ImplicativeAlgebraCategory False)
                           (EvidencedFrameCategory False)
                           (UEFFunctor False)
                           FIAFunctor
                           (pseudonatural_transformation (cat_id (ImplicativeAlgebraCategory False)) (cat_comp (UEFFunctor False) FIAFunctor) (@IA_to_FIA_UEF) _)
                           (pseudonatural_transformation (cat_comp (UEFFunctor False) FIAFunctor) (cat_id (ImplicativeAlgebraCategory False)) (@FIA_UEF_to_IA) _)
                           (pseudonatural_transformation (cat_id (EvidencedFrameCategory False)) (cat_comp FIAFunctor (UEFFunctor False)) (@EF_to_UEF_FIA) _)
                           (pseudonatural_transformation (cat_comp FIAFunctor (UEFFunctor False)) (cat_id (EvidencedFrameCategory False)) (@UEF_FIA_to_EF) _)
                           _ _ _ _ _.
Next Obligation.
  rename o1 into A1. rename o1' into A2.
  assert (Hunary:=iamunary m1).
  destruct m1. rename IAMap into F.
  destforall (uef A2).
  destimp (uef A2).
  destbase (uef A2).
  destconj (uef A2).
  destruct (@top_imp (uef A2)) as (eti,Hti).
  destruct (@imp_mon (uef A2)) as (emon,Hmon).
  destruct (@Pi_phi (uef A2)) as (epp,Hpp).
  destruct (@phi_inv_r (uef A2)) as (epir,Hpir).
  destruct (@phi_inv_l (uef A2)) as (epil,Hpil).
  destruct (@arrow_phi (uef A2)) as (eap,Hap).
  destruct (@phi_inv_r (uef A1)) as ((epir1,sep_epir1),Hpir1).
  destruct (@phi_inv_l (uef A1)) as ((epil1,sep_epil1),Hpil1).
  split; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl; unfold fia_map; simpl.
  - unfold fia,IASeparator,separator in *; simpl in *.
    unfold valid.
    pose (sep_eF:=(Hunary epir1 sep_epir1)).
    pose (tF:=(⊓ (λ a2 : IASet A2, ∃ a1 a1' : IASet A1, IAOrd A1 epir1 (a1 ↦ a1') ∧ F a1 ↦ F a1' = a2))).
    pose (ef:=(exist _ tF sep_eF)).
    exists (ecut (efa (ecut (eti (ecut epil (ecut ef epir))) eap )) epp).
    (* eexists. *)
    eapply Hcut;[|apply Hpp].
    apply Hfa. intros p [a [[b Hb] Ha]];subst.
    eapply Hcut;[|apply Hap]. 
    apply Hti.
    eapply Hcut;[apply Hpil|]. 
    eapply Hcut;[|apply Hpir].
    apply meet_elim.
    exists b. eexists. split;[|reflexivity].
    apply Hpir1.
  - pose (sep_eF:=(Hunary epil1 sep_epil1)).
    pose (tF:=(⊓ (λ a2 : IASet A2, ∃ a1 a1' : IASet A1, IAOrd A1 epil1 (a1 ↦ a1') ∧ F a1 ↦ F a1' = a2))).
    pose (ef:=(exist _ tF sep_eF)).
    exists (ecut (efa (ecut (eti (ecut epil (ecut ef epir))) eap )) epp).
    eapply Hcut;[|apply Hpp].
    apply Hfa. intros p [a [[b Hb] Ha]];subst.
    eapply Hcut;[|apply Hap]. 
    apply Hti.
    eapply Hcut;[apply Hpil|]. 
    eapply Hcut;[|apply Hpir].
    apply meet_elim.
    eexists. exists b. split;[|reflexivity].
    apply Hpil1.
Qed.  
Next Obligation.
  rename o1 into A1. rename o1' into A2.
  destruct m1. rename IAMap into F.
  destruct (@phi_inv_r (uef A2)) as ((epir,sep_epir),Hpir).
  destruct (@phi_inv_l (uef A2)) as ((epil,sep_epil),Hpil).
  split; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl; unfold fia_map; simpl.
  - apply up_closed with epil;[|apply sep_epil].
    auto_meet_intro. apply Hpil.
  - apply up_closed with epir;[|apply sep_epir].
    auto_meet_intro. apply Hpir.
Qed.
Transparent phi.
Next Obligation.
  rename o1 into E1. rename o1' into E2. rename m1 into F.
  destruct (eaxiom E1) as [ ea1 eaxiom1 ].
  destruct (ecut E2) as [ ec2 ecut2 ].
  destruct (econje2 E2) as [ ece22 econje22 ].
  destruct (eimpi E2) as [ eii2 eimpi2 ].
  destruct (emeeti E1) as [ emi1 emeeti1 ].
  destruct (emeete E1) as [ eme1 emeete1 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  edestruct (conevidence F) as [ ce' conevidence' ].
  edestruct (conevidence F) as [ ce'' conevidence'' ].
  split; simpl (Refines _); unfold EvidencedFrameRefines; simpl; unfold fia_map; simpl.
  - simple refine (ex_intro _ (exist _ (exist _ (fun a0 => exists p1, exists2 ps1, ps1 (Convert F p1) & ax_arrow ps1 (ax_phi (Convert F (phi (inv p1)))) = a0) _) _) _).
    + simpl. unfold up_closed0. intros ? ? [ ? [ ? ? ? ] ] ?. subst. inversion H1; clear H1; subst. inversion H3; clear H3; subst. exists x. exists p'; try reflexivity. apply H5. assumption.
    + simpl. unfold valid.
      eexists.
      apply emeeti2. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. destruct H as [ ? [ ? ? ? ] ]. subst. simpl. apply eimpi2. eapply ecut2; [ apply econje22 | ].
      eapply ecut2. apply emeete2. eassumption.
      apply conevidence'.
      apply emeeti1. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H0. unfold preinv in H0. subst. simpl.
      apply eaxiom1.
    + intros p1 a0 e. unfold In in e. unfold prearrow0 in e. destruct e as [ ? [ ? [ ? [ ? ? ] ] ] ]. simpl in H1. unfold preinv in H1. subst. unfold In. simpl. exists p1. exists x; try reflexivity. apply H0. unfold In. unfold injec. eexists (ax_phi _). split; reflexivity.
  - simple refine (ex_intro _ (exist _ (exist _ (fun a0 => exists p1, exists2 ps1, ps1 (Convert F (phi (inv p1))) & ax_arrow ps1 (ax_phi (Convert F p1)) = a0) _) _) _).
    + simpl. unfold up_closed0. intros ? ? [ ? [ ? ? ? ] ] ?. subst. inversion H1; clear H1; subst. inversion H3; clear H3; subst. exists x. exists p'; try reflexivity. apply H5. assumption.
    + simpl. unfold valid.
      eexists.
      apply emeeti2. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. destruct H as [ ? [ ? ? ? ] ]. subst. simpl. apply eimpi2. eapply ecut2; [ apply econje22 | ].
      eapply ecut2. apply emeete2. eassumption.
      apply conevidence''.
      apply emeete1. unfold injec. eexists (ax_phi _). split; reflexivity.
    + intros p1 a0 e. unfold In in e. unfold prearrow0 in e. destruct e as [ ? [ ? [ ? [ ? ? ] ] ] ]. simpl in H1. unfold preinv in H1. subst. unfold In. simpl. exists p1. exists x; try reflexivity. apply H0. unfold In. unfold injec. eexists (ax_phi _). split; reflexivity.
Qed.
Next Obligation.
  rename o1 into E1. rename o1' into E2. rename m1 into F.
  destruct (eaxiom E2) as [ ea2 eaxiom2 ].
  destruct (emeeti E2) as [ emi2 emeeti2 ].
  destruct (emeete E2) as [ eme2 emeete2 ].
  split; simpl (Refines _); unfold EvidencedFrameRefines; simpl; unfold fia_map; simpl.
  - eexists.
    intro.
    apply emeete2. unfold injec. eexists (ax_phi _). split; reflexivity.
  - eexists.
    intro.
    apply emeeti2. unfold injec. intros ? [ ? [ ? ? ] ]. simpl in H. unfold preinv in H. subst. simpl.
    apply eaxiom2.
Qed.
Next Obligation.
  intro A.
  destruct (@phi_inv_r (uef A)) as ((epir,sep_epir),Hpir).
  destruct (@phi_inv_l (uef A)) as ((epil,sep_epil),Hpil).
  split; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl.
  - apply up_closed with epil;[|apply sep_epil].
    auto_meet_intro. apply Hpil.
  - apply up_closed with epir;[|apply sep_epir].
    auto_meet_intro. apply Hpir.
Qed.
Next Obligation.
  intro A.
  destruct (@inv_phi_r (uef A)) as ((epir,sep_epir),Hpir).
  destruct (@inv_phi_l (uef A)) as ((epil,sep_epil),Hpil).
  split; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl.
   - apply up_closed with epil;[|apply sep_epil].
    auto_meet_intro. apply Hpil.
  - apply up_closed with epir;[|apply sep_epir].
    auto_meet_intro. apply Hpir.
Qed.
Next Obligation.
  intro E.
  destruct (eaxiom E) as [ ea eaxiom ].
  destruct (emeeti E) as [ emi emeeti ].
  destruct (emeete E) as [ eme emeete ].
  split; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
  - eexists.
    intro.
    apply emeete. unfold injec. eexists (ax_phi _). split; reflexivity.
  - eexists.
    intro.
    apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. simpl in H. unfold preinv in H. subst. simpl. apply eaxiom.
Qed.
Next Obligation.
  intro E.
  destruct (eaxiom E) as [ ea eaxiom ].
  destruct (ecut E) as [ ec ecut ].
  destruct (econje2 E) as [ ece2 econje2 ].
  destruct (eimpi E) as [ eii eimpi ].
  destruct (emeeti E) as [ emi emeeti ].
  destruct (emeete E) as [ eme emeete ].
  split; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
  - simple refine (ex_intro _ (exist _ (exist _ (fun a0 => exists a, exists2 ps1, ps1 (phi a) & exists2 a0', (proj1_sig a) a0' & ax_arrow ps1 a0' = a0) _) _) _).
    + simpl. unfold up_closed0. intros ? ? [ ? [ ? ? [ ? ? ? ] ] ] ?. subst. inversion H2; clear H2; subst. exists x. exists p'.
      * apply H6. assumption.
      * exists a'; try reflexivity. destruct x as [ ? up ]. simpl in *. apply up with x1; assumption.
    + simpl. unfold valid.
      eexists.
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. destruct H as [ ? [ ? ? [ ? ? ? ] ] ]. subst. simpl. apply eimpi. eapply ecut; [ apply econje2 | ].
      eapply ecut. apply emeete. eassumption. clear x1 H.
      apply emeete. unfold injec. eauto.
    + intros p1 a0 e. unfold In in e. unfold prearrow0 in e. destruct e as [ ? [ ? [ ? [ ? ? ] ] ] ]. simpl in H1. unfold preinv in H1. subst. unfold In. simpl. exists p1. exists x.
      * apply H0. unfold In. unfold injec. eexists (ax_phi _). split; reflexivity.
      * exists x0; trivial.
  - simple refine (ex_intro _ (exist _ (exist _ (fun a0 => exists a : A, exists2 ps1 : PHI -> Prop, (forall a0, (proj1_sig a) a0 -> ps1 (injec0 a0)) & ax_arrow ps1 (ax_phi (phi a)) = a0) _) _) _).
    + simpl. unfold up_closed0. intros ? ? [ ? [ ? ? ? ] ] ?. subst. inversion H1; clear H1; subst. inversion H3; clear H3; subst. exists x. exists p'; try reflexivity. intros. apply H5. unfold In. auto.
    + simpl. unfold valid.
      eexists.
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. destruct H as [ ? [ ? ? ? ] ]. subst. simpl. apply eimpi. eapply ecut; [ apply econje2 | ].
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst.
      apply emeete. auto.
    + intros p1 a0 e. unfold In in e. unfold prearrow0 in e. destruct e as [ ? [ ? [ ? [ ? ? ] ] ] ]. simpl in H1. unfold preinv in H1. subst. unfold In. simpl. exists p1. exists x; try reflexivity. intros. apply H0. unfold In. unfold injec. eauto.
Qed.
Next Obligation.
  simpl.
  split; [ | split; [ | split ] ].
  - Opaque phi.
    intro A.
    destruct (@phi_inv_r (uef A)) as (epir,Hpir).
    destruct (@phi_inv_l (uef A)) as (epil,Hpil).
    split; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
    + exists epil. apply Hpil.
    + exists epir. apply Hpir.
  - intro A.
    destruct (@phi_inv_r (uef A)) as (epir,Hpir).
    destruct (@phi_inv_l (uef A)) as (epil,Hpil).
    split; simpl (Refines _); unfold EvidencedFrameRefines; simpl.
    + exists epil. apply Hpil.
    + exists epir. apply Hpir.
    Transparent phi.  
  - intro E.
    unfold Equiv; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl.
    destruct (eaxiom E) as [ ea eaxiom ].
    destruct (ecut E) as [ ec ecut ].
    destruct (etopi E) as [ eti etopi ].
    destruct (econji E) as [ eci econji ].
    destruct (econje1 E) as [ ece1 econje1 ].
    destruct (econje2 E) as [ ece2 econje2 ].
    destruct (eimpi E) as [ eii eimpi ].
    destruct (eimpe E) as [ eie eimpe ].
    destruct (emeeti E) as [ emi emeeti ].
    destruct (emeete E) as [ eme emeete ].
    split.
    + eexists.
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl. apply eimpi. eapply ecut; [ apply econje2 | ].
      eapply ecut. apply emeete. apply H0. unfold In. unfold injec. eexists. split; try reflexivity. simpl. eexists (eq _). exists (ax_phi (phi x1)). split; try reflexivity. split.
        intros ? [ ? [ ? ? ] ]. subst. unfold preintersection_set in H. specialize (H (inv (etop E)) I). simpl in H. unfold preinv in H. subst. simpl. reflexivity.
        unfold preunion_set. eexists. split; [ eexists; split; reflexivity | ]. simpl. reflexivity.
      clear H0 x0. simpl.
      eapply ecut; [ | eapply ecut; [ apply eimpe | ] ]. apply econji; [ | apply eaxiom ]. apply emeeti. intros. subst. apply etopi.
      apply emeete. unfold injec. eauto.
    + eexists.
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. simpl in H1. destruct H1 as [ ? [ ? [ ? [ ? ? ] ] ] ]. unfold preunion_set in H3. destruct H3 as [ ? [ [ ? [ ? ? ] ] ? ] ]. unfold preinv in H3. subst. simpl in H5. unfold preinv in H5. subst. simpl. apply eimpi. eapply ecut; [ apply econje2 | ].
      apply eimpi.
      eapply ecut; [ apply econje1 | ].
      apply emeeti. intros.
      apply emeete. apply H0. assumption.
  - intro E.
    unfold Equiv; simpl (Refines _); unfold ImplicativeAlgebraRefines; simpl.
    destruct (eaxiom E) as [ ea eaxiom ].
    destruct (ecut E) as [ ec ecut ].
    destruct (etopi E) as [ eti etopi ].
    destruct (econji E) as [ eci econji ].
    destruct (econje1 E) as [ ece1 econje1 ].
    destruct (econje2 E) as [ ece2 econje2 ].
    destruct (eimpi E) as [ eii eimpi ].
    destruct (eimpe E) as [ eie eimpe ].
    destruct (emeeti E) as [ emi emeeti ].
    destruct (emeete E) as [ eme emeete ].
    split.
    + eexists.
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl. apply eimpi. eapply ecut; [ apply econje2 | ].
      eapply ecut. apply emeete. apply H0. unfold In. unfold injec. eexists. split; reflexivity. clear x0 H0. simpl.
      eapply ecut. apply emeete. unfold injec. simpl. eexists. split; try reflexivity. unfold prearrow0. eexists (eq _). eexists. split; try reflexivity. split.
        intros ? ?. unfold In in H. unfold injec in H. destruct H as [ ? [ ? ? ] ]. subst. simpl in H. unfold preintersection_set in H. specialize (H (inv (etop E)) I). simpl in H. unfold preinv in H. subst. simpl. reflexivity.
        simpl. unfold preunion_set. eexists. split; [ eexists; split; reflexivity | ]. simpl. eassumption.
      simpl. clear x1 H1.
      eapply ecut; [ apply econji; [ | apply eaxiom ] | apply eimpe ].
      apply emeeti. intros. subst.
      apply etopi.
    + eexists.
      apply emeeti. unfold injec. intros ? [ ? [ ? ? ] ]. subst. simpl in H. unfold preunion_set in H. destruct H as [ ? [ [ ? ? ] ? ] ]. subst. simpl in H0. unfold prearrow0 in H0. destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ]. simpl in H1. unfold preinv in H1. subst. simpl. apply eimpi. eapply ecut; [ apply econje2 | ].
      apply emeeti. intros ? [ ? [ ? ? ] ]. simpl in H. unfold prearrow0 in H. destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]. subst. simpl in H3. unfold preunion_set in H3. destruct H3 as [ ? [ ? ? ] ]. unfold injec in H. destruct H as [ ? [ ? ? ] ]. simpl in H. unfold preinv in H. subst. simpl in H1. simpl.
      apply eimpi. eapply ecut; [ apply econje1 | ]. clear x2 H2.
      apply emeete. apply H0. unfold In. unfold injec. eauto.
Qed.
