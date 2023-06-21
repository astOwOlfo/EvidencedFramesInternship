Set Implicit Arguments.
Set Contextual Implicit.

Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.
Require Export Relation_Definitions.
Require Import Sets.Ensembles.
Require Import EF.Categories.
Require Import Arith.
Require Import Coq.micromega.Lia.
Require Import EF.Categories.
Require Import EF.Triposes.


(** This files contains the definitions of 
    standard algebraic structures required 
    in the sequel (orders, lattices, etc.) *)


(**  *   Partial Orders  *)

Definition Ens `{X:SET}:= Ensemble X.
Definition emptyset `{X:SET}:= Empty_set X.

Class Order {X:SET} :=
  {
    ord : X → X → Prop;
    ord_refl : reflexive X ord;
    (* ord_antisym : antisymmetric X ord; *)
    ord_trans : transitive X ord
  }.

Generalizable Variables X ord.
Declare Scope ia_scope.
Infix "≤" := ord : ia_scope.
Global Open Scope ia_scope.


Global Instance ord_Reflexive `{Ord:Order X}: Reflexive ord:=ord_refl.
Global Instance ord_Transitive `{Ord:Order X}: Transitive ord:=ord_trans.


(** Simple lemma to simplify proof of ordering when equalities hold. *)
Lemma by_refl `{Ord:Order X}: ∀ (a b:X), a = b → a ≤ b.
Proof.
  intros a b H; subst;reflexivity.
Qed.  


Definition lb  `{O:Order} (P:Ens) : X → Prop := fun x => forall y, P(y) -> x ≤ y.
Definition ub  `{O:Order} (P:Ens) : X → Prop := fun x => forall y, P(y) -> y ≤ x.
Definition glb `{O:Order} (P:Ens) : X → Prop := fun x => lb P x ∧ ∀ y, lb P y → y ≤ x.
Definition lub `{O:Order} (P:Ens) : X → Prop := fun x => ub P x ∧ ∀ y, ub P y → x ≤ y.
Definition min `{O:Order} (P:Ens) : X → Prop := fun x => lb P x ∧ P x.
Definition sup `{O:Order} (P:Ens) : X → Prop := fun x => ub P x ∧ P x.

Transparent lb ub glb lub.



Class CompleteLattice `{Ord:Order} :=
  {
    meet_set: Ens → X;
    join_set: Ens → X;

    meet_elim : ∀ (A:Ens) y, A y → ord (meet_set A) y;
    meet_intro : ∀ (A:Ens) y, (∀ x, A x → ord y x) → ord y (meet_set A);

    join_elim: ∀ (A:Ens) y, A y → ord y (join_set A);
    join_intro : ∀ (A:Ens) y, (∀ x, A x → ord x  y) → ord (join_set A) y;
}.


(* #[export] Hint Resolve meet_elim meet_intro join_elim join_intro:ia. *)

Notation "⊓":= meet_set.
Notation "⊔":= join_set.


Definition same_set `{X:SET} A B:= Same_set X A B.

Lemma same_set_sym `{X:SET} A B: @same_set X A B → same_set B A.
Proof. intros (H1,H2). split;intuition. Qed.

Infix "≅" := same_set (at level 69).


(** * Properties related to the lattice structure *)

Definition top `{CL:CompleteLattice}:= ⊔ (λ _ : X, True).
Definition bot `{CL:CompleteLattice}:= ⊓ (λ _ : X, True).
Notation "⊥" := bot.
Notation "⊤" := top.

Definition equiv `{O:Order} (a b:X):=ord a b /\ ord b a.
Notation "a ≈ b":=(equiv a b) (at level 25).



Lemma bot_min `{CL:CompleteLattice}:
  ∀ (a : X), bot ≤ a.
Proof.
  intro a. apply meet_elim. apply I. 
Qed.

Lemma top_max `{CL:CompleteLattice}:
  ∀ a : X, a ≤ top .
Proof.
  intro a. apply join_elim. apply I.
Qed.

Lemma meet_emptyset `{CL:CompleteLattice}:  (⊓ emptyset) ≈ ⊤.
Proof.
    split;[apply top_max|].
    apply meet_intro; intros x H; contradict H.
Qed.
  
Lemma join_emptyset `{CL:CompleteLattice}: ⊔ emptyset ≈ ⊥.
Proof.
    split;[|apply bot_min].
    apply join_intro; intros x H; contradict H.
Qed.



Definition subset `{X:SET} := fun P Q =>  Included X P Q.
Definition supset `{X:SET} := fun P Q =>  Included X Q P.
Notation " P ⊆ Q" := (subset P Q) (at level 75). 
Notation " P ⊇ Q" := (supset P Q) (at level 75).


(**  If two sets have the same elements, their meet are equivalent. *)

Lemma meet_subset `{CL:CompleteLattice}: 
  ∀ A B, subset A B -> ⊓ B ≤ ⊓ A.
Proof.
intros A B H.
apply meet_intro. intros x Ax.
apply meet_elim. apply H; intuition.
Qed.


Lemma meet_same_set_le `{CL:CompleteLattice}:
  ∀ A B, same_set A B -> ⊓ A ≤ ⊓ B.
Proof.
intros A B H; apply meet_intro.
intros x Hx; apply meet_elim.
apply H; exact Hx.
Qed.

Lemma meet_same_set `{CL:CompleteLattice}:
  ∀ A B, same_set A B -> ⊓ A ≈ ⊓ B.
Proof.
intros A B H. split;apply meet_same_set_le;auto.
apply same_set_sym;auto.
Qed.

Definition meet_family `{CL:CompleteLattice} I (f:I → X):X := ⊓ (fun x => ∃ (i:I), x = f i).
Definition join_family `{CL:CompleteLattice} I (f:I → X):X := ⊔ (fun x => ∃ (i:I), x = f i).

Notation "∩ f" := (meet_family f) (at level 60).
Notation " '⋂[' a ']' p " := ( ⊓ (fun x => ∃ a, x= p)) (at level 60).
Notation " '⋃[' a ']' p " := ( ⊔ (fun x => ∃ a, x= p)) (at level 60).
Definition inf `{CL:CompleteLattice} (f:X → X):= ⋂[a] ((f a)). 



Lemma meet_elim_trans `{CL:CompleteLattice}:
  ∀ (A : Ens) (z: X), (exists y , A y ∧ y ≤ z) → ⊓ A ≤ z.
Proof.
  intros A z (y,(Hy,Hyz)).
  apply (@ord_trans X Ord _ _ _ (meet_elim A y Hy) Hyz).
Qed.




(** * Tactics *)
(** We give a bunch of simple tactics to automatize the resolution
    of inequation involving meets and joins *)

Ltac later:=eapply ex_intro.
Ltac auto_refl:=repeat (
  match goal with
  | [|- _ ∧ _ ]=> split
  | [|- _ = _ ]=> reflexivity
  end).


Ltac auto_meet_elim_trans:=repeat (apply meet_elim_trans;later;split;[later;reflexivity|]);try reflexivity.
Ltac auto_meet_elim_risky:=repeat (apply meet_elim_trans;later;split;[later;auto_refl|]);repeat(reflexivity);repeat(assumption).
Ltac auto_meet_intro:= let H:=fresh "H" in let H1:=fresh "H" in let H2:=fresh "H" in let H3:=fresh "H" in apply meet_intro;try(intros ?x (?a,(H,(H1,(H2,H3)))));try(intros ?x (?a,(H,(H1,H2))));try(intros ?x (?a,(H,H1)));try(intros ?x (?a,H));try(subst).
Ltac auto_meet_leq:= repeat auto_meet_intro; auto_meet_elim_trans.


(** * Other properties *)



Lemma inf_elim_trans `{CL:CompleteLattice}:
  ∀ (f:X → X) (z:X), (exists b, f b ≤ z) → inf f ≤ z.
Proof.
  intros f z (b,Hb).
  eapply ord_trans.
  - apply meet_elim;exists b;reflexivity.
  - assumption.
Qed.



Lemma inf_comm_aux `{CL:CompleteLattice}:
  ∀(f:X→X→X), ⋂[a] (⋂[b] (f a b)) ≤ ⋂[b] (⋂[a] (f a b)).
Proof.
  intro f.  auto_meet_leq.
Qed.


Lemma inf_comm `{CL:CompleteLattice}:
  ∀(f:X→X→X), (⋂[a] (⋂[b] (f a b))) ≈ (⋂[b] (⋂[a] (f a b))).
Proof.
  intro f;split;apply (inf_comm_aux).
Qed.



Lemma meet_comm_aux `{CL:CompleteLattice}: 
∀(P:X→X→Prop) (f:X→X→X), 
          ⊓ (λ x,∃ a, x=⊓(λ y,∃ b, y=f a b ∧ P a b)) ≤ ⊓ (λ y,∃ b, y=⊓(λ x,∃ a, x = f a b ∧ P  a b)) .
Proof.
  intros P f.
  auto_meet_leq.
  now auto_meet_elim_risky.
Qed.


Lemma meet_comm `{CL:CompleteLattice}: 
∀(P:X→X→Prop) (f:X→X→X),
      ⊓ (λ x,∃ a, x=⊓(λ y,∃ b, y=f a b ∧ P a b)) ≈ ⊓ (λ y,∃ b, y=⊓(λ x,∃ a, x = f a b ∧ P  a b)).
Proof.
  intros P f. split;apply (meet_comm_aux).
Qed.

Lemma meet_fam_elim `{CL:CompleteLattice}: 
  ∀ I (f:I → X) (i:I), (∩ f)  ≤ f(i).
Proof.
  intros. apply meet_elim.
  exists i;reflexivity.
Qed.

Lemma meet_fam_intro `{CL:CompleteLattice}:
  ∀I f y, (∀ (i:I), y ≤ f i) → y ≤ ∩ f.
Proof.
  intros.
  apply meet_intro.
  intros.
  destruct H0 as [i Hi];rewrite Hi; auto.
Qed.


(** We define the lifting of the arrow (a ↦ b) for sets (A ↦ b, a ↦ B, A ↦ B) *)


Definition arrow_set_l `{X:SET} `{arrow:X → X → X} (A:Ens) (b:X):Ens :=
  fun x => ∃a, A a ∧ x = arrow a  b.
Definition arrow_set_r `{X:SET} `{arrow:X → X → X} (a:X) (B:Ens):Ens :=
    fun x => ∃b, B b ∧ x = arrow a b.
Definition arrow_set `{X:SET} `{arrow:X → X → X} (A:Ens) (B:Ens):Ens :=
    fun x => ∃a,∃b, A a ∧ B b ∧ x = arrow a b.



(** * Definition VI.2 : Implicative Structures *)


Class ImplicativeStructure `{CL:CompleteLattice} :=
  
  {
    arrow:X → X → X;

    arrow_mon_l: ∀ a a' b, ord a a' ->  ord (arrow a' b ) (arrow a b );
    arrow_mon_r: ∀ a b b', ord b b' ->  ord (arrow a b  ) (arrow a b');

    arrow_meet: ∀ a B, arrow a (meet_set B) ≈ meet_set (@arrow_set_r _ arrow a B)
  }.

Infix "↦" := arrow (at level 60, right associativity):ia_scope.
Notation "a ↪ B":= (@arrow_set_r _ _ a B) (at level 69):ia_scope.
Notation "⊓":= meet_set.
Notation "⊔":= join_set.

Generalizable Variables arrow meet_set join_set.


Lemma meet_arr `{IS:ImplicativeStructure}:
  forall (a:X) (B:Ens), a ↦ ⊓ B ≤ ⊓ (@arrow_set_r _ arrow a B).
Proof. intros. apply arrow_meet. Qed.

Lemma arr_meet `{IS:ImplicativeStructure}:
  forall (a:X) (B:Ens), ⊓ (@arrow_set_r _ arrow a B) ≤ a ↦ ⊓ B .
Proof. intros. apply arrow_meet. Qed.

Ltac trans_arr_meet:=eapply ord_trans;[|apply arr_meet].
Ltac trans_meet_arr:=eapply ord_trans;[|apply meet_arr].


(** ** Properties of implicative structures *)


(** Variance of the arrow *)
Lemma arrow_mon `{IS:ImplicativeStructure}: ∀ a a' b b' , a' ≤ a -> b ≤ b' -> arrow a b ≤ arrow a' b'.
Proof.
  intros.
  apply (ord_trans  _ (a' ↦ b)).
  - apply arrow_mon_l; auto.
  - apply arrow_mon_r; auto.
Qed.


  
  

(** * Encoding the λ-calculus         *)


(** ** Application *)
(** We begin by defining the application of "a" to "b", 
     denoted by "a@b". *)
     

Definition app `{IS:ImplicativeStructure} a b:= ⊓ (fun x => a ≤ b ↦ x).
Infix "@" := app (at level 59, left associativity).


(** Properties of the application *)

Lemma app_mon_l `{IS:ImplicativeStructure}:
  ∀ a b c, a ≤ b → a @ c ≤ b @ c.
Proof.
  intros a b c Hab.
  unfold app.
  apply meet_subset.
  intros x Hx.
  apply (ord_trans _ _ _  Hab Hx).
Qed.

Lemma app_mon_r `{IS:ImplicativeStructure}:
  ∀ a b c, b ≤ c → a @ b ≤ a @ c.
Proof.
  intros a b c Hbc.
  apply meet_subset.
  intros x Hx.
  apply (ord_trans _ _ _  Hx).
  now apply arrow_mon_l.
Qed.

Lemma app_mon `{IS:ImplicativeStructure}:
  ∀ a a' b b', a≤ a' → b ≤ b' → a @ b ≤ a' @ b'.
Proof.
  intros a a' b b' Ha Hb.
  eapply ord_trans;[apply (app_mon_l _ _ _ Ha)|].
  apply (app_mon_r _ _ _ Hb).
Qed.


(** ß-reduction is reflected by the order. *)

Lemma app_beta `{IS:ImplicativeStructure}:
  ∀ a b, (a ↦ b) @ a ≤ b.
Proof.
  intros a b.
  apply meet_elim.
  reflexivity.
Qed.


(** η-expansion is reflected by the reverse order. *)

Lemma app_eta `{IS:ImplicativeStructure}:
  ∀ a b, a ≤ b ↦ (a@b).
Proof.
  intros a b.
  eapply ord_trans;[|apply arr_meet].
  apply meet_intro.
  intros x (c,(Hx,Hc)). 
  now subst x.
Qed.


(** The application is a minimum.  *)

Lemma app_min `{IS:ImplicativeStructure}:
  ∀ a b, min (fun x => a ≤ b ↦ x) (a@b).
Proof.
intros a b.
split.
- unfold lb,app. intros y Hy. now apply meet_elim. 
- apply app_eta. 
Qed.


(** We have a fundamental adjunction.*)

Lemma adjunction `{IS:ImplicativeStructure}:
  ∀ a b c, a @ b ≤ c ↔ a ≤ b ↦ c.
Proof.
  intros.
  split;intros.
  - apply (ord_trans _ _ _ (app_eta a b)).
    now apply arrow_mon_r.
  - apply meet_elim.
    assumption.
Qed.


Lemma adj_imp `{IS:ImplicativeStructure}: ∀ a b c : X, a @ b ≤ c -> a ≤ b ↦ c.
Proof. intros. now apply adjunction. Qed.

Lemma adj_app `{IS:ImplicativeStructure}: ∀ a b c : X, a ≤ b ↦ c -> a @ b ≤ c.
Proof. intros. now apply adjunction. Qed.



(** ** Abstraction *)

(** We now define the abstraction of a function "f",
     which we denote by "λ' f". *)


Definition abs `{IS:ImplicativeStructure} f:= ⊓ (fun x => ∃ a, x = a ↦ f a).
Notation "λ- f":= (abs f) (at level 60):ia_scope.


(** Properties of the abstraction *)

(** Monotonicity *)

Lemma abs_mon `{IS:ImplicativeStructure}:
   ∀ f g, (∀a, f a ≤ g a) → (λ- f) ≤ (λ- g).
Proof.
intros f g H.
auto_meet_leq.
now apply arrow_mon_r.
Qed.


(** ß-reduction is reflected by the order. *)

Lemma betarule `{IS:ImplicativeStructure}:
  ∀ f a, (λ- f) @ a ≤ f a.
Proof.
  intros f a.
  do 2 apply meet_elim.
  exists a;reflexivity.
Qed.

Lemma beta_red `{IS:ImplicativeStructure}: 
  ∀ f t u, f t ≤ u → (λ- f)@t ≤ u.
Proof.
  intros f t u H.
  eapply ord_trans;[apply betarule|exact H].
Qed.



(* (** η-expansion is reflected by the reverse order. *) *)

(* Definition eta  `{IS:ImplicativeStructure}a := fun x => a @ x . *)
(* Lemma etarule `{IS:ImplicativeStructure}: *)
(*    ∀ a, a ≤ (λ- (eta a)). *)
(* Proof. *)
(*   intros a.  unfold eta,app,abs. *)
(*   apply meet_intro. *)
(*   intros b (x,Hb);subst. *)
(*   trans_arr_meet;apply meet_intro. *)
(*   intros z (b,(Hz,Hb)). subst. *)
(*   assumption. *)
(* Qed. *)

  

Ltac adjunction_mon:=
  repeat
    match goal with
      | |- (_ ↦ ?a ≤ _ ↦ ?a) => apply arrow_mon_l
      | |- (?a ↦ _ ≤ ?a ↦ _ )=> apply arrow_mon_r
      | |- _@?a ≤ _@?a       => apply app_mon_l
      | |- _  ≤ ?a ↦ (_@?a)=> apply adjunction
      | |- ?a ≤ _ ↦ (?a@_)=> apply adjunction
      | |- (?a ↦ _)@?a ≤ _ => apply adjunction
      | |- (_ ↦ ?a)@_ ≤ ?a => apply adjunction
    end;try (apply ord_refl); auto.



(** * Definition VI.3 -  Implicative Algebras *)

Definition Id `{IS:ImplicativeStructure} := ⋂[a] (a ↦ a).
Definition K `{IS:ImplicativeStructure} := ⋂[a] (⋂[b] (a ↦ b ↦ a)).
Definition S `{IS:ImplicativeStructure} := ⋂[a] (⋂[b] ⋂[c] ((a ↦ b ↦ c) ↦ (a ↦ b) ↦ a ↦ c)).
Definition cc `{IS:ImplicativeStructure} :=⋂[a] (⋂[b] (((a ↦ b) ↦ a) ↦ a)).


Class ImplicativeAlgebra `{IS:ImplicativeStructure}:=
  {
    separator: X → Prop;
    modus_ponens: ∀ a b, separator a → separator (arrow a b) → separator b;
    up_closed: ∀ a b, ord a b → separator a → separator b;
    sep_K : separator K;
    sep_S : separator S;
    (* sep_cc : separator cc *)
  }.

Class KImplicativeAlgebra `{IA:ImplicativeAlgebra}:=
  {
    sep_cc : separator cc
  }.



Generalizable Variables separator.

Notation "a ∈ʆ":= (separator a) (at level 80,no associativity).
Infix "@" := (app) (at level 59, left associativity).
Notation "λ- f":= (abs f) (at level 60).

(* #[export] Hint Resolve arrow_meet modus_ponens sep_K sep_S sep_cc:ia. *)
(* #[export] Hint Unfold arrow_set_l arrow_set_r arrow_set:ia. *)

Definition Succ:=Datatypes.S.


Section IA.
  Context `{IA:ImplicativeAlgebra}.


  (** ** Properties *)
  (** Separators are closed under application. *)
  
  Lemma app_closed : ∀ a b, a ∈ʆ → b ∈ʆ → a@b ∈ʆ.
  Proof.
    intros.
    apply (modus_ponens b (a@b)).
    - assumption.
    - apply (up_closed a).
      + apply adjunction.
        apply ord_refl.
      + assumption.
  Qed.
  
  Hint Resolve sep_S sep_K:ia. 

  Lemma lambda_K:
    K ≈ λ- (fun x=> λ- (fun y => x)).
  Proof.
    split.
    - auto_meet_intro. apply adjunction. auto_meet_intro.
      apply adjunction; auto_meet_elim_trans.
    - repeat auto_meet_intro.
      now repeat (apply adjunction,beta_red).
  Qed.

  
  (** ** S (λxyz.xy(zy) *) 

  Lemma lambda_S: S ≈ λ- (fun x => λ- (fun y => λ- (fun z => (x@z)@(y@z)))).
  Proof.
    split.
    - auto_meet_intro.  trans_arr_meet.
      apply meet_intro;intros y [z [[b Hb] Hy]];subst.
      do 2 (apply adj_imp). auto_meet_intro;subst;apply adj_imp.
      auto_meet_intro;intros x H. apply adj_imp in H.
      repeat apply adj_app.
      eapply ord_trans;[|apply arrow_mon_l,H].
      eapply ord_trans;[apply meet_elim;exists a0;reflexivity|].
      eapply ord_trans;[apply meet_elim;exists (b@a0);reflexivity|].
      auto_meet_elim_trans. repeat apply arrow_mon;try reflexivity. now apply adjunction. 
    - repeat auto_meet_intro. repeat (apply adjunction,beta_red).
      repeat (apply adj_app). repeat apply arrow_mon;try reflexivity. now apply adjunction.
  Qed.

  
  Lemma Id_SK : (S @ K) @ K ≤ Id.
  Proof.
    repeat (apply adj_app); eapply ord_trans;[apply lambda_S|].
    repeat (apply adjunction,beta_red). auto_meet_intro;apply adjunction,beta_red.
    repeat (apply adj_app);eapply ord_trans;[apply lambda_K|].
    now repeat (apply adjunction,beta_red).
  Qed.


  Lemma sep_Id: Id ∈ʆ.
  Proof.
    apply (up_closed  _ _ Id_SK).
    repeat (apply app_closed);auto with ia.
  Qed.

  
  (** ** Entailment *)

  Definition entails a b := (a ↦ b) ∈ʆ .
  Infix "⊢":= entails (at level 75).
  Definition equivalence a b := a ⊢ b ∧  b ⊢ a.
  Infix "⊣⊢":= equivalence (at level 80). 
  Definition neg a:=(a ↦ bot).
  Notation "¬ a":=(neg a).

  
  (** The ordering relation is including in the entailment relation *)
  
  Lemma subtyping : ∀ a b, a ≤ b → a ⊢ b.
  Proof.
    intros.
    apply (up_closed (a ↦ a)).
    + apply arrow_mon_r.
      assumption.
    + apply (up_closed (Id));[|apply sep_Id].
      apply meet_elim. exists a;reflexivity.
  Qed.



  (** COMPILATION OF λ-terms to the S-K basis **)
  
  Definition ifte `{X:SET} (b:bool) (t f:X):=
  match b with
  |true => t
  |false => f
  end.
  
  Inductive trm : SET :=
  | trm_bvar : nat → trm
  | trm_cvar : X → trm
  | tK : trm
  | tS : trm
  | trm_app  : trm → trm → trm.

  Notation "[ t ] u":= (trm_app (t) u ) (at level 69, right associativity).
  Notation "$ n":= (trm_bvar n) (at level 69, right associativity).
  
  
  Fixpoint lam (n:nat) (t: trm) {struct t}: trm:=
    match t with
    | trm_bvar m => ifte (Nat.eqb n m) ([[ tS ] tK] tK) ([tK] ($ m-1)) 
    | trm_app t u => [[tS] (lam n t) ] (lam n u)
    | _ => [tK] t
    end.
  
  Notation "λ+ t":= (lam 0 t) (at level 69, right associativity).

  Fixpoint sub (t: trm) (n:nat) (a:X) {struct t}: trm:=
    match t with
    | trm_bvar m => ifte (Nat.eqb n m) (trm_cvar a) ($ m) 
    | trm_app t u => [sub t n a] (sub u n a)
    | _ => t
    end.

  Notation "[ n ~> a ] t":=(sub t n a) (at level 69).
  
   

  Lemma eq_true: forall n n', n=n' -> Nat.eqb n n' = true.
  Proof. intros n n' H. subst. induction n';simpl;trivial. Qed.

  Lemma eq_false: forall n n', n<>n' -> Nat.eqb n n' = false.
  Proof.
    intros n;induction n; intros n' H;destruct n';trivial.
    - now contradict H. 
    - simpl. apply IHn. intros H';apply H;now subst. 
  Qed.

  Lemma sub_app: forall t a u n,  [n ~> a] ([t] u) =  [([n ~> a] t)] ([n ~> a] u).
  Proof. intros t a u n; reflexivity. Qed.

  Lemma sub_eq: forall a n,  [n ~> a] ($n) =  trm_cvar a.
  Proof. intros a n; simpl; rewrite eq_true;trivial.  Qed.

  Lemma sub_neq: forall a n m, n<>m -> [n ~> a] ($m) =  $m.
  Proof. intros a n m H; simpl; rewrite eq_false;trivial. Qed.

  Lemma sub_cste: forall a n b,  [n ~> a] (trm_cvar b) =  trm_cvar b.
  Proof. intros a n b;reflexivity. Qed.


  Lemma sub_lam: forall t a n,  [n ~> a] (λ+ t) =  λ+ ([Succ n ~> a] t).
  Proof.
    intro t; induction t; intros a m;trivial.
    - destruct (Nat.eq_dec n (Succ m)).
      + subst. simpl. replace (m-0) with m by lia.
        rewrite eq_true;trivial. 
      + rewrite sub_neq;[|intro;subst;now apply n0].
        destruct n;simpl;trivial.
        * rewrite eq_false;trivial.
          intro;subst;apply n0;f_equal;[|lia]. intro H;rewrite H at 1;reflexivity.
    - simpl; now rewrite IHt1,IHt2. 
  Qed.

  

  Ltac rw_sub:=repeat (repeat rewrite sub_lam;repeat rewrite sub_app);
    repeat rewrite sub_eq; repeat (rewrite sub_neq;[|auto]);repeat rewrite sub_cste.


  Fixpoint translate (t:trm):X:=
    match t with 
    | trm_bvar n => top
    | trm_cvar x =>  x
    | trm_app  t u => (translate t)@ (translate u)
    | tK => K
    | tS => S
    end.


  Fixpoint fv (t:trm):nat:=
    match t with 
    | trm_bvar n =>  n+1
    | trm_app  t u => max (fv t) (fv u)
    | _ => 0
    end.

  Lemma fv_lam: forall t n, fv t <= 1+n -> fv (lam n t) <= n.
  Proof.
    intro t; induction t; intros.
    - simpl in H.  simpl.
      destruct (Nat.eq_dec n n0);subst.
      * rewrite eq_true;simpl; lia. 
      * rewrite eq_false;simpl;lia.
    - simpl;lia.
    - simpl; lia.
    - simpl; lia.
    - simpl in *.
      apply Nat.max_lub.
      apply IHt1. apply (Nat.max_lub_l _ _ _ H).
      apply IHt2. apply (Nat.max_lub_r _ _ _ H).
  Qed.

  Fixpoint fc (t:trm):bool:=
    match t with 
    | trm_cvar a =>  true
    | trm_app  t u => orb (fc t) (fc u)
    | _ => false
    end.

 
  
  Lemma translate_app: forall t u,  translate ([t] u) = translate (t) @ translate (u).
  Proof. reflexivity. Qed.
  
  Lemma translate_lam: forall t,  translate (λ+ t) ≤ λ- (fun x => translate ([0 ~> x] t)).
  Proof.
    induction t;try (auto_meet_intro; apply adj_app;now auto_meet_elim_risky). 
    - destruct n;simpl. 
      + apply Id_SK. 
      + auto_meet_intro. apply adj_app;auto_meet_elim_risky.
    - auto_meet_intro. rw_sub. rewrite translate_app.
      simpl.
      eapply ord_trans;[apply app_mon_r,IHt2|]. apply adj_app.
      eapply ord_trans;[apply app_mon_r,IHt1|]. apply adj_app.
      eapply ord_trans;[apply lambda_S|].
      do 3 (apply adjunction,beta_red).
      apply app_mon;apply adj_app;auto_meet_elim_trans.
  Qed.

  
  Lemma translate_cvar: forall a ,  translate (trm_cvar a) = a.
  Proof. reflexivity. Qed.


  
  Lemma translate_beta: forall t a,  translate (λ+ t) @ a ≤ translate ([0 ~> a] t).
  Proof.
    intros. eapply adj_app,ord_trans;[apply translate_lam|];auto_meet_elim_trans.
  Qed.

  Definition closed t:= fc t = false /\ fv t <= 0.

  Lemma sep_closed_trm: forall t, closed t-> (translate t)∈ʆ.
  Proof.
    intros t (FC,FV); induction t; intros.
    - simpl in FV.  lia. 
    - simpl in FC. inversion FC.  
    - simpl. apply sep_K.
    - simpl. apply sep_S.
    - simpl in * .
      apply Bool.orb_false_elim in FC.
      destruct FC as (FC1,FC2).
      apply app_closed.
      + apply IHt1. assumption. lia.
      + apply IHt2. assumption. lia.
  Qed.

  
  Lemma sep_translated_closed: forall t u, closed u -> translate u ≤ t -> t ∈ʆ.
  Proof.
    intros t u Hu Ht.
    apply (up_closed _ _ Ht). now apply sep_closed_trm.
  Qed.

  Ltac trm_sep:=  repeat apply app_closed;try apply sep_S;try apply sep_K.
  Ltac auto_closed:=split;try reflexivity.
  Ltac try_beta:=
    try (apply adj_imp; eapply ord_trans;[apply translate_beta|]; rw_sub).

  Ltac auto_real:=
    repeat 
      match goal with
      |  |- ?a ≤ ?a => reflexivity
      |  |- _ ≤ λ- _ => auto_meet_intro      
      |  |- _ ≤ meet_set _ => auto_meet_intro
      |  |- ?a ≤ _ ↦ ?a @ _ => apply adj_imp,app_mon_r
      |  |- ?a ≤ _ ↦ _ ↦ ?a @ _ @ _ => apply adj_imp,adj_imp,app_mon_r
      |  |- ?a ≤ _ ↦ _ ↦ ?a @ _ @ _ => apply adj_imp,adj_imp,app_mon
      |  |- _ @ _ ≤ _ => apply adj_app
      |  |- _ ↦ ?a ≤ _ ↦ ?a => apply arrow_mon_l
      |  |- translate (λ+ _ ) ≤ _ ↦ _ => try_beta
      |  |- context G [translate ([ _ ] _ )]  => rewrite translate_app
      |  |- context G [translate( trm_cvar _)] => rewrite translate_cvar
      |  |- meet_set _ ≤ _ => try now auto_meet_elim_trans
      |  |- _ ↦ _ ≤ _ ↦ _ => apply arrow_mon
      end.

  Ltac realizer t:=
    apply sep_translated_closed with t;[auto_closed|auto_real]. 

  
  Lemma composition: ∀ a b c, (a ↦ b) ↦ (b ↦ c) ↦ (a ↦ c) ∈ʆ.
  Proof.
    intros.
    realizer (λ+ λ+ λ+ ([ $ 1 ] ([$ 2] $ 0))).
  Qed.  (** λxyz.y(xz) *) 

  Lemma entails_real : forall x y, (x ⊢ y <-> (exists s, s∈ʆ /\ s ≤ x ↦ y)).
  Proof.
    intros x y;split;intro H.
    exists (x ↦ y);split;[apply H|reflexivity].
    destruct H as (s,(Hs,Hxy)). apply (up_closed s); assumption.
  Qed.
  
  (** The entailment relation is a preorder *)

  Lemma entails_refl : reflexive X entails.
  Proof.
    unfold entails,reflexive.
    intro a.
    realizer (λ+ $0).
  Qed.

  Lemma entails_trans : transitive X entails.
  Proof.
    unfold entails,transitive.
    intros a b c Ha Hb.
    apply (modus_ponens (b ↦ c));auto.
    apply (modus_ponens (a ↦ b));auto.
    realizer (λ+ λ+ λ+ ([$1] ([$2] $0))).
  Qed.
  
  Lemma modus_ponens_later: ∀ a, (exists b, b ∈ʆ ∧ b ⊢ a ) → a ∈ʆ. 
  Proof.
    intros a (b,(Hb,Ha)).
    apply up_closed with ((b ↦a)@b).
    adjunction_mon.
    now apply app_closed.
  Qed.

  Lemma exfalso_S: ∀ a, ⊥ ⊢ a.
  Proof.
    intro.
    apply (subtyping _ _ (bot_min a)).
  Qed.

  
  Lemma true_S: ∀ a, a ⊢ ⊤.
  Proof.
    intro.
    apply (subtyping _ _ (top_max a)).
  Qed.



  (** *** Negation *)

  Lemma dni: ∀ a, a ⊢ ¬ (¬ a).
  Proof.
    intro. unfold neg.
    realizer (λ+ λ+ ([$0] $1)).
  Qed.

  Lemma dne `{sep_cc: cc∈ʆ}: ∀ a, (¬ (¬ a)) ⊢ a.
  Proof.
    intro. unfold entails,neg.
    apply (up_closed (((a ↦ ⊥ ) ↦ a) ↦ a)).
    - adjunction_mon. apply bot_min.
    - apply (up_closed cc);auto. 
      auto_meet_elim_trans.
  Qed.


  Lemma dn `{sep_cc: cc∈ʆ}: ∀ a, a ⊣⊢ ¬ ¬ a.
  Proof.
    intros;split;[apply dni|apply (@dne  sep_cc)].
  Qed.

  

  (** The relation of entailment is compatible with the arrow: *)

  Lemma arrow_entails_mon_r: ∀ a b b', b ⊢ b' → a ↦ b ⊢ a ↦ b'.
  Proof.
    intros a b b' H.
    apply modus_ponens_later. exists (b ↦ b'). split;auto.
    realizer (λ+ λ+ λ+ ([ $2 ] ([ $1 ] $0))).
  Qed.

  Lemma arrow_entails_mon_l: ∀ a a' b, a ⊢ a' → a' ↦ b ⊢ a ↦ b.
  Proof.
    intros a a' b H.
    apply modus_ponens_later. exists (a ↦ a'). split;auto.
    realizer (λ+ λ+ λ+ ([ $1 ] ([ $2 ] $0))).
  Qed.


  Lemma arrow_entails_mon: ∀ a a' b b', a' ⊢ a → b ⊢ b' → a ↦ b ⊢ a' ↦ b'.
  Proof.
    intros a a' b b' Ha Hb.
    apply modus_ponens_later. exists (b ↦ b'). split;auto.
    apply modus_ponens_later. exists (a' ↦ a). split;auto.
    realizer (λ+ λ+ λ+ λ+ ([ $2 ] ([ $1 ] ([ $3 ] $0)))).
  Qed.



  
  (** We define simple tactics to automatize the proof by beta reduction 
  for goals of the shape λ- f ≤ a ↦ b  or   λ- f ≤ ⋂[_] t.  *)
  
  Ltac lam_leq:=apply adjunction,beta_red;try (adjunction_mon).
  Ltac lam_meet:=auto_meet_intro;apply adjunction,beta_red.

  
  (** *** Quantifiers*)
  
  Definition forallt:=meet_family.
 
  Notation "[∀] a":=(forallt a) (at level 69).
   
  (** We prove the semantic typing rules for the ∀ type. *)
  
  Lemma type_fa_intro:
    ∀ I (a:I→X) t, (∀ i,  t ≤ a i) →  t ≤ [∀] a.
  Proof.
  intros I a t H. 
  now auto_meet_intro.
  Qed.
  
  Lemma type_fa_elim:
    ∀ I (a:I→X) t, t ≤ [∀] a → ∀i, t≤ a i.
  Proof.
  intros I a t H i.
  eapply ord_trans;[exact H|].
  auto_meet_elim_trans.
  Qed.


  Definition existst `{I:Type} (a:I→X):=⋂[c](meet_family (fun (i:I)=> a i ↦ c) ↦ c).
  Notation "[∃] a":=(existst a) (at level 69).
   
  
  (** We prove the semantic typing rules for the ∃ type. *)
  
  Lemma type_ex_intro:
    ∀ I (a:I→X) t, (∃ i,  t ≤ a i) →  λ- (fun x => x@t) ≤ [∃] a.
  Proof.
    intros I a t [i H].
    lam_meet.
    apply adjunction;auto_meet_elim_trans.
    apply arrow_mon_l;exact H.
  Qed.

  
  Definition ext_i := λ- (fun t => λ- (fun x => x@t)).
  Lemma ext_i_sep : ext_i ∈ʆ.
  Proof. unfold ext_i. realizer (λ+ λ+ [$0] $1).  Qed.

  Lemma ext_intro : forall (I:SET) (a:I->X) (i:I), ext_i ≤ a i ↦ [∃] a.
  Proof.
    intros I a i;unfold ext_i;apply adjunction,beta_red.
    apply type_ex_intro. now exists i.
  Qed.

   
  Lemma ext_elim:
    ∀ I (a:I→X) u c, (∀i, u ≤ a i ↦ c) → ([∃] a)@u≤ c.
  Proof.
    intros I a u c Hu.
    apply adjunction.
    auto_meet_elim_trans. apply arrow_mon_l.
    auto_meet_intro.
    apply Hu.
  Qed.
  
  Lemma type_ex_elim:
    ∀ I (a:I→X) t u c, t ≤ [∃] a → (∀i x, x≤ a i → u x≤ c) → (t@λ- (fun x => u x))≤ c.
  Proof.
  intros I a t u c H Hu.
  apply adjunction.   eapply ord_trans;[exact H|].
  auto_meet_elim_trans.  apply arrow_mon_l.
  apply meet_intro. intros x [i Hx]. subst.
  lam_leq. now apply (Hu i).
  Qed.
 
  

  (** *** Meet: × *)
  
  Definition prodt a b :=(⋂[c] ((a ↦ b ↦ c) ↦c)).
  Notation "a × b":=(prodt a b) (at level 69).
  Definition pair a b :=λ- (fun x => x@ a @ b).
  Definition proj1:= λ- (fun x => λ- (fun y => x)).
  Definition proj2:= λ- (fun x => λ- (fun y => y)).

  Transparent proj1 proj2.
  
  (** ~> Proposition 37 <~ *)
  (** We prove the semantic typing rules for the × type. *)
  
  Lemma type_pair:
    ∀ a b t u, t ≤ a → u ≤ b → pair t u ≤ a × b .
  Proof.
  intros a b t u Ha Hb.
  apply meet_intro.
  intros x [c H]. subst.
  lam_leq.
  do 2 apply adjunction.
  do 2 (apply arrow_mon;intuition).
  Qed.
  
  Lemma type_proj1:
    ∀ a b t , t ≤ a × b → t@proj1  ≤ a.
  Proof.
  intros a b t Ha.
  apply adjunction.
  eapply ord_trans;[exact Ha|].
  auto_meet_elim_trans. apply arrow_mon_l.
  now do 2 lam_leq.
  Qed.
  
  Lemma type_proj2:
    ∀ a b t , t ≤ a × b → t@proj2  ≤ b.
  Proof.
  intros a b t Ha.
  apply adjunction.
  eapply ord_trans;[exact Ha|].
  auto_meet_elim_trans. apply arrow_mon_l.
  now do 2 lam_leq.
  Qed.



  Lemma ha_adjunction:
    ∀ a b c, a ⊢ b ↦ c <-> a × b ⊢ c.
  Proof.
    intros a b c;split;intro H.
    - apply modus_ponens_later.
      exists (a ↦ b ↦ c);split;auto.
      unfold prodt.
      realizer (λ+ λ+ [$0] $1).
    - apply modus_ponens_later.
      exists ((a × b) ↦ c);split;auto.
      unfold entails,prodt.
      realizer (λ+ λ+ λ+ [$2] (λ+ ([[$0] $2] $1))).
  Qed.      

  (** We prove that × is indeed a meet in the induced Heyting prealgebra: *)
  
  Lemma prodt_l:
      ∀ a b, a × b ⊢ a.
  Proof.
  intros a b. unfold prodt.
  realizer (λ+ [$0] (λ+ λ+ $1)).
  auto_meet_elim_trans. apply arrow_mon_l.
  auto_real.
  Qed.      

  Lemma prodt_r:
      ∀ a b, a × b ⊢ b.
  Proof.
  intros a b.  unfold prodt.
  realizer (λ+ [$0] (λ+ λ+ $0)).
  auto_meet_elim_trans. apply arrow_mon_l.
  auto_real.
  Qed.      

  Lemma prodt_intro:
      ∀ a b c, c ⊢ a → c ⊢ b → c ⊢ a × b.
  Proof.
  intros a b c Ha Hb.
  apply modus_ponens with (a:=c↦b);auto.
  apply modus_ponens with (a:=c↦a);auto.
  (* λtucz.z(tc)(uc) *)
  unfold prodt;realizer (λ+ λ+ λ+ λ+ [[$0] ([$3] $1)] ([$2] $1)).
  Qed.      


    
  (** *** Join: + *)
  
  Definition sumt a b :=(⋂[c] ((a ↦ c) ↦ (b ↦ c) ↦c)).
  Notation "a ⊕ b":=(sumt a b) (at level 69).
  Definition inj1 t:= λ- (fun x => λ- (fun y => x@t )).
  Definition inj2 t:= λ- (fun x => λ- (fun y => y@t)).
  Definition case t u v := (t@λ- (fun x => u x)) @ λ- (fun x => v x).
  
  
  (** We prove the semantic typing rules for the + type. *)
  
  Lemma type_inj1:
    ∀ a b t , t ≤ a  → inj1 t  ≤ a ⊕ b.
  Proof.
  intros a b t Ha.
  lam_meet. lam_leq. 
  Qed.
  
  Lemma type_inj2:
    ∀ a b t , t ≤ b  → inj2 t  ≤ a ⊕ b.
  Proof.
  intros a b t Ha.
  lam_meet. lam_leq. 
  Qed.
  
  
  Lemma type_case:
    ∀ a b c t u v, t ≤ a ⊕ b → (∀x,x≤a → u x≤ c) → (∀x,x≤b → v x≤ c)
    → case t u v ≤ c.
  Proof.
  intros a b c t u v Ht Hu Hv.
  do 2 apply adjunction.
  eapply ord_trans;[exact Ht|].
  auto_meet_elim_trans. 
  apply arrow_mon;[|apply arrow_mon_l];lam_leq;intuition.
  Qed.
  
  (** We prove that + is indeed a join in the induced Heyting prealgebra: *)
  
  Lemma sumt_l:
      ∀ a b, a ⊢ a ⊕ b.
  Proof.
  intros a b.
  realizer (λ+ λ+ λ+ [$1] $2).  (* λxyz.yx *)
  auto_meet_intro.
  auto_real.
  Qed.      

  Lemma sumt_r:
      ∀ a b, b ⊢ a ⊕ b.
  Proof.
  intros a b.
  realizer (λ+ λ+ λ+ [$0] $2). (* λxyz.zx *)
  auto_meet_intro.
  auto_real.
  Qed.      


  Lemma sumt_elim:
      ∀ a b c, a ⊢ c → b ⊢ c → a ⊕ b ⊢ c.
  Proof.
  intros a b c Ha Hb.
  apply modus_ponens with (a:=b↦c);auto.
  apply modus_ponens with (a:=a↦c);auto.
  realizer (λ+ λ+ λ+ [[$0] $2] $1).    (* λxyz.zxy *)
  auto_meet_elim_trans.
  Qed.   

  Obligation Tactic := intros;simpl in *;apply entails_real.
  Program Definition IA_PHA : PreHeytingAlgebra :=
    preheyting_algebra X (fun a b => exists s, separator s /\ s ≤ a ↦ b) (top)
                       (fun a b => a × b) (bot)  (fun a b => a ⊕ b) (fun a b => a ↦ b)
                       _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation. apply entails_refl. Defined.
  Next Obligation. apply entails_real in H,H0. eapply entails_trans. apply H. assumption. Defined.
  Next Obligation. apply true_S. Defined.
  Next Obligation. apply entails_real in H,H0. now apply prodt_intro. Defined.
  Next Obligation. apply prodt_l. Defined.
  Next Obligation. apply prodt_r. Defined.
  Next Obligation. apply exfalso_S. Defined.
  Next Obligation. apply sumt_l. Defined.
  Next Obligation. apply sumt_r. Defined.
  Next Obligation. apply entails_real in H,H0. now apply sumt_elim. Defined.
  Next Obligation. apply entails_real in H. now apply ha_adjunction. Defined.
  Next Obligation.
    apply up_closed with  (λ- (fun x => x@(λ- (fun y => λ- (fun z => z@y))))).
    - apply adjunction, beta_red,adjunction.
      auto_meet_elim_trans.
      now apply arrow_mon_l,adjunction,beta_red,adjunction,beta_red,adjunction.
    - realizer (λ+ [$0] λ+ λ+ [$0] $1). Defined.
  

  
End IA.


Record ImplicativeAlgebraObject : Class := implicative_algebra_object {
  IASet : SET;
  IAOrder : @Order IASet;
  IALattice : @CompleteLattice IASet IAOrder;
  IAStructure : @ImplicativeStructure IASet IAOrder IALattice;
  IAAlgebra : @ImplicativeAlgebra IASet IAOrder IALattice IAStructure
}.
Definition IAOrd (A : ImplicativeAlgebraObject) : IASet A -> IASet A -> Prop
:= @ord _ (IAOrder A).
Definition IAmeet (A : ImplicativeAlgebraObject) : (IASet A -> Prop) -> IASet A
:= @meet_set _ _ (IALattice A).
Definition IAarrow (A : ImplicativeAlgebraObject) : IASet A -> IASet A -> IASet A
:= @arrow _ _ _ (IAStructure A).
Definition IASeparator (A : ImplicativeAlgebraObject) : IASet A -> Prop
:= @separator _ _ _ _ (IAAlgebra A).


Notation " a ↦ b":=(IAarrow _ a b).
Notation " ⊓ A ":=(IAmeet _ A) (at level 60).


Definition IAapp {A:ImplicativeAlgebraObject} :=@app _ _ _ (IAStructure A).
Definition IAabs {A:ImplicativeAlgebraObject} :=@abs _ _ _ (IAStructure A).
Definition lamIA (IA:ImplicativeAlgebraObject):=@lam (IASet IA).


(** Tactics to automatize proof via a closed realizer *)

Notation "[ t ] u":= (trm_app (t) u ) (at level 69, right associativity).
Notation "$ n":= (trm_bvar n) (at level 69, right associativity).
Notation "λ+ t":= (lam 0 t) (at level 69, right associativity).
Notation "λ[ IA ]+ t":= (lamIA IA 0 t) (at level 69, right associativity).
Notation "[ n ~> a ] t":=(sub t n a) (at level 69).

Ltac rw_sub:=repeat (repeat rewrite sub_lam;repeat rewrite sub_app);
             repeat rewrite sub_eq; repeat (rewrite sub_neq;[|auto]);repeat rewrite sub_cste.

Ltac auto_closed:=split;try reflexivity.
Ltac try_beta:=
  try (apply adj_imp; eapply ord_trans;[apply translate_beta|]; rw_sub).
Ltac auto_trans_le:=unfold IAapp,IAabs,lamIA;
  repeat 
    match goal with
    |  |- ?a ≤ ?a => reflexivity
    |  |- _ ≤ abs _ => auto_meet_intro      
    |  |- _ ≤ meet_set _ => auto_meet_intro
    |  |- ?a ≤ arrow _ (app   ?a  _)=> apply adj_imp,app_mon_r
    |  |- ?a ≤ arrow ?b (arrow ?c  (?a @ ?b @ ?c)) => apply adj_imp,adj_imp,app_mon_r
    |  |- ?a ≤ arrow _ (arrow _ (?a @ _ @ _)) => apply adj_imp,adj_imp,app_mon
    |  |- app _  _ ≤ _ => apply adj_app
    |  |- arrow _ ?a ≤ arrow _ ?a => apply arrow_mon_l
    |  |- translate (λ+ _ ) ≤ arrow _ _ => try_beta
    |  |- context G [translate ([ _ ] _ )]  => rewrite translate_app
    |  |- context G [translate( trm_cvar _)] => rewrite translate_cvar
    |  |- meet_set _ ≤ _ => try now auto_meet_elim_trans
    |  |- _ ↦ _ ≤ _ ↦ _ => apply arrow_mon
    end.

Ltac realizer t:=
    apply sep_translated_closed with t;[auto_closed|auto_trans_le]. 

Ltac realizerIA IA t:=
    apply (@sep_translated_closed _ _ _ _ (IAAlgebra IA)) with t;[auto_closed|auto_trans_le]. 






Record ImplicativeAlgebraMorphism {int : Prop} {A1 A2 : ImplicativeAlgebraObject} : Type := implicative_algebra_morphism {
  IAMap : IASet A1 -> IASet A2;
  iamsep : forall s1 : IASet A1, IASeparator A1 s1 -> IASeparator A2 (IAMap s1);
  iambinary : forall s1 : IASet A1, IASeparator A1 s1 -> IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a1 a1' a1'' : IASet A1, IAOrd A1 s1 (IAarrow A1 a1 (IAarrow A1 a1' a1'')) /\ IAarrow A2 (IAMap a1) (IAarrow A2 (IAMap a1') (IAMap a1'')) = a2));
  iammeet : IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists as1 : IASet A1 -> Prop, IAarrow A2 (IAmeet A2 (fun a2 : IASet A2 => exists2 a1 : IASet A1, as1 a1 & IAMap a1 = a2)) (IAMap (IAmeet A1 as1)) = a2));
  iamarrow : IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a1 a1' : IASet A1, IAarrow A2 (IAarrow A2 (IAMap a1) (IAMap a1')) (IAMap (IAarrow A1 a1 a1')) = a2));
  iamdense : exists2 f : IASet A2 -> IASet A1, IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a2' : IASet A2, IAarrow A2 a2' (IAMap (f a2')) = a2)) /\ IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a2' : IASet A2, IAarrow A2 (IAMap (f a2')) a2' = a2)) &
     int -> exists2 finv : IASet A1 -> IASet A2, (fun p1 : IASet A1 => p1) = (fun p1 : IASet A1 => f (finv p1)) & (fun p2 : IASet A2 => p2) = (fun p2 : IASet A2 => finv (f p2))
}.
Arguments ImplicativeAlgebraMorphism : clear implicits.
Arguments implicative_algebra_morphism : clear implicits.

Definition ImplicativeAlgebraRefines {int : Prop} {A1 A2 : ImplicativeAlgebraObject} (F G : ImplicativeAlgebraMorphism int A1 A2) : Prop
:= IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a1 : IASet A1, IAarrow A2 (IAMap F a1) (IAMap G a1) = a2)).


Obligation Tactic:=intros.
Program Definition ia_id (int : Prop) (A : ImplicativeAlgebraObject) : ImplicativeAlgebraMorphism int A A
:= implicative_algebra_morphism int A A (fun a : IASet A => a) _ _ _ _ _.
Next Obligation.
  trivial.
Qed.
Next Obligation.
  apply up_closed with s1;trivial. auto_meet_intro.
  assumption.
Qed.
Next Obligation.
  simpl. eapply up_closed;[|apply sep_Id].
  auto_meet_intro;subst.
  apply adjunction. auto_meet_intro;intros.
  eapply ord_trans;[apply betarule|].
  apply meet_elim. exists x;trivial.
Qed.
Next Obligation.
  eapply up_closed;[|apply sep_Id].
  auto_meet_intro. 
  auto_meet_elim_trans. apply arrow_mon;reflexivity.
Qed.
Next Obligation.
  simpl. exists (fun a => a).  split;
  eapply up_closed;[|apply sep_Id| |apply sep_Id];auto_meet_intro;
    auto_meet_elim_trans;apply arrow_mon;reflexivity.
  intro.  exists (fun a => a);reflexivity.
Qed.



  
  

  
Lemma iammeet_real {A1 A2:ImplicativeAlgebraObject} (IAMap : IASet A1 -> IASet A2):
  IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists as1 : IASet A1 -> Prop, IAarrow A2 (IAmeet A2 (fun a2 : IASet A2 => exists2 a1 : IASet A1, as1 a1 & IAMap a1 = a2)) (IAMap (IAmeet A1 as1)) = a2))
  <->  exists (s:IASet A2), IASeparator _ s  /\ forall as1, IAOrd A2 (IAapp s  (IAmeet A2 (fun a2 : IASet A2 => exists2 a1 : IASet A1, as1 a1 & IAMap a1 = a2)))  (IAMap (IAmeet A1 as1)).
Proof.
  split.
  - intros. eexists;split;[apply H|].
    intros A. apply adjunction. apply meet_elim.
    exists A. reflexivity. 
  - intros  [s [Hs H]].
    eapply up_closed;[|apply Hs].
    auto_meet_intro.
    apply adjunction. apply H.
Qed.

Lemma iamunary {int:Prop} {A1 A2 : ImplicativeAlgebraObject} (F : ImplicativeAlgebraMorphism int A1 A2) :
  forall s1, IASeparator A1 s1 -> IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a1 a1' : IASet A1, IAOrd A1 s1 (IAarrow A1 a1 a1') /\ IAarrow A2 (IAMap F a1) (IAMap F a1')  = a2)).
Proof.
  destruct F. rename IAMap0 into F.
  intros;simpl.
  pose (k:=(@K _ _  _ (IAStructure A1)) ).
  pose (s2:=IAapp  (⊓ (λ a2 : IASet A2,
                        ∃ a1 a1' a1'' : IASet A1,
                          IAOrd A1 (IAapp (IAabs (fun x=> (IAabs (fun y => x)))) s1) (a1 ↦ a1' ↦ a1'') ∧ F a1 ↦ F a1' ↦ F a1'' = a2)) (F k)).
  apply up_closed with s2.
  auto_meet_intro.
  apply adjunction. 
  apply meet_elim. do 3 eexists;split;[|reflexivity].
  apply beta_red.
  transitivity (k ↦ s1);[|apply arrow_mon_r;trivial].
  apply meet_elim. exists k;reflexivity.
  apply app_closed;[|apply iamsep0,sep_K].
  apply iambinary0.
  apply app_closed.

  eapply up_closed;[|apply sep_K].
  apply lambda_K.
  assumption.
Qed.

Lemma iamunary_real {int:Prop} {A1 A2 : ImplicativeAlgebraObject} (F : ImplicativeAlgebraMorphism int A1 A2) :
  IASeparator A2 (IAmeet A2 (fun a2 : IASet A2 => exists a1 a1' : IASet A1, IAarrow A2 (IAMap F (IAarrow A1 a1 a1')) (IAarrow A2 (IAMap F a1) (IAMap F a1'))  = a2)).
Proof.
destruct F;rename IAMap0 into F;simpl.
eapply up_closed;[|apply (iambinary0 _ sep_Id)].
auto_meet_intro.
apply meet_elim;repeat eexists.
apply meet_elim;repeat eexists.
Qed.


Program Definition ia_comp {int : Prop} {A1 A2 A3 : ImplicativeAlgebraObject} (F : ImplicativeAlgebraMorphism int A1 A2) (G : ImplicativeAlgebraMorphism int A2 A3) : ImplicativeAlgebraMorphism int A1 A3
:= implicative_algebra_morphism int A1 A3 (fun a1 : IASet A1 => IAMap G (IAMap F a1)) _ _ _ _ _.
Obligation Tactic:=intros.
Next Obligation. do 2 apply iamsep. assumption. Qed.
Next Obligation.
  destruct F,G;simpl. rename IAMap0 into F,IAMap1 into G.
  eapply up_closed;[|apply (iambinary1 (⊓ (λ a2 : IASet A2,
                        ∃ a1 a1' a1'' : IASet A1,
                          IAOrd A1 s1 (a1 ↦ a1' ↦ a1'') ∧ F a1 ↦ F a1' ↦ F a1'' = a2)))].
  auto_meet_intro. rename H0 into b,H1 into c. 
  apply meet_elim. exists (F a);exists (F b); exists (F c);split;[|reflexivity].
  apply meet_elim. exists  a;exists b; exists c;split;[|reflexivity]. assumption.
  apply iambinary0. assumption.
Qed.
Next Obligation.
  assert (HG:=iamunary G).
  assert (HF:=iamunary F).
  destruct F,G;simpl in *. rename IAMap0 into F,IAMap1 into G.
  apply iammeet_real in iammeet1,iammeet0.
  destruct iammeet0 as (sf,(sep_sf,Hsf)).
  destruct iammeet1 as (sg,(sep_sg,Hsg)).
  pose (s1:= ⊓ (λ a2 : IASet A3, ∃ A,
         (⊓ (λ a0, exists a1 , A a1 /\ G (F a1) = a0)) ↦ G (⊓ (fun a => exists x, A x /\ a=F x)) = a2)).
  pose (s2:= ⊓ (λ a2 : IASet A3, ∃ A,
         (G (⊓ (fun a => exists x, A x /\ a=F x)) ↦ G (F (⊓ A)) = a2))).
  eapply (up_closed  (((λ- (fun y=> (λ- (fun z=> (λ- (fun x=> y @(z@x)))))))@s2)@s1)).
  - apply (@adj_app _ _ _ (IAStructure A3)).
    apply (@beta_red _ _ _ (IAStructure A3)).
    apply adjunction.
    apply beta_red.
    apply meet_intro;intros a [A Hx];subst.
    apply adjunction.
    apply beta_red.
    apply (@adj_app _ _ _ (IAStructure A3)).
    apply ord_trans with ( G (⊓ (λ a : IASet A2, ∃ x : IASet A1, A x ∧ a = F x)) ↦ G (F (⊓ A))).
    + apply meet_elim. exists A;reflexivity.
    + apply arrow_mon;[|reflexivity].  apply (@adj_app _ _ _ (IAStructure A3)).
      apply ord_trans with ((⊓ (λ a0 : IASet A3, ∃ a1 : IASet A1, A a1 ∧ G (F a1) = a0))
                            ↦ G (⊓ (λ a : IASet A2, ∃ x : IASet A1, A x ∧ a = F x))).
      * apply meet_elim. exists A;reflexivity.
      * apply arrow_mon;[|reflexivity]. auto_meet_intro.
        apply meet_elim. exists a;trivial.
  - repeat (apply app_closed).
    + realizer (λ[A3]+ λ+ λ+ ([$2] ([$1] $0))).
    + pose (s3:=⊓ (λ a2 ,   ∃ A : IASet A1 → Prop,
               ⊓ (λ a : IASet A2, ∃ x : IASet A1, A x ∧ a = F x) ↦ F (⊓ A) = a2)).
      specialize (HG s3).
      eapply up_closed;[|apply HG].
      auto_meet_intro. rename a into A.
      apply meet_elim. eexists;eexists;split;[|reflexivity].
      apply meet_elim. exists A. reflexivity.
      eapply up_closed ;[|apply sep_sf].
      auto_meet_intro.
      apply adjunction.
      transitivity ((IAapp sf (⊓ (λ a2 : IASet A2, exists2 a1 : IASet A1, a a1 & F a1 = a2)))).
      apply app_mon_r. apply meet_intro;intros x (z,H,H');subst.
      apply meet_elim. exists z;split;trivial.
      apply Hsf.
    +  eapply up_closed ;[|apply sep_sg].
      auto_meet_intro.
      apply adjunction.
      eapply ord_trans;[|apply Hsg].
      apply app_mon_r. apply meet_intro;intros x (z,(y,(H,Hy)),H');subst.
      apply meet_elim. exists y;split;trivial.
Qed.
Next Obligation.
  assert (HG:=iamunary G).
  assert (HF:=iamunary F).
  destruct F,G;simpl in *. rename IAMap0 into F,IAMap1 into G.
  pose (s2:=(⊓ (λ a2 , ∃ a1 a1', (G (F a1) ↦ G (F a1')) ↦ G ((F a1) ↦ F a1') = a2))).
  pose (s1:=(⊓ (λ a2 , ∃ a1 a1',  G ((F a1) ↦ F a1') ↦ G(F (a1 ↦ a1')) = a2))).
  eapply (up_closed  (((λ- (fun y=> (λ- (fun z=> (λ- (fun x=> y @(z@x)))))))@s1)@s2)).
  - apply (@adj_app _ _ _ (IAStructure A3)),(@beta_red  _ _ _ (IAStructure A3)), (@adj_imp _ _ _ (IAStructure A3)),(@beta_red  _ _ _ (IAStructure A3)).
    auto_meet_intro. rename H into b.
    apply adj_imp,beta_red, (@adj_app _ _ _ (IAStructure A3)).
    apply ord_trans with ( G ((F a ↦ F b)) ↦ G(F (a ↦ b))).
    apply meet_elim;do 2 eexists;reflexivity.
    apply arrow_mon_l,(@adj_app _ _ (IALattice A3)). 
    apply meet_elim;do 2 eexists;reflexivity.
  - repeat (apply app_closed).
    + realizer (λ[A3]+ λ+ λ+ ([$2] ([$1] $0))).
    + eapply up_closed ;[|apply (HG _ iamarrow0)].
      auto_meet_intro.
      apply meet_elim;do 2 eexists;split;[|reflexivity].
      apply meet_elim;do 2 eexists;reflexivity.
    + eapply up_closed ;[|apply  iamarrow1].
      auto_meet_intro.
      apply meet_elim;do 2 eexists;reflexivity.
Qed.
Next Obligation.
  assert (HG:=iamunary G).
  assert (HF:=iamunary F).
  destruct F,G;simpl in *. rename IAMap0 into F,IAMap1 into G.
  destruct iamdense0 as (ff,(Hf1,Hf2),Hfint).
  destruct iamdense1 as (gg,(Hg1,Hg2),Hgint).
  exists (fun x => ff(gg(x))). split.
  - pose (s1:=⊓ (λ a2, ∃ a2' : IASet A3, (gg a2')  ↦ F (ff (gg a2')) = a2)).
    pose (s2:=⊓ (λ a2, ∃ a2' : IASet A3,  a2'  ↦ G (gg a2') = a2)).
    pose (sG:=(⊓ (λ a2 : IASet A3, ∃ a1 a1' : IASet A2, IAOrd A2 s1 (a1 ↦ a1') ∧ G a1 ↦ G a1' = a2))).
    eapply (up_closed  (((λ- (fun y=> (λ- (fun z=> (λ- (fun x=> y @(z@x)))))))@sG)@s2)).
    + auto_meet_intro.
      apply (@adj_app _ _ _ (IAStructure A3)),(@beta_red  _ _ _ (IAStructure A3)), (@adj_imp _ _ _ (IAStructure A3)),(@beta_red  _ _ _ (IAStructure A3)),adj_imp,beta_red, (@adj_app _ _ _ (IAStructure A3)).
      apply ord_trans with ((G (gg a))  ↦ G (F (ff (gg a)))).
      apply meet_elim;do 2 eexists;split;[|reflexivity].
      apply meet_elim;eexists;reflexivity.
      apply arrow_mon_l,(@adj_app _ _ _ (IAStructure A3)). 
      apply meet_elim;eexists;split;reflexivity.
    + repeat (apply app_closed).
      * realizer (λ[A3]+ λ+ λ+ ([$2] ([$1] $0))).
      * eapply up_closed ;[|apply (HG _ Hf1)].
        auto_meet_intro. rename H into b.
        apply meet_elim;do 2 eexists;split;[|reflexivity].
        transitivity s1;[|apply H0].
        auto_meet_intro.
        apply meet_elim;do 2 eexists;split;reflexivity.
      *  exact Hg1. 
  - pose (s1:=⊓ (λ a2, ∃ a2' : IASet A3, (F (ff(gg a2')))  ↦ (gg a2') = a2)).
    pose (s2:=⊓ (λ a2, ∃ a2' : IASet A3,  G (gg a2') ↦ a2'   = a2)).
    pose (sG:=(⊓ (λ a2 : IASet A3, ∃ a1 a1' : IASet A2, IAOrd A2 s1 (a1 ↦ a1') ∧ G a1 ↦ G a1' = a2))).
    eapply (up_closed  (((λ- (fun y=> (λ- (fun z=> (λ- (fun x=> y @(z@x)))))))@s2)@sG)).
    + auto_meet_intro.
      apply (@adj_app _ _ _ (IAStructure A3)),(@beta_red  _ _ _ (IAStructure A3)), (@adj_imp _ _ _ (IAStructure A3)),(@beta_red  _ _ _ (IAStructure A3)),adj_imp,beta_red, (@adj_app _ _ _ (IAStructure A3)).
      apply ord_trans with ((G (gg a))  ↦ a).
      apply meet_elim;eexists;reflexivity.
      apply arrow_mon_l,(@adj_app _ _ _ (IAStructure A3)).
      apply meet_elim;do 2 eexists;split;[|reflexivity].
      apply meet_elim;eexists;split;reflexivity.
    + repeat (apply app_closed).
      * realizer (λ[A3]+ λ+ λ+ ([$2] ([$1] $0))).
      * exact Hg2. 
      * eapply up_closed ;[|apply (HG _ Hf2)].
        auto_meet_intro. rename H into b.
        apply meet_elim;do 2 eexists;split;[|reflexivity].
        transitivity s1;[|apply H0].
        auto_meet_intro.
        apply meet_elim;do 2 eexists;split;reflexivity.
  - intro. destruct Hfint as [ finv finvf ffinv ]; try assumption. destruct Hgint as [ ginv ginvg gginv ]; try assumption. exists (fun a1 => ginv (finv a1)).
    + change ((fun p => p) = (fun p => ff ((fun p => gg (ginv p)) (finv p)))). rewrite <- ginvg. assumption.
    + change ((fun p => p) = (fun p => ginv ((fun p => finv (ff p)) (gg p)))). rewrite <- ffinv. assumption.
Qed.



(** * Definition VI.10 - Categories IA_int / IA_ext *)

Program Definition ImplicativeAlgebraCategory (int : Prop) : LocallyPreorderedBicategory
:= locally_preordered_bicategory ImplicativeAlgebraObject (ImplicativeAlgebraMorphism int) (@ImplicativeAlgebraRefines int) (@ia_id int) (@ia_comp int)  _ _ _ _ _  _  .
Next Obligation.
  eapply up_closed;[|apply sep_Id].
  auto_meet_intro.
  now apply adjunction,beta_red.
Qed.
Next Obligation.  
  unfold ImplicativeAlgebraRefines in *.
  pose (s1:=(⊓ (λ a2 : IASet o2, ∃ a1 : IASet o1, IAMap f a1 ↦ IAMap f' a1 = a2))).
  pose (s2:=(⊓ (λ a2 : IASet o2, ∃ a1 : IASet o1, IAMap f' a1 ↦ IAMap f'' a1 = a2))).
  apply up_closed with ((IAapp (IAapp (@IAabs o2 (fun y=> (IAabs (fun z=> (IAabs (fun x=> IAapp y (IAapp z x))))))) s2) s1));[|repeat (apply app_closed);trivial]. 
  - auto_meet_intro.
    apply (@adj_app _ _ _ (IAStructure o2)),(@beta_red  _ _ _ (IAStructure o2)), (@adj_imp _ _ _ (IAStructure o2)),(@beta_red  _ _ _ (IAStructure o2)),adj_imp,beta_red, (@adj_app _ _ _ (IAStructure o2)).
    transitivity (IAMap f' a ↦ IAMap f'' a).
    apply meet_elim;eexists;reflexivity.
    apply arrow_mon_l,adj_app.
    apply meet_elim;eexists;reflexivity.
  -  realizer (λ[o2]+ λ+ λ+ ([$2] ([$1] $0))).
Qed.
Next Obligation.
  unfold ImplicativeAlgebraRefines in *.
  assert (Hu2:=iamunary f23).
  destruct f12,f12',f23,f23'.
  rename IAMap0 into f0, IAMap1 into f1, IAMap2 into f2, IAMap3 into f3.
  simpl in *.
  pose (s:=⊓ (λ a2 : IASet o2, ∃ a1 : IASet o1, f0 a1 ↦ f1 a1 = a2)).
  pose (t:=⊓ (λ a2 : IASet o3, ∃ a1 : IASet o2, f2 a1 ↦ f3 a1 = a2)).
  pose (u2:=(⊓ (λ a2 : IASet o3, ∃ a1 a1' : IASet o2, IAOrd o2 s (a1 ↦ a1') ∧ f2 a1 ↦ f2 a1' = a2))).
  pose (r:=IAapp (IAapp (IAabs(fun t => IAabs (fun u2 => IAabs (fun x => IAapp t (IAapp u2 x))))) t ) u2).
  apply up_closed with r.
  auto_meet_intro.
  apply adj_app,beta_red,adj_imp ,beta_red,adj_imp,beta_red,adj_app.
  transitivity (f2 (f1 a) ↦ f3 (f1 a)).
  apply meet_elim;eexists;reflexivity.
  apply arrow_mon_l,adj_app.
  apply meet_elim;do 2 eexists;split;[| reflexivity].
  apply meet_elim;eexists;reflexivity.
  repeat (apply app_closed);trivial.
  realizer (λ[o3]+ λ+ λ+ ([$2] ([$1] $0))).
  now apply Hu2.
Qed.
Next Obligation.
  split;eapply up_closed;[|apply sep_Id| |apply sep_Id];auto_meet_intro;apply meet_elim;eexists;reflexivity.
Qed.
Next Obligation.
  split;eapply up_closed;[|apply sep_Id| |apply sep_Id];auto_meet_intro;apply meet_elim;eexists;reflexivity.
Qed. 
Next Obligation.
  split;eapply up_closed;[|apply sep_Id| |apply sep_Id];auto_meet_intro;apply meet_elim;eexists;reflexivity.
Qed.


