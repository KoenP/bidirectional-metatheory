
Require Import Coq.Init.Prelude.
Require Import Vec.
Require Import Target.
Require Import TargetAux.
Require Import Source.
Require Import SourceAux.
Require Import SourceTyping.
Require Import TargetTyping.

(****************************************************************)
(*                  PRESERVATION OF LOOKUPS                     *)
(****************************************************************)

Lemma lookup_tyvar_preservation : forall Γ Δ a b, HsTyVarIn a Γ b -> ElabTyEnv Γ Δ -> FcTyVarIn b Δ.
Proof.
  intros.
Admitted.

Lemma lookup_tycon_preservation : forall Γ Δ cn tc, HsCnIn cn Γ tc -> ElabTyEnv Γ Δ -> FcConIn tc Δ.
Proof.
  intros.
Admitted.

(****************************************************************)
(*      PRESERVATION OF TYPE AND CONSTRAINT ELABORATION         *)
(****************************************************************)

Theorem wf_mono_preservation : forall Γ τ Δ υ, HsTcMono Γ τ υ -> ElabTyEnv Γ Δ -> FcTcTy Δ υ.
Proof.
  intros.
  induction H.
  + constructor.
    apply (lookup_tyvar_preservation Γ Δ a fcA ainΓ H0).
  + constructor.
    apply IHHsTcMono1.
    apply IHHsTcMono2.
Qed.

Theorem wf_ct_preservation : forall Γ π Δ υ, HsTcCt Γ π υ -> ElabTyEnv Γ Δ -> FcTcTy Δ υ.
Proof.
  intros.
  induction H.
  + constructor.    
    apply (lookup_tycon_preservation Γ Δ cn tc cninΓ H0).
    apply (wf_mono_preservation Γ τ Δ υ wfτ H0).
Qed.

Theorem wf_qual_preservation : forall Γ ρ Δ υ, HsTcQual Γ ρ υ -> ElabTyEnv Γ Δ -> FcTcTy Δ υ.
Proof.
  intros.
  induction H.
  + apply (wf_mono_preservation Γ τ Δ υ wfτ H0).
  + constructor.
    apply (wf_ct_preservation Γ π Δ υ₁ wfπ H0).
    apply IHHsTcQual.
Qed.

Theorem wf_poly_preservation : forall Γ σ Δ υ, HsTcPoly Γ σ υ -> ElabTyEnv Γ Δ -> FcTcTy Δ υ.
Proof.
  intros.
  induction H.
  + apply (wf_qual_preservation Γ ρ Δ υ wfρ H0).
  + constructor.
Admitted.


Lemma fc_tc_co_wf : forall Δ γ υ₁ υ₂, FcTcCo Δ γ υ₁ υ₂ -> (FcTcTy Δ υ₁ /\ FcTcTy Δ υ₂).
Proof.
  intros.
  induction H.
  + auto.
  + destruct IHFcTcCo.
    auto.
  + destruct IHFcTcCo1.
    destruct IHFcTcCo2.
    constructor.
    apply H1.
    apply H4.
  + constructor.    
    constructor.
    apply fninΔ.
Admitted.


(*
(* TODO: ACTUALLY PROVE ONCE YOU HAVE DEFINED THE LOOKUPS *)
Theorem preservation_tyvar Γ Δ a fca
      (elabΓ : HsElabEnv Γ Δ) (lookup : HsTyVarIn a Γ fca) : FcTyVarIn fca Δ.
Admitted.
 *)

(* JUST FOR GUIDANCE
Axiom HsTmVarIn : nat -> Poly -> HsTyEnv -> FcTm -> Prop. (* Elaborate the lookup also *)
Axiom HsTyVarIn : nat -> HsTyEnv -> nat -> Prop.          (* Elaborate the lookup also *)
Axiom HsTmMdIn  : nat -> Poly -> HsTyEnv -> FcTm -> Prop. (* Elaborate the lookup also *)
Axiom HsCnIn : nat -> HsTyEnv -> nat -> Prop.             (* Elaborate the class name also *)
 *)

(*
  Inductive ElabTyEnv : HsTyEnv -> FcTyEnv -> Prop :=
    | ElabEnvNil
        : ElabTyEnv HsEnvNil FcEnvNil
    | ElabConsTy Γ Δ (eΓ : ElabTyEnv Γ Δ)
        : ElabTyEnv (HsConsTy Γ) (FcConsTy Δ)
    | ElabConsTm Γ Δ σ υ (eΓ : ElabTyEnv Γ Δ) (eσ : HsTcPoly Γ σ υ)
        : ElabTyEnv (HsConsTm Γ σ) (FcConsTm Δ υ)
    | ElabConsCt Γ Δ π υ (eΓ : ElabTyEnv Γ Δ) (eπ : HsTcCt Γ π υ)
        : ElabTyEnv (HsConsCt Γ π) (FcConsTm Δ υ)                     (* it's a term variable *)
    | ElabConsCls Γ Δ n scs τ (eΓ : ElabTyEnv Γ Δ)
        : ElabTyEnv (HsConsCls Γ (MkCls n scs τ)) Δ   (* TODO: ADD THE COMPONENTS *)
    | ElabConsIns Γ Δ n ctx τ e (eΓ : ElabTyEnv Γ Δ)
        : ElabTyEnv (HsConsIns Γ (MkIns n ctx τ e)) Δ (* TODO: ADD THE COMPONENTS *)
  .
*)

(*
Inductive HsTmVarIn : nat -> Poly -> HsTyEnv -> nat -> Prop :=

Inductive HsTyVarIn : nat -> HsTyEnv -> nat -> Prop :=
*)




(*
(* TODO: PRESERVATION OF TYPING FOR ENTAILMENT *)
Theorem preservation_entailment Γ Δ t π υ
  (elabΓ  : ElabTyEnv Γ Δ) (elabπ  : HsTcCt Γ π υ) (entail : HsEntail Γ t π) : FcTcTm Δ t υ.
Admitted.
*)

(* NOTHING HERE YET!!! *)


(*



(****************************************************************)
Section HS.
  (*****************)
  (* SOURCE SYNTAX *)
  (*****************)



  (******************************)
  (* SOURCE ENVIRONMENT LOOKUPS *)
  (******************************)


  (* MUHAHA *)
  Inductive HsTyEnv : Set :=
    | HsEnvNil
    | HsConsTy  (Γ : HsTyEnv)
    | HsConsTm  (Γ : HsTyEnv) (σ : Poly)
    | HsConsCn  (Γ : HsTyEnv) (cen : ClsEntry)
    | HsConsAx  (Γ : HsTyEnv) (ax : Rule).
  (* MUHAHA *)
  Inductive FcTyEnv : Set :=
    | fcEnvNil                                                                     (* Empty environment *)
    | fcConsTy (Δ : FcTyEnv)                                                       (* Type variable     *)
    | fcConsTm (Δ : FcTyEnv) (υ : FcTy)                                            (* Term variable     *)
    | fcConsFn (Δ : FcTyEnv)                                                       (* Family name       *)
    | fcConsTc (Δ : FcTyEnv) (ctx : FcTy) (n : nat) (scs : Vec FcTy n) (md : FcTy) (* Type declaration  *)
    | fcConsAx (Δ : FcTyEnv) (ax : FcAx).                                          (* Equality axiom    *)
  (* MUHAHA *)
  Inductive FcAx : Set :=
    | MkFcAx (bnds : nat) (cn : nat) (υ : FcTy) (m : nat) (υs : Vec FcTy m).
    (* axiom g asⁿ : F (υ) ∼ (υ₁,…,υₘ) *)
  Inductive ClsEntry : Set :=
    | MkClsEntry n (scs : Vec Ct n) (md : Mono).
  (* MUHAHA *)
  Inductive Rule : Set :=
    | MkRule n (bnds : nat) (πs : Vec Ct n) (π : Ct).


  Inductive TyIn : nat -> tyEnv -> Prop :=
    | TyInNil    : forall Γ,
                     TyIn 0 (cons_ty Γ)
    | TyInSuc    : forall Γ n,
                     TyIn n Γ -> TyIn (S n) (cons_ty Γ)
    | TyInSkipTm : forall Γ n σ,
                     TyIn n Γ -> TyIn n (cons_tm Γ σ)
    | TyInSkipCn : forall Γ n t,
                     TyIn n Γ -> TyIn n (cons_cn Γ t)
    | TyInSkipAx : forall Γ n p,
                     TyIn n Γ -> TyIn n (cons_ax Γ p).


Fixpoint subst_ty_in_mono

Fixpoint subst_ty_in_qual


G |- ty ~~> fcty
G ~~> D
-----------------
D |- fcty


G |- t : s ~~> fct
G |- s ~~> fcs
G ~~> D
------------------
D |- fct : fcs



G |- t : forall a. s ~~~> FCtm    G |- tt ~~~> FCty
===================================================
G | t : [a |-> tt]s ~~~> FCtm FCty


G, a |- t : sigma
===================================
G |- t : forall a. sigma



G, (d : CT) |- t : rho  ~~~> FCT
==============================================
G |- t : (CT => rho)  ~~> \(d : elab(CT)). FCT


G |- t : (CT => rho)  ~~> fct1
G |= td : CT
==============================
G |- t : rho ~~> fct1 td

(TC t)



 G |- ts wf
 theta == [as |-> ts]
 forall as. (Q1 Q2 .. Qn) => TC t  in G
 G |= theta(Qi) ...
========================================
G |= (TC (theta(t)))


 G |- ts ~~> fcs
 theta   == [as |-> ts]
 fctheta == [as |-> fcs]
 (dG : forall as. (Q1 Q2 .. Qn) => TC t) in G
 G |= tdi : theta(Qi)  forall i
========================================
G |= (dG fctheta(as) tds) : (TC (theta(t)))


G |= td : ct
G |- ct ~~> fcty
G ~~> D
-----------------
D |- td : fcty




Inductive clsDecl : Set := CD (tce : tcEntry).

Inductive insDecl : Set := .

Inductive letBind : Set := .


Inductive pgm : Set :=
  | PgmNil
  | PgmCls (clsd : clsDecl) (p : pgm)
  | PgmIns (clsi : insDecl) (p : pgm)
  | PgmLet (letb : letBind) (p : pgm).

Inductive TyPgm
Inductive TyClsDecl : tyEnv -> clsDecl -> tyEnv -> Set :=
  Cls :




End ShiftTyHs.

(****************************************************************)
Section ShiftTcHs.

  Fixpoint shift_tc_tc (h : Dom) (n : nat) : nat :=
    match h,n with
    | NilDom ,_   => S n
    | TmDom h,_   => shift_tc_tc h n
    | TyDom h,_   => shift_tc_tc h n
    | TcDom h,0   => 0
    | TcDom h,S m => S (shift_tc_tc h m)
    end.

  (* No need to shift monotypes, they have no tc name in them*)

  Definition shift_tc_ct (h : Dom) (p : ct) : ct :=
    match p with
    | Ct tc t => Ct (shift_tc_tc h tc) t
    end.

  Fixpoint shift_tc_qual (h : Dom) (q : qual) : qual :=
    match q with
    | QMono t    => QMono t
    | QQual ct p => QQual (shift_tc_ct h ct) (shift_tc_qual h p)
    end.

  Fixpoint shift_tc_poly (h : Dom) (s : poly) : poly :=
    match s with
    | PQual p  => PQual (shift_tc_qual h p)
    | PPoly s' => PPoly (shift_tc_poly (TyDom h) s')
    end.

  Definition shift_tc_cs (n : nat) (h : Dom) (cs : t ct n) : t ct n :=
    map (shift_tc_ct h) cs.

  Fixpoint shift_tc_axiom (h : Dom) (ax : axiom) : axiom :=
    match ax with
    | Ax n m cs ct => Ax n m
                         (shift_tc_cs n (extend_ty_dom m h) cs)
                         (shift_ty_ct (extend_ty_dom m h) ct)
    end.

End ShiftTcHs.








  Definition shift_ty_cs (n : nat) (h : Dom) (cs : t ct n) : t ct n :=
    map (shift_ty_ct h) cs.








Inductive TmIn : nat -> poly -> tyEnv -> Set :=
  | TmInNil    : forall G s,
                   TmIn 0 s (cons_tm G s)
  | TmInSuc    : forall G n s s',
                   TmIn n s G -> TmIn (S n) s (cons_tm G s')
  | TmInSkipTy :
                   TmIn

  | TmInSkipTc

  | TmInSkipD
.


*)




