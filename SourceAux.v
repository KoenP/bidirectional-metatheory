
Require Import Vec.
Require Import Source.
(* Require Import Target. *)

(* Constraint Scheme *)
Inductive Rule : Set :=
  | MkRule (bnds : nat) n (lhs : Vec Ct n) (rhs : Ct).

(* Source Typing Environments *)
Inductive HsTyEnv : Set :=
  | HsEnvNil
  | HsConsTy   (Γ : HsTyEnv)
  | HsConsTm   (Γ : HsTyEnv) (σ : Poly)
  | HsConsRule (Γ : HsTyEnv) (S : Rule)
  | HsConsCls (Γ : HsTyEnv) (cls : Cls)
  | HsConsIns (Γ : HsTyEnv) (ins : Ins).   (* FOR GENERATING THE EQUALITY AXIOM *)

(* TODO: WRONG. THINGS NEED TO BE SHIFTED. LEAVE AS IS FOR NOW. *)
Fixpoint concatHsTyEnv (Γ₁ : HsTyEnv) (Γ₂ : HsTyEnv) : HsTyEnv :=
  match Γ₂ with
    | HsEnvNil         => Γ₁
    | HsConsTy   Γ     => HsConsTy   (concatHsTyEnv Γ₁ Γ)
    | HsConsTm   Γ σ   => HsConsTm   (concatHsTyEnv Γ₁ Γ) σ
    | HsConsRule Γ r   => HsConsRule (concatHsTyEnv Γ₁ Γ) r
    | HsConsCls  Γ cls => HsConsCls  (concatHsTyEnv Γ₁ Γ) cls
    | HsConsIns  Γ ins => HsConsIns  (concatHsTyEnv Γ₁ Γ) ins
  end.

(* Domains. TODO: FIX THIS *)
Inductive Dom : Set :=
  | NilDom
  | TyDom (h : Dom)
  | TmDom (h : Dom)
  | RlDom (h : Dom)
  | CnDom (h : Dom). (* NOT ENOUGH. WE NEED THE 'n's TOO, FOR CLASSES AND INSTANCES *)


  Fixpoint bindTyVars (bnds : nat) (Γ : HsTyEnv) : HsTyEnv :=
    match bnds with
      | 0   => Γ
      | S n => bindTyVars n (HsConsTy Γ)
    end.

  (****************************************************************)
  (*                        SHIFTING SHIT                         *)
  (****************************************************************)

    Axiom shift_tyvar : Dom -> nat -> nat.

(*
  Fixpoint shift_tyvar (h : Dom) (a : nat) : nat :=
    match h,a with
    | NilDom ,_   => S a
    | TmDom h,_   => shift_tyvar h a
    | TyDom h,0   => 0
    | TyDom h,S b => S (shift_tyvar h b)
    | CnDom h,_   => shift_tyvar h a
    | AxDom h,_   => shift_tyvar h a
    end.
*)

  Fixpoint shift_ty_mono (h : Dom) (τ : Mono) : Mono :=
    match τ with
    | TyVar x     => TyVar (shift_tyvar h x)
    | TyArr τ₁ τ₂ => TyArr (shift_ty_mono h τ₁)
                           (shift_ty_mono h τ₂)
    end.

  Fixpoint shift_ty_ct (h : Dom) (π : Ct) : Ct :=
    match π with
    | MkCt cn τ => MkCt cn (shift_ty_mono h τ)
    end.

  Fixpoint shift_ty_qual (h : Dom) (ρ : Qual) : Qual :=
    match ρ with
    | QMono τ    => QMono (shift_ty_mono h τ)
    | QQual π ρ' => QQual (shift_ty_ct h π)
                          (shift_ty_qual h ρ')
    end.

  Fixpoint shift_ty_poly (h : Dom) (σ : Poly) : Poly :=
    match σ with
    | PQual ρ  => PQual (shift_ty_qual h ρ)
    | PPoly σ' => PPoly (shift_ty_poly (TyDom h) σ')
    end.

  Fixpoint extend_ty_dom (h : Dom) (n : nat) : Dom :=
    match n with
    | 0    => h
    | S n' => TyDom (extend_ty_dom h n')
    end.

  Definition shift_ty_cs (n : nat) (h : Dom) (πs : Vec Ct n) : Vec Ct n :=
    vmap Ct Ct n (shift_ty_ct h) πs.

(*
  Fixpoint shift_ty_axiom (h : Dom) (ax : Rule) : Rule :=
    match ax with
    | MkRule n m πs π => MkRule n m
                                 (shift_ty_cs n (extend_ty_dom h m) πs)
                                 (shift_ty_ct (extend_ty_dom h m) π)
    end.
*)

  (****************************************************************)
  (*                      SUBSTITUTION SHIT                       *)
  (****************************************************************)

(* Source-level Type Substitutions *)
Definition HsSub (n : nat) : Set := Vec Mono n.

(* TODO : Rename me! *)
Fixpoint asdf (n : nat) (θ : HsSub n) (x : nat) : Mono :=
  match θ with
  | VN         => TyVar x
  | VC t n' ts => match x with
                  | O    => t
                  | S x' => asdf n' ts x'
                  end
  end.

(* The h should actually be a domain but we don't have a need for it it seems *)
Fixpoint subst_ty_in_tyvar (n : nat) (θ : HsSub n) (h : nat) (x : nat) : Mono :=
  match h with
  | O    => asdf n θ x
  | S h' => match x with
            | O    => TyVar O
            | S x' => shift_ty_mono NilDom (subst_ty_in_tyvar n θ h' x')
            end
  end.

Fixpoint subst_ty_in_mono (n : nat) (θ : HsSub n) (h : nat) (τ : Mono) : Mono :=
  match τ with
  | TyVar x     => subst_ty_in_tyvar n θ h x
  | TyArr τ₁ τ₂ => TyArr (subst_ty_in_mono n θ h τ₁)
                         (subst_ty_in_mono n θ h τ₂)
  end.

Definition subst_ty_in_ct (n : nat) (θ : HsSub n) (h : nat) (π : Ct) : Ct :=
  match π with
  | MkCt cn τ => MkCt cn (subst_ty_in_mono n θ h τ)
  end.

Fixpoint subst_ty_in_qual (n : nat) (θ : HsSub n) (h : nat) (ρ : Qual): Qual :=
  match ρ with
  | QMono τ    => QMono (subst_ty_in_mono n θ h τ)
  | QQual π ρ' => QQual (subst_ty_in_ct n θ h π)
                        (subst_ty_in_qual n θ h ρ')
  end.

Fixpoint subst_ty_in_poly (n : nat) (θ : HsSub n) (h : nat) (σ : Poly) : Poly :=
  match σ with
  | PQual ρ  => PQual (subst_ty_in_qual n θ h ρ)
  | PPoly σ' => PPoly (subst_ty_in_poly n θ (S h) σ')
  end.

Definition uni_sub (τ : Mono) : HsSub (S 0) := VC Mono τ 0 (VN Mono).

(* Substitute 0 with τ₁ in τ₂ *)
Definition hsSubstTyInMono (τ₁ τ₂ : Mono) : Mono :=
  subst_ty_in_mono (S 0) (uni_sub τ₁) 0 τ₂.

(* Substitute 0 with τ in m monotypes *)
Fixpoint hsSubstTyInMonos m (τ : Mono) (τs : Vec Mono m) : Vec Mono m :=
  match τs with
    | VN          => VN Mono
    | VC τ' n τs' => VC Mono (hsSubstTyInMono τ τ') n (hsSubstTyInMonos n τ τs')
  end.

Axiom hsSubstTysInMono  : forall n, Vec Mono n -> Mono -> Mono.               (* the first (0,..,n-1) *)
Axiom hsSubstTysInMonos : forall n m, Vec Mono n -> Vec Mono m -> Vec Mono m. (* the first (0,..,n-1) *)
Axiom hsSubstTysInCt : forall n, Vec Mono n -> Ct -> Ct.               (* the first (0,..,n-1) *)
Axiom hsSubstTysInCs : forall n m, Vec Mono n -> Vec Ct m -> Vec Ct m. (* the first (0,..,n-1) *)
