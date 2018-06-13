
Require Import Vec.

(* SIMPLIFICATIONS
 * ~~~~~~~~~~~~~~~
 * No kinds ==> no type applications, everything fully saturated
 * Less coercion forms (we don't need them all for this)
 * No recursion
 *)

Inductive FcTy : Set :=
  | FcTyVar (a : nat)                     (* Type variable (a) *)
  | FcTyArr (υ₁ υ₂ : FcTy)                (* Arrow type (υ₁ → υ₂) *)
  | FcTyAll (υ : FcTy)                    (* Universal quantification (∀a. υ) *)
  | FcTyCon (tc : nat) (υ : FcTy)         (* Type constructor application (T υ) *)
  | FcTyFam (fn : nat) (υ : FcTy)         (* Type family application (F υ) *)
  | FcTyTup (n : nat) (υs : Vec FcTy n).  (* Tuple type ((υ₁,…,υₙ)) *)

Inductive Co : Set :=
  | CoRefl  (υ : FcTy)                             (* Reflexivity (<γ>) *)
  | CoSym   (γ : Co)                               (* Symmetry (sym γ) *)
  | CoTrans (γ₁ γ₂ : Co)                           (* Transitivity (γ₁ ; γ₂) *)
  | CoAxiom (g : nat) (n : nat) (υs : Vec FcTy n). (* Axiom application (g υs) *)

Inductive FcTm : Set :=
    (* Term variable (x) *)
  | FcTmVar (x : nat)
    (* Term abstraction (λ(x : υ). t) *)
  | FcTmAbs (υ : FcTy) (t : FcTm)
    (* Term application (t₁ t₂) *)
  | FcTmApp (t₁ t₂ : FcTm)
    (* Tuple term (t₁,…,tₙ) *)
  | FcTmTup (n : nat) (ts : Vec FcTm n)
    (* Type abstraction (Λa. t) *)
  | FcTyAbs (t : FcTm)
    (* Type application (t υ) *)
  | FcTyApp (t : FcTm) (υ : FcTy)
    (* Type cast (t ▹ γ) *)
  | FcCast  (t : FcTm) (γ : Co)
    (* Constructor (K υ t₀ tⁿ md) *)
  | FcCon   (dc : nat) (υ : FcTy) (ctx : FcTm) n (scs : Vec FcTm n) (md : FcTm)
    (* Case expression (case scr of { K ctx scs x → rhs }) *)
  | FcDCase (scr : FcTm) (* 1+n+1 *) (rhs : FcTm)
    (* Tuple case (case scr of { (x₁,…,xₙ) → rhs }) *)
  | FcTCase (scr : FcTm) (* ps : nat *) (rhs : FcTm).

(* Top-level Value Binding *)
Inductive FcVal : Set :=
  | MkFcVal (t : FcTm) (υ : FcTy).

(* Datatype Declaration *)
Inductive FcData : Set :=
  | MkFcData (ctx : FcTy) n (scs : Vec FcTy n) (md : FcTy).

(* Type Family Declaration *)
Inductive FcFam : Set :=
  | MkFcFam. (* TODO : USELESS *)

Inductive FcAx : Set :=
    (* axiom g asⁿ : F (υ) ∼ (υ₁,…,υₘ) *)
  | MkFcAx (bnds : nat) (fn : nat) (υ : FcTy) (m : nat) (υs : Vec FcTy m).

(* Target Program *)
Inductive FcPgm : Set :=
  | FcPgmEmpty
  | FcPgmVal  (fcval  : FcVal)  (fcpgm : FcPgm)
  | FcPgmData (fcdata : FcData) (fcpgm : FcPgm)
  | FcPgmFam  (fcfam  : FcFam)  (fcpgm : FcPgm)
  | FcPgmAx   (fcax   : FcAx)   (fcpgm : FcPgm).

(* Target Typing Environment *)
Inductive FcTyEnv : Set :=
  | FcEnvNil                                                                     (* Empty environment *)
  | FcConsTy (Δ : FcTyEnv)                                                       (* Type variable     *)
  | FcConsTm (Δ : FcTyEnv) (υ : FcTy)                                            (* Term variable     *)
  | FcConsFn (Δ : FcTyEnv)                                                       (* Family name       *)
  | FcConsDt (Δ : FcTyEnv) (dt : FcData)                                         (* Data type         *)
  | FcConsAx (Δ : FcTyEnv) (ax : FcAx).                                          (* Equality axiom    *)


(* ************************************ *)
(* SOME UTILITIES *)

Fixpoint appToTms (t : FcTm) n (ts : Vec FcTm n) : FcTm :=
  match ts with
    | VN          => t
    | VC t' m ts' => appToTms (FcTmApp t t') m ts'
  end.

Fixpoint appToTys (t : FcTm) n (υs : Vec FcTy n) : FcTm :=
  match υs with
    | VN        => t
    | VC υ m υs => appToTys (FcTyApp t υ) m υs
  end.