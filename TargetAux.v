
Require Import Vec.
Require Import Target.

(* Target Typing Environment *)
Inductive FcTyEnv : Set :=
  | FcEnvNil                                                                     (* Empty environment *)
  | FcConsTy (Δ : FcTyEnv)                                                       (* Type variable     *)
  | FcConsTm (Δ : FcTyEnv) (υ : FcTy)                                            (* Term variable     *)
  | FcConsFn (Δ : FcTyEnv)                                                       (* Family name       *)
  | FcConsDt (Δ : FcTyEnv) (dt : FcData)                                         (* Data type         *)
  | FcConsAx (Δ : FcTyEnv) (ax : FcAx).                                          (* Equality axiom    *)

(* TODO: WRONG. THINGS NEED TO BE SHIFTED. LEAVE AS IS FOR NOW. *)
Fixpoint concatFcTyEnv (Δ₁ : FcTyEnv) (Δ₂ : FcTyEnv) : FcTyEnv :=
  match Δ₂ with
    | FcEnvNil      => Δ₁
    | FcConsTy Δ    => FcConsTy (concatFcTyEnv Δ₁ Δ)
    | FcConsTm Δ υ  => FcConsTm (concatFcTyEnv Δ₁ Δ) υ
    | FcConsFn Δ    => FcConsFn (concatFcTyEnv Δ₁ Δ)
    | FcConsDt Δ dt => FcConsDt (concatFcTyEnv Δ₁ Δ) dt
    | FcConsAx Δ ax => FcConsAx (concatFcTyEnv Δ₁ Δ) ax
  end.

(* TODO: WRITE THESE *)
Axiom fcSubstTyInTy   : FcTy -> FcTy -> FcTy.                               (* the first (0)        *)
Axiom fcSubstTyInTys  : forall m,  FcTy -> Vec FcTy m -> Vec FcTy m.        (* the first (0)        *)
Axiom fcSubstTysInTy  : forall n, Vec FcTy n -> FcTy -> FcTy.               (* the first (0,..,n-1) *)
Axiom fcSubstTysInTys : forall n m, Vec FcTy n -> Vec FcTy m -> Vec FcTy m. (* the first (0,..,n-1) *)

Fixpoint fcBindTmVars n (υs : Vec FcTy n) (Δ : FcTyEnv) : FcTyEnv :=
    match υs with
      | VN      => Δ
      | VC υ n υs => fcBindTmVars n υs (FcConsTm Δ υ)
    end.

Fixpoint fcBindTyVars (bs : nat) (Δ : FcTyEnv) : FcTyEnv :=
    match bs with
      | 0   => Δ
      | S n => fcBindTyVars n (FcConsTy Δ)
    end.
