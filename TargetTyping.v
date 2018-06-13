
Require Import Vec.
Require Import Target.
Require Import TargetAux.


(*****************************************************************)
(*                       TARGET LOOKUPS                          *)
(*****************************************************************)

(* TODO: WRITE THESE *)
Axiom FcAxIn : nat -> FcAx -> FcTyEnv -> Prop.
Axiom FcTmVarIn : nat -> FcTy -> FcTyEnv -> Prop.
Axiom FcTyVarIn : nat -> FcTyEnv -> Prop.
Axiom FcTyFamIn : nat -> FcTyEnv -> Prop.
Axiom FcDataIn : nat -> FcTyEnv -> FcData -> Prop.
Axiom FcConIn : nat -> FcTyEnv -> Prop.
(* TODO: ALSO ADD MORE *)

(*
(* TODO: THIS IS PLAIN WRONG. WE NEED TO SHIFT STUFF *)
Inductive FcAxIn : nat -> FcAx -> FcTyEnv -> Prop :=
  | FcAxInAxHere Δ ax
      : FcAxIn 0 ax (fcConsAx Δ ax)
  | FcAxInAxThere n ax Δ ax' (there : FcAxIn n ax Δ)
      : FcAxIn (S n) ax (fcConsAx Δ ax')
  | FcAxInTyThere n ax Δ (there : FcAxIn n ax Δ)       (* IT IS THE AX THAT SHOULD BE SHIFTED *)
      : FcAxIn n ax (fcConsTy Δ)
  | FcAxInTmThere n ax Δ υ (there : FcAxIn n ax Δ)
      : FcAxIn n ax (fcConsTm Δ υ)
  | FcAxInCnThere n ax Δ ctx m scs md (there : FcAxIn n ax Δ)   (* IT IS THE AX THAT SHOULD BE SHIFTED *)
      : FcAxIn n ax (fcConsTc Δ ctx m scs md).
*)

(*****************************************************************)
(*                      TYPE WELL-FORMEDNESS                     *)
(*****************************************************************)

(* System FC Type Well-formedness *)
Inductive FcTcTy (Δ : FcTyEnv) : FcTy -> Prop :=
  | FcTcTyVar a (ainΔ : FcTyVarIn a Δ)
    : FcTcTy Δ (FcTyVar a)
  | FcTcTyArr υ₁ υ₂ (wfυ₁ : FcTcTy Δ υ₁) (wfυ₂ : FcTcTy Δ υ₂)
    : FcTcTy Δ (FcTyArr υ₁ υ₂)
  | FcTcTyAll υ (wfυ : FcTcTy (FcConsTy Δ) υ)
    : FcTcTy Δ (FcTyAll υ)
  | FcTcTyCon tc υ (tcinΔ : FcConIn tc Δ) (wfυ : FcTcTy Δ υ)
    : FcTcTy Δ (FcTyCon tc υ)
  | FcTcTyFam fn υ (fninΔ : FcTyFamIn fn Δ) (wfυ : FcTcTy Δ υ)
    : FcTcTy Δ (FcTyFam fn υ)
  | FcTcTyTup n υs (wfυs : FcTcTys Δ n υs)
    : FcTcTy Δ (FcTyTup n υs)
with FcTcTys (Δ : FcTyEnv) : forall n, Vec FcTy n -> Prop :=
  | FcTcTysNil  : FcTcTys Δ 0 (VN FcTy)
  | FcTcTysCons υ n υs (wfυ : FcTcTy Δ υ) (wfυs : FcTcTys Δ n υs) : FcTcTys Δ (S n) (VC FcTy υ n υs).

(*****************************************************************)
(*                        COERCION TYPING                        *)
(*****************************************************************)

(* System FC Coercion Typing *)
Inductive FcTcCo (Δ : FcTyEnv) : Co -> FcTy -> FcTy -> Prop :=
  | FcTcCoRefl υ (wfυ : FcTcTy Δ υ)
      : FcTcCo Δ (CoRefl υ) υ υ
  | FcTcCoSym γ υ₁ υ₂ (tcγ : FcTcCo Δ γ υ₁ υ₂)
      : FcTcCo Δ (CoSym γ) υ₂ υ₁
  | FcTcCoTrans γ₁ γ₂ υ₁ υ₂ υ₃ (tcγ₁ : FcTcCo Δ γ₁ υ₁ υ₂) (tcγ₂ : FcTcCo Δ γ₂ υ₂ υ₃)
      : FcTcCo Δ (CoTrans γ₁ γ₂) υ₁ υ₃
  | FcTcCoAxiom n g fn υs υ m rυs (fninΔ : FcTyFamIn fn Δ)
                (ginΔ : FcAxIn g (MkFcAx n fn υ m rυs) Δ) (wfυs : FcTcTys Δ n υs)
      : FcTcCo Δ (CoAxiom g n υs)
             (FcTyFam fn (fcSubstTysInTy n υs υ)) (FcTyTup m (fcSubstTysInTys n m υs rυs)).

(*****************************************************************)
(*                          TERM TYPING                          *)
(*****************************************************************)

(* System FC Term Typing *)
Inductive FcTcTm (Δ : FcTyEnv) : FcTm -> FcTy -> Prop :=
  | FcTcTmVar x υ (xinΔ : FcTmVarIn x υ Δ)
      : FcTcTm Δ (FcTmVar x) υ
  | FcTcTmAbs υ₁ t υ₂ (wfυ : FcTcTy Δ υ₁) (tct : FcTcTm (FcConsTm Δ υ₁) t υ₂)
      : FcTcTm Δ (FcTmAbs υ₁ t) (FcTyArr υ₁ υ₂) (* TODO: No shifting I guess, it's a tmvar? *)
  | FcTcTmApp t₁ t₂ υa υb (tct₁ : FcTcTm Δ t₁ (FcTyArr υa υb)) (tct₂ : FcTcTm Δ t₂ υa)
      : FcTcTm Δ (FcTmApp t₁ t₂) υb
  | FcTcTmTup n ts υs (tcts : FcTcTms Δ n ts υs)
      : FcTcTm Δ (FcTmTup n ts) (FcTyTup n υs)
  | FcTcTyAbs t υ (tct : FcTcTm (FcConsTy Δ) t υ)
      : FcTcTm Δ (FcTyAbs t) (FcTyAll υ)
  | FcTcTyApp t υ υ₁
      (tct : FcTcTm Δ t (FcTyAll υ₁))
      (wfυ : FcTcTy Δ υ)
      :  FcTcTm Δ (FcTyApp t υ) (fcSubstTyInTy υ υ₁)
  | FcTcCast t γ υ₁ υ₂
      (tct : FcTcTm Δ t υ₁)
      (tcγ : FcTcCo Δ γ υ₁ υ₂)
    : FcTcTm Δ (FcCast t γ) υ₂
  | FcTcTmCon dc υ ctx n scs md υctx υscs υmd
      (dcinΔ : FcDataIn dc Δ (MkFcData υctx n υscs υmd))
      (wfυ   : FcTcTy Δ υ)
      (tcctx : FcTcTm Δ ctx (fcSubstTyInTy υ υctx))
      (tcscs : FcTcTms Δ n scs (fcSubstTyInTys n υ υscs))
      (tcmd : FcTcTm Δ md (fcSubstTyInTy υ υmd))
    : FcTcTm Δ (FcCon dc υ ctx n scs md) (FcTyCon dc υ)
  | FcTcDCase scr rhs tc υ n υctx υscs υmd υrhs
      (tcscr : FcTcTm Δ scr (FcTyCon tc υ))
      (dcinΔ : FcDataIn tc Δ (MkFcData υctx n υscs υmd))
      (tcrhs : FcTcTm (FcConsTm (fcBindTmVars n (fcSubstTyInTys n υ υscs)
                                              (FcConsTm Δ (fcSubstTyInTy υ υctx))
                                ) (fcSubstTyInTy υ υmd)) rhs υrhs)
    : FcTcTm Δ (FcDCase scr rhs) υrhs
  | FcTcTCase scr n υs rhs υrhs
      (tcscr : FcTcTm Δ scr (FcTyTup n υs))
      (tcrhs : FcTcTm (fcBindTmVars n υs Δ) rhs υrhs)
      : FcTcTm Δ (FcTCase scr rhs) υrhs

with FcTcTms (Δ : FcTyEnv) : forall n, Vec FcTm n -> Vec FcTy n -> Prop :=
  | FcTcTmsNil
    : FcTcTms Δ 0 (VN FcTm) (VN FcTy)
  | FcTcTmsCons n t ts υ υs (tct : FcTcTm Δ t υ) (tcts : FcTcTms Δ n ts υs)
    : FcTcTms Δ (S n) (VC FcTm t n ts) (VC FcTy υ n υs).

(*****************************************************************)
(*                       DECLARATION TYPING                      *)
(*****************************************************************)

(* System FC Top-level Value Binding || TODO: NON-RECURSIVE *)
(* Just return the type, to extend the environment with *)
Inductive FcTcVal (Δ : FcTyEnv) : FcVal -> FcTy -> Prop :=
  | FcTcMkVal t υ
      (tct : FcTcTm Δ t υ)
    : FcTcVal Δ (MkFcVal t υ) υ.

(* System FC Type Family Declaration || TODO: REMOVE EVENTUALLY *)
Inductive FcTcFam (Δ : FcTyEnv) : FcFam -> Prop :=
  | FcTcMkFam
    : FcTcFam Δ MkFcFam.

(* System FC Datatype Declaration *)
Inductive FcTcData (Δ : FcTyEnv) : FcData -> Prop :=
  | FcTcMkData ctx n scs md
      (tcctx : FcTcTy  (FcConsTy Δ) ctx)
      (tcscs : FcTcTys (FcConsTy Δ) n scs)
      (tcmd  : FcTcTy  (FcConsTy Δ) md)
    : FcTcData Δ (MkFcData ctx n scs md).

(* System FC Equality Axiom *)
Inductive FcTcAx (Δ : FcTyEnv) : FcAx -> Prop :=
  | FcTcMkAx bs fn υ m υs
      (fninΔ : FcTyFamIn fn Δ)
      (wfυ  : FcTcTy  (fcBindTyVars bs Δ) υ)
      (wfυs : FcTcTys (fcBindTyVars bs Δ) m υs)
    : FcTcAx Δ (MkFcAx bs fn υ m υs).

(*****************************************************************)
(*                        PROGRAM TYPING                         *)
(*****************************************************************)

Inductive FcTcPgm (Δ : FcTyEnv) : FcPgm -> Prop :=
  | FcTcPgmEmpty
    : FcTcPgm Δ FcPgmEmpty
  | FcTcPgmVal fcval fcpgm υ
      (tcfcval : FcTcVal Δ fcval υ)
      (fcfcpgm : FcTcPgm (FcConsTm Δ υ) fcpgm)
    : FcTcPgm Δ (FcPgmVal fcval fcpgm)
  | FcTcPgmData fcdata fcpgm
      (tcfcdata : FcTcData Δ fcdata)
      (tcfcpgm  : FcTcPgm (FcConsDt Δ fcdata) fcpgm)
    : FcTcPgm Δ (FcPgmData fcdata fcpgm)
  | FcTcPgmFam fcfam fcpgm
      (tcfcfam : FcTcFam Δ fcfam)
      (fcfcpgm : FcTcPgm (FcConsFn Δ) fcpgm)
    : FcTcPgm Δ (FcPgmFam fcfam fcpgm)
  | FcTcPgmAx fcax fcpgm
      (tcfcax  : FcTcAx Δ fcax)
      (fcfcpgm : FcTcPgm (FcConsAx Δ fcax) fcpgm)
    : FcTcPgm Δ (FcPgmAx fcax fcpgm).
