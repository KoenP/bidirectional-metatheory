
Require Import Vec.

(* SIMPLIFICATIONS
 * ~~~~~~~~~~~~~~~
 * Single class parameter
 * Single method for each class
 * Methods have a monotype
 * No recursion (yet)
 * No let-bindings (yet)
 *)

(* Monotype *)
Inductive Mono : Set :=
  | TyVar (a : nat)
  | TyArr (τ₁ τ₂ : Mono).

(* Class Constraint *)
Inductive Ct : Set :=
  | MkCt (cn : nat) (τ : Mono).

(* Qualified Type *)
Inductive Qual : Set :=
  | QMono (τ : Mono)
  | QQual (π : Ct) (ρ : Qual).

(* Polytype *)
Inductive Poly : Set :=
  | PQual (π : Qual)
  | PPoly (σ : Poly).

(* Term *)
(* TODO: ADD LET BINDINGS *)
Inductive HsTm : Set :=
  | TmVar (x : nat)
  | TmAbs (e : HsTm)
  | TmApp (e₁ e₂ : HsTm).

(* Class Declaration *)
Inductive Cls : Set :=
  | MkCls n (scs : Vec Ct n) (md : Mono).

(* Instance Declaration *)
Inductive Ins : Set :=
  | MkIns (bnds : nat) n (ctx : Vec Ct n) (cn : nat) (τ : Mono) (e : HsTm).

(* Top-level Value Binding *)
Inductive Val : Set :=
  | MkVal (e : HsTm).

(* Top-level Value Binding with a Signature *)
Inductive Sig : Set :=
  | MkSig (e : HsTm) (σ : Poly).

(* Source Program *)
Inductive Pgm : Set :=
  | PgmEmpty
  | PgmCls (cls : Cls) (pgm : Pgm)
  | PgmIns (ins : Ins) (pgm : Pgm)
  | PgmVal (val : Val) (pgm : Pgm)
  | PgmSig (sig : Sig) (pgm : Pgm).
