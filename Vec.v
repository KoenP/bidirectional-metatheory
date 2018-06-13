
Inductive Vec (A : Type) : nat -> Type :=
  | VN : Vec A 0
  | VC : A -> forall (n : nat), Vec A n -> Vec A (S n).

Fixpoint vmap (A B : Type) (n : nat) (f : A -> B) (v : Vec A n) : Vec B n :=
  match v with
  | VN        => VN B
  | VC x n xs => VC B (f x) n (vmap A B n f xs)
  end.
