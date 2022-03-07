Inductive Kind := KProp | KType.

Module Def.

Section Syntax.

Definition id := nat.

Inductive Term :=
  | TVar : id -> Term
  | TSort : Kind -> Term
  | TFor : Term -> Term -> Term
  | TFun : Term -> Term -> Term
  | TApp : Term -> Term -> Term
  | TRef : Term -> Term -> Term
  | TPrf : Term -> Term.

Inductive ContextSnippet :=
  | CType : Term -> ContextSnippet
  | CHold : Term -> ContextSnippet.

Definition Context := list (option ContextSnippet).

End Syntax.

Fixpoint Shift M d c :=
  match M with
  | TVar n => TVar (if Nat.leb c n then n + d else n)
  | TSort s => TSort s
  | TFor A B => TFor (Shift A d c) (Shift B d (S c))
  | TFun A t => TFun (Shift A d c) (Shift t d (S c))
  | TApp M N => TApp (Shift M d c) (Shift N d c)
  | TRef A P => TRef (Shift A d c) (Shift P d c)
  | TPrf P => TPrf (Shift P d c)
  end.

Fixpoint Subst M y N :=
  match M with
  | TVar x =>
    if (Nat.eqb x y) then
      Shift N y 0
    else if Nat.ltb y x then
      TVar (Nat.pred x)
    else
      TVar x
  | TSort s => TSort s
  | TFor A B => TFor (Subst A y N) (Subst B (S y) N)
  | TFun A t => TFun (Subst A y N) (Subst t (S y) t)
  | TApp M1 M2 => TApp (Subst M1 y N) (Subst M2 y N)
  | TRef A P => TRef (Subst A y N) (Subst P y N)
  | TPrf P => TPrf (Subst P y N)
  end.