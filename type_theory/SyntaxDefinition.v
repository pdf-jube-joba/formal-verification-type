Inductive Kind := KProp | KType.

Definition id := nat.

Inductive Term :=
  | TVar : id -> Term
  | TSort : Kind -> Term
  | TFor : id -> Term -> Term -> Term
  | TFun : id -> Term -> Term -> Term
  | TApp : Term -> Term -> Term
  | TRef : Term -> Term -> Term
  | TPrf : Term -> Term.

Inductive ContextSnippet :=
  | CType : id -> Term -> ContextSnippet
  | CHold : Term -> ContextSnippet.

Definition Context := list ContextSnippet.