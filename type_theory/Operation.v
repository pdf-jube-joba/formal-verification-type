Require Import T.SyntaxDefinition.

Parameter AlphaEq : Term -> Term -> Prop.
Parameter AlphaEqb : Term -> Term -> bool.
Parameter Subst : Term -> id -> Term -> Term.

Inductive BetaStep : Term -> Term -> Prop :=
  | Step : forall x A M N ,
    BetaStep (TApp (TFun x A M) N) (Subst M x N)
  | CongTFor1 : forall x A A' B ,
    BetaStep A A' ->
    BetaStep (TFor x A B) (TFor x A' B)
  | CongTFor2 : forall x A B B' ,
    BetaStep B B' ->
    BetaStep (TFor x A B) (TFor x A B')
  | CongTFun1 : forall x A A' B ,
    BetaStep A A' ->
    BetaStep (TFun x A B) (TFor x A' B)
  | CongTFun2 : forall x A B B' ,
    BetaStep B B' ->
    BetaStep (TFun x A B) (TFor x A B')
  | CongTApp1 : forall M M' N ,
    BetaStep M M' ->
    BetaStep (TApp M N) (TApp M' N)
  | CongTApp2 : forall M N N' ,
    BetaStep N N' ->
    BetaStep (TApp M N) (TApp M N')
  | CongTRef1 : forall M M' N ,
    BetaStep M M' ->
    BetaStep (TRef M N) (TRef M' N)
  | CongTRef2 : forall M N N' ,
    BetaStep N N' ->
    BetaStep (TRef M N) (TRef M N')
  | CongPrf : forall P P' ,
    BetaStep P P' ->
    BetaStep (TPrf P) (TPrf P').

Inductive BetaEq : Term -> Term -> Prop :=
  | Beta : forall M N ,
    BetaStep M N -> BetaEq M N
  | Refl : forall M ,
    BetaEq M M
  | Sym : forall M N ,
    BetaEq M N -> BetaEq N M
  | Trans : forall L M N ,
    BetaEq L M -> BetaEq M N ->
    BetaEq L N.