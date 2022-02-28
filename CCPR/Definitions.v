Inductive Kind := KProp | KType.

Module Def.

Section Syntax.

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

End Syntax.

Section Operation.

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

End Operation.

Section System.

Inductive ContextJudge : Context -> Type :=
  | Empty : ContextJudge nil
  | StartType : forall G A x s ,
    TypeJudge G A (TSort s) ->
    ContextJudge (cons (CType x A) G)
  | StartProp : forall G P ,
    TypeJudge G P (TSort KProp) ->
    ContextJudge (cons (CHold P) G)
with TypeJudge : Context -> Term -> Term -> Type :=
  | AxiomKind : TypeJudge nil (TSort KProp) (TSort KType)
  | Weakning : forall G t T h ,
    TypeJudge G t T ->
    ContextJudge (cons h G) ->
    TypeJudge (cons h G) t T
  | Variab : forall x A G , 
    ContextJudge (cons (CType x A) G) ->
    TypeJudge (cons (CType x A) G) (TVar x) A
  | ForForm : forall G x A B s1 s2 ,
    TypeJudge G A (TSort s1) ->
    TypeJudge (cons (CType x A) G) B (TSort s2) ->
    TypeJudge G (TFor x A B) (TSort s2)
  | ForIntro : forall G x A t B s ,
    TypeJudge G (TFor x A B) (TSort s) ->
    TypeJudge (cons (CType x A) G) t B ->
    TypeJudge G (TFun x A t) (TFor x A B)
  | ForElim : forall G M N x A B , 
    TypeJudge G M (TFor x A B) ->
    TypeJudge G N A ->
    TypeJudge G (TApp M N) (Subst B x M)
  | RefForm : forall G x A P ,
    TypeJudge G A (TSort KType) ->
    TypeJudge G P (TFor x A (TSort KProp)) ->
    TypeJudge G (TRef A P) (TSort KType)
  | RefIntro : forall G t A P ,
    TypeJudge G t A ->
    ProofJudge G (TApp P t) ->
    TypeJudge G t (TRef A P)
  | RefElim : forall G t A P ,
    TypeJudge G t (TRef A P) ->
    TypeJudge G t A
  | Conversion : forall G t A B s ,
    BetaEq A B ->
    TypeJudge G t A ->
    TypeJudge G B (TSort s) ->
    TypeJudge G t B
  | ProofAbstraction : forall G P ,
    ProofJudge G P ->
    TypeJudge G (TPrf P) P
with ProofJudge : Context -> Term -> Type :=
  | Assumption : forall G P ,
    ContextJudge (cons (CHold P) G) ->
    ProofJudge (cons (CHold P) G) P
  | ProofExistence : forall G P t ,
    TypeJudge G P (TSort KProp) ->
    TypeJudge G t P ->
    ProofJudge G P
  | RefInversion : forall G t A P ,
    TypeJudge G t (TRef A P) ->
    ProofJudge G (TApp P t).

End System.

End Def.