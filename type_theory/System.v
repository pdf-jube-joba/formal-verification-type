Require Import T.SyntaxDefinition.
Require Import T.Operation.

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