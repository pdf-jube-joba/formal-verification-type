Require Import Definitions.
Import Def.

Definition FalseProp : Term := TFor 0 (TSort KProp) (TVar 0).

(*goal*)
Theorem consistency : forall (t:Term) , TypeJudge nil t FalseProp -> False.
Proof.
Admitted.