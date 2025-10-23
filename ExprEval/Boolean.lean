import ExprEval.Expr
import ExprEval.ArStepLemmas

def eval_bool (val: V -> Int) (e: BoolExpr V): Bool :=
    match e with
    | BoolExpr.Const b => b
    | BoolExpr.Less l r =>  (eval V val l) < (eval V val r)
    | BoolExpr.Eq l r => (eval V val l) == (eval V val r)
    | BoolExpr.Not e => not (eval_bool val e)
    | BoolExpr.And l r => if eval_bool val l then eval_bool val r else false
    | BoolExpr.Or l r => if eval_bool val l then true else eval_bool val r

inductive BoolStep: (val: V -> Int) -> (BoolExpr V) -> (BoolExpr V) -> Prop where
    | notIsBoolNot (b: Bool): BoolStep val
        (BoolExpr.Not (BoolExpr.Const b))
        (BoolExpr.Const !b)
    | andLeftTrue (e: BoolExpr V): BoolStep val
        (BoolExpr.And (BoolExpr.Const true) e)
        e
    | orLeftFalse (e: BoolExpr V): BoolStep val
        (BoolExpr.Or (BoolExpr.Const false) e)
        e
    | andLeftShortCircuit e : BoolStep val
        (BoolExpr.And (BoolExpr.Const false) e)
        (BoolExpr.Const false)
    | orLeftShortCircuit e : BoolStep val
        (BoolExpr.Or (BoolExpr.Const true) e)
        (BoolExpr.Const true)


    | lessConstConstTrue n₁ n₂ : n₁ < n₂ -> BoolStep val
        (BoolExpr.Less (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const true)
    | lessConstConstFalse n₁ n₂ : n₁ >= n₂ -> BoolStep val
        (BoolExpr.Less (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const false)
    | eqConstConstTrue n₁ n₂ : n₁ = n₂ -> BoolStep val
        (BoolExpr.Eq (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const true)
    | eqConstConstFalse n₁ n₂ : n₁ != n₂ -> BoolStep val
        (BoolExpr.Eq (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const false)
    | lessArStepLeft (e₁ e₁' e₂: ArExpr V):
        ArStep V val e₁ e₁' ->
            BoolStep val
                (BoolExpr.Less e₁ e₂)
                (BoolExpr.Less e₁' e₂)
    | eqArStepLeft (e₁ e₁' e₂: ArExpr V):
        ArStep V val e₁ e₁' ->
            BoolStep val
                (BoolExpr.Eq e₁ e₂)
                (BoolExpr.Eq e₁' e₂)
     | lessArStepRight (e₁ e₂ e₂': ArExpr V):
        ArStep V val e₂ e₂' ->
            BoolStep val
                (BoolExpr.Less e₁ e₂)
                (BoolExpr.Less e₁ e₂')
    | eqArStepRight (e₁ e₂ e₂': ArExpr V):
        ArStep V val e₂ e₂' ->
            BoolStep val
                (BoolExpr.Eq e₁ e₂)
                (BoolExpr.Eq e₁ e₂')
    | orStepLeft (e₁ e₁' e₂: BoolExpr V):
        BoolStep val e₁ e₁' ->
            BoolStep val
                (BoolExpr.Or e₁ e₂)
                (BoolExpr.Or e₁' e₂)
    | andStepLeft (e₁ e₁' e₂: BoolExpr V):
        BoolStep val e₁ e₁' ->
            BoolStep val
                (BoolExpr.And e₁ e₂)
                (BoolExpr.And e₁' e₂)
    | notStep (e e' : BoolExpr V):
        BoolStep val e e' -> BoolStep val
            (BoolExpr.Not e)
            (BoolExpr.Not e')

def BoolStepStar (V: Type) := StepStar (Step := BoolStep) V
def BoolStepStar.refl {V: Type} (val: V -> Int) := StepStar.refl (Step := BoolStep) val
def BoolStepStar.trans {V: Type} {val: V -> Int} e₁ e₂ e₃ := StepStar.trans e₁ e₂ e₃ (Step := BoolStep) (val := val)
