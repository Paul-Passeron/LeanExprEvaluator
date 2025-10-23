import ExprEval.Expr
import ExprEval.ArStepLemmas

def eval_bool (val: V -> Int) (e: BoolExpr V): Bool :=
    match e with
    | BoolExpr.True => true
    | BoolExpr.False => false
    | BoolExpr.Less l r =>  (eval V val l) < (eval V val r)
    | BoolExpr.Eq l r => (eval V val l) == (eval V val r)
    | BoolExpr.Not e => not (eval_bool val e)
    | BoolExpr.And l r => if eval_bool val l then eval_bool val r else false
    | BoolExpr.Or l r => if eval_bool val l then true else eval_bool val r

inductive BoolStep: (val: V -> Int) -> (BoolExpr V) -> (BoolExpr V) -> Prop where
    | notFalseIsTrue: BoolStep val
        (BoolExpr.Not BoolExpr.False)
        BoolExpr.True
    | notTrueIsFalse : BoolStep val
        (BoolExpr.Not BoolExpr.True)
         BoolExpr.False
    | andLeftTrue (e: BoolExpr V): BoolStep val
        (BoolExpr.And BoolExpr.True e)
        e
    | orLeftFalse (e: BoolExpr V): BoolStep val
        (BoolExpr.Or BoolExpr.False e)
        e
    | andLeftShortCircuit e : BoolStep val
        (BoolExpr.And BoolExpr.False e)
        BoolExpr.False
    | orLeftShortCircuit e : BoolStep val
        (BoolExpr.Or BoolExpr.True e)
        BoolExpr.True
    | lessConstConst n₁ n₂ : BoolStep val
        (BoolExpr.Less (ArExpr.Const n₁) (ArExpr.Const n₂))
        (if n₁ < n₂ then BoolExpr.True else BoolExpr.False)
    | eqConstConst n₁ n₂ : BoolStep val
        (BoolExpr.Eq (ArExpr.Const n₁) (ArExpr.Const n₂))
        (if n₁ == n₂ then BoolExpr.True else BoolExpr.False)
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

    -- | orStepRight (e₁ e₂ e₂': BoolExpr V):
    --     BoolStep val e₂ e₂' ->
    --         BoolStep val
    --             (BoolExpr.Or e₁ e₂)
    --             (BoolExpr.Or e₁ e₂')
    -- | andStepRight (e₁ e₂ e₂': BoolExpr V):
    --     BoolStep val e₂ e₂' ->
    --         BoolStep val
    --             (BoolExpr.And e₁ e₂)
    --             (BoolExpr.And e₁ e₂')
    | notStep (e e' : BoolExpr V):
        BoolStep val e e' -> BoolStep val
            (BoolExpr.Not e)
            (BoolExpr.Not e')
