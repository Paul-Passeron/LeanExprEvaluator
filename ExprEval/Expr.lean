variable (V: Type)

-- Arithmetic Expressions

inductive ArExpr: Type
    | Const: Int -> ArExpr
    | Add: ArExpr -> ArExpr -> ArExpr
    | Sub: ArExpr -> ArExpr -> ArExpr
    | Mul: ArExpr -> ArExpr -> ArExpr
    | Var: V -> ArExpr


-- Boolean Expressions

inductive BoolExpr : Type
    | Const: Bool -> BoolExpr
    | Less: ArExpr V -> ArExpr V -> BoolExpr
    | Eq: ArExpr V -> ArExpr V -> BoolExpr
    | Not : BoolExpr -> BoolExpr
    | And : BoolExpr -> BoolExpr -> BoolExpr
    | Or : BoolExpr -> BoolExpr -> BoolExpr

inductive StepStar {ExprType: Type} {StepKind: (V -> Int) -> ExprType -> ExprType -> Prop} : (val: V -> Int) -> ExprType -> ExprType -> Prop where
        | refl val e : StepStar val e e
        | trans e₁ e₂ e₃ : StepKind val e₁ e₂ -> StepStar val e₂ e₃ -> StepStar val e₁ e₃
