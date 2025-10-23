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
    | True: BoolExpr
    | False : BoolExpr
    | Less: ArExpr V -> ArExpr V -> BoolExpr
    | Eq: ArExpr V -> ArExpr V -> BoolExpr
    | Not : BoolExpr -> BoolExpr
    | And : BoolExpr -> BoolExpr -> BoolExpr
    | Or : BoolExpr -> BoolExpr -> BoolExpr
