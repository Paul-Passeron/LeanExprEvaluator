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

def StepKind (V: Type) (ExprType: Type):= (V -> Int) -> ExprType -> ExprType -> Prop

inductive StepStar {ExprType: Type} {Step: StepKind V ExprType} : (val: V -> Int) -> ExprType -> ExprType -> Prop where
        | refl val e : StepStar val e e
        | trans e₁ e₂ e₃ : Step val e₁ e₂ -> StepStar val e₂ e₃ -> StepStar val e₁ e₃

theorem chasles_step_star {ExprKind: Type} {Step: StepKind V ExprKind} {e₁ e₂ e₃: ExprKind}:
    StepStar (Step := Step) V val e₁ e₂  ->
        StepStar (Step := Step) V val e₂ e₃ ->
            StepStar (Step := Step) V val e₁ e₃ := by
    intros h1 h2
    induction h1 with
    | refl e => exact h2
    | trans a b c step _ ihn =>
        have h3 := ihn h2
        have h4 := StepStar.trans _ _ _ step h3
        exact h4

theorem step_to_stepstar {ExprKind: Type} {Step: StepKind V ExprKind} {e e': ExprKind}:
    Step val e e' -> StepStar (Step := Step) V val e e' := by
    intro h
    have h': StepStar (Step := Step) V val e' e' := StepStar.refl val e'
    apply StepStar.trans _ _ _ h h'
