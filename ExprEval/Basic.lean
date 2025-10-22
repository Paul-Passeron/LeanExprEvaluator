

inductive Expr: Type
    | Const: Int -> Expr
    | Add: Expr -> Expr -> Expr
    | Sub: Expr -> Expr -> Expr
    | Mul: Expr -> Expr -> Expr

def eval (e: Expr): Int :=
    match e with
        | Expr.Const x => x
        | Expr.Add lhs rhs => (eval lhs) + (eval rhs)
        | Expr.Sub lhs rhs => (eval lhs) - (eval rhs)
        | Expr.Mul lhs rhs => (eval lhs) * (eval rhs)


-- My small steps semantic

inductive Step: Expr -> Expr -> Prop where
    | addConstConst(n1 n2: Int) :
        Step
            (Expr.Add (Expr.Const n1) (Expr.Const n2))
            (Expr.Const (n1 + n2))
    | subConstConst(n1 n2: Int) :
        Step
            (Expr.Sub (Expr.Const n1) (Expr.Const n2))
            (Expr.Const (n1 - n2))
    | mulConstConst(n1 n2: Int) :
        Step
            (Expr.Mul (Expr.Const n1) (Expr.Const n2))
            (Expr.Const (n1 * n2))
    | addLeft (e1 e1' e2) : Step e1 e1' -> Step (Expr.Add e1 e2) (Expr.Add e1' e2)
    | subLeft (e1 e1' e2) : Step e1 e1' -> Step (Expr.Sub e1 e2) (Expr.Sub e1' e2)
    | mulLeft (e1 e1' e2) : Step e1 e1' -> Step (Expr.Mul e1 e2) (Expr.Mul e1' e2)
    | addRight (n: Int) (e2 e2': Expr) : Step e2 e2' -> Step (Expr.Add (Expr.Const n) e2)  (Expr.Add (Expr.Const n) e2')
    | subRight (n: Int) (e2 e2': Expr) : Step e2 e2' -> Step (Expr.Sub (Expr.Const n) e2)  (Expr.Sub (Expr.Const n) e2')
    | mulRight (n: Int) (e2 e2': Expr) : Step e2 e2' -> Step (Expr.Mul (Expr.Const n) e2)  (Expr.Mul (Expr.Const n) e2')

inductive StepStar : Expr → Expr → Prop where
    | refl e : StepStar e e
    | trans e₁ e₂ e₃ : Step e₁ e₂ → StepStar e₂ e₃ → StepStar e₁ e₃

theorem step_preserve_eval (e e': Expr): Step e e' -> eval e = eval e' := by
    intro h
    induction h with

    | addConstConst n1 n2
    | subConstConst n1 n2
    | mulConstConst n1 n2 => simp [eval]

    | addLeft e1 e1' e2 _ ih
    | subLeft e1 e1' e2 _ ih
    | mulLeft e1 e1' e2 _ ih => simp [eval, ih]

    | addRight n e2 e1' _ ih
    | subRight n e2 e1' _ ih
    | mulRight n e2 e1' _ ih => simp [eval, ih]

theorem stepstar_preserves_eval (e e': Expr) : StepStar e e' → eval e = eval e' := by
    intro h
    induction h with
    | refl _ => rfl
    | trans _ _ _ h1 _ ih => rw [step_preserve_eval _ _ h1, ih]

theorem soundness (e: Expr) (v: Int) : StepStar e (Expr.Const v) → eval e = v := by
    exact stepstar_preserves_eval _ _

theorem stepstar_add_left (e1 e1' e2: Expr) :
    StepStar e1 e1' → StepStar (Expr.Add e1 e2) (Expr.Add e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.addLeft _ _ _ step
        . exact ih

theorem stepstar_add_right (n: Int) (e2 e2': Expr) :
    StepStar e2 e2' → StepStar (Expr.Add (Expr.Const n) e2) (Expr.Add (Expr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.addRight _ _ _ step1
        . exact ih

theorem completeness (e: Expr) : StepStar e (Expr.Const (eval e)) := by
    induction e with
    | Const x =>
        simp [eval]
        exact StepStar.refl _
    | Add e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (Expr.Const (eval e1))
        -- ih2 : StepStar e2 (Expr.Const (eval e2))
        simp [eval]
        have a := stepstar_add_left _ _ e2 ih1
        sorry
    | Sub e1 e2 => sorry
    | Mul e1 e2 => sorry
