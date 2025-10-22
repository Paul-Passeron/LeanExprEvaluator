inductive ArExpr: Type
    | Const: Int -> ArExpr
    | Add: ArExpr -> ArExpr -> ArExpr
    | Sub: ArExpr -> ArExpr -> ArExpr
    | Mul: ArExpr -> ArExpr -> ArExpr

def eval (e: ArExpr): Int :=
    match e with
        | ArExpr.Const x => x
        | ArExpr.Add lhs rhs => (eval lhs) + (eval rhs)
        | ArExpr.Sub lhs rhs => (eval lhs) - (eval rhs)
        | ArExpr.Mul lhs rhs => (eval lhs) * (eval rhs)


-- My small steps semantic

inductive Step: ArExpr -> ArExpr -> Prop where
    | addConstConst(n1 n2: Int) :
        Step
            (ArExpr.Add (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 + n2))
    | subConstConst(n1 n2: Int) :
        Step
            (ArExpr.Sub (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 - n2))
    | mulConstConst(n1 n2: Int) :
        Step
            (ArExpr.Mul (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 * n2))
    | addLeft (e1 e1' e2) : Step e1 e1' -> Step (ArExpr.Add e1 e2) (ArExpr.Add e1' e2)
    | subLeft (e1 e1' e2) : Step e1 e1' -> Step (ArExpr.Sub e1 e2) (ArExpr.Sub e1' e2)
    | mulLeft (e1 e1' e2) : Step e1 e1' -> Step (ArExpr.Mul e1 e2) (ArExpr.Mul e1' e2)
    | addRight (n: Int) (e2 e2': ArExpr) : Step e2 e2' -> Step (ArExpr.Add (ArExpr.Const n) e2)  (ArExpr.Add (ArExpr.Const n) e2')
    | subRight (n: Int) (e2 e2': ArExpr) : Step e2 e2' -> Step (ArExpr.Sub (ArExpr.Const n) e2)  (ArExpr.Sub (ArExpr.Const n) e2')
    | mulRight (n: Int) (e2 e2': ArExpr) : Step e2 e2' -> Step (ArExpr.Mul (ArExpr.Const n) e2)  (ArExpr.Mul (ArExpr.Const n) e2')

inductive StepStar : ArExpr → ArExpr → Prop where
    | refl e : StepStar e e
    | trans e₁ e₂ e₃ : Step e₁ e₂ → StepStar e₂ e₃ → StepStar e₁ e₃

theorem step_preserve_eval (e e': ArExpr): Step e e' -> eval e = eval e' := by
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

theorem stepstar_preserves_eval (e e': ArExpr) : StepStar e e' → eval e = eval e' := by
    intro h
    induction h with
    | refl _ => rfl
    | trans _ _ _ h1 _ ih => rw [step_preserve_eval _ _ h1, ih]

theorem soundness (e: ArExpr) (v: Int) : StepStar e (ArExpr.Const v) → eval e = v := by
    exact stepstar_preserves_eval _ _

theorem stepstar_add_left (e1 e1' e2: ArExpr) :
    StepStar e1 e1' → StepStar (ArExpr.Add e1 e2) (ArExpr.Add e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.addLeft _ _ _ step
        . exact ih

theorem stepstar_add_right (n: Int) (e2 e2': ArExpr) :
    StepStar e2 e2' → StepStar (ArExpr.Add (ArExpr.Const n) e2) (ArExpr.Add (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.addRight _ _ _ step1
        . exact ih



theorem stepstar_sub_left (e1 e1' e2: ArExpr) :
    StepStar e1 e1' → StepStar (ArExpr.Sub e1 e2) (ArExpr.Sub e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.subLeft _ _ _ step
        . exact ih

theorem stepstar_sub_right (n: Int) (e2 e2': ArExpr) :
    StepStar e2 e2' → StepStar (ArExpr.Sub (ArExpr.Const n) e2) (ArExpr.Sub (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.subRight _ _ _ step1
        . exact ih



theorem stepstar_mul_left (e1 e1' e2: ArExpr) :
    StepStar e1 e1' → StepStar (ArExpr.Mul e1 e2) (ArExpr.Mul e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.mulLeft _ _ _ step
        . exact ih

theorem stepstar_mul_right (n: Int) (e2 e2': ArExpr) :
    StepStar e2 e2' → StepStar (ArExpr.Mul (ArExpr.Const n) e2) (ArExpr.Mul (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.mulRight _ _ _ step1
        . exact ih

theorem chasle_step_star {e1 e2 e3: ArExpr}: StepStar e1 e2 -> StepStar e2 e3 -> StepStar e1 e3 := by
    intros h1 h2
    induction h1 with
    | refl e => exact h2
    | trans a b c step rest ihn =>
        have h3 := ihn h2
        have h4 := StepStar.trans _ _ _ step h3
        exact h4

theorem completeness (e: ArExpr) : StepStar e (ArExpr.Const (eval e)) := by
    induction e with
    | Const x =>
        simp [eval]
        exact StepStar.refl _
    | Add e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : StepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := stepstar_add_left _ _ e2 ih1
        have b := stepstar_add_right (eval e1) e2 _ ih2
        have c := Step.addConstConst (eval e1) (eval e2)
        have d := StepStar.trans _ _ _ c (StepStar.refl (ArExpr.Const (eval e1 + eval e2)))
        have e := chasle_step_star a (chasle_step_star b d)
        exact e
    | Sub e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : StepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := stepstar_sub_left _ _ e2 ih1
        have b := stepstar_sub_right (eval e1) e2 _ ih2
        have c := Step.subConstConst (eval e1) (eval e2)
        have d := StepStar.trans _ _ _ c (StepStar.refl (ArExpr.Const (eval e1 - eval e2)))
        have e := chasle_step_star a (chasle_step_star b d)
        exact e
    | Mul e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : StepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := stepstar_mul_left _ _ e2 ih1
        have b := stepstar_mul_right (eval e1) e2 _ ih2
        have c := Step.mulConstConst (eval e1) (eval e2)
        have d := StepStar.trans _ _ _ c (StepStar.refl (ArExpr.Const (eval e1 * eval e2)))
        have e := chasle_step_star a (chasle_step_star b d)
        exact e
