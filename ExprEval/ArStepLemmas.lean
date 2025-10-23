import ExprEval.Arithmetic
variable (V: Type)

theorem arstep_preserve_eval (e e': ArExpr V): (ArStep V val) e e' -> eval V val e = eval V val e' := by
    intro h
    induction h with

    | addConstConst n₁ n₂
    | subConstConst n₁ n₂
    | mulConstConst n₁ n₂ => simp [eval]

    | addLeft e₁ e₁' e₂ _ ih
    | subLeft e₁ e₁' e₂ _ ih
    | mulLeft e₁ e₁' e₂ _ ih => simp [eval, ih]

    | addRight n e₂ e₁' _ ih
    | subRight n e₂ e₁' _ ih
    | mulRight n e₂ e₁' _ ih => simp [eval, ih]

    | getVarValue var => simp [eval]

theorem arstepstar_preserves_eval (e e': ArExpr V) :
    ArStepStar V val e e' -> eval V val e = eval V val e' := by
    intro h
    induction h with
    | refl _ => rfl
    | trans _ _ _ h1 _ ih => rw [arstep_preserve_eval _ _ _ h1, ih]

theorem arstepstar_add_left (e₁ e₁' e₂: ArExpr V) :
    ArStepStar V val e₁ e₁' -> ArStepStar V val (ArExpr.Add e₁ e₂) (ArExpr.Add e₁' e₂) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact ArStep.addLeft _ _ _ step
        . exact ih

theorem arstepstar_add_right (n: Int) (e₂ e₂': ArExpr V) :
    ArStepStar V val e₂ e₂' ->
        ArStepStar V val
            (ArExpr.Add (ArExpr.Const n) e₂)
            (ArExpr.Add (ArExpr.Const n) e₂') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e₁ e₂ e3 step1 step2 ih =>
        apply StepStar.trans
        . apply ArStep.addRight _ _ _ step1
        . exact ih

theorem arstepstar_sub_left (e₁ e₁' e₂: ArExpr V) :
    ArStepStar V val e₁ e₁' ->
        ArStepStar V val
            (ArExpr.Sub e₁ e₂)
            (ArExpr.Sub e₁' e₂) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact ArStep.subLeft _ _ _ step
        . exact ih

theorem arstepstar_sub_right (n: Int) (e₂ e₂': ArExpr V) :
    ArStepStar V val e₂ e₂' ->
        ArStepStar V val
            (ArExpr.Sub (ArExpr.Const n) e₂)
            (ArExpr.Sub (ArExpr.Const n) e₂') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e₁ e₂ e3 step1 step2 ih =>
        apply StepStar.trans
        . apply ArStep.subRight _ _ _ step1
        . exact ih

theorem arstepstar_mul_left (e₁ e₁' e₂: ArExpr V) :
    ArStepStar V val e₁ e₁' ->
        ArStepStar V val
            (ArExpr.Mul e₁ e₂)
            (ArExpr.Mul e₁' e₂) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact ArStep.mulLeft _ _ _ step
        . exact ih

theorem arstepstar_mul_right (n: Int) (e₂ e₂': ArExpr V) :
    ArStepStar V val e₂ e₂' ->
        ArStepStar V val
            (ArExpr.Mul (ArExpr.Const n) e₂)
            (ArExpr.Mul (ArExpr.Const n) e₂') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e₁ e₂ e3 step1 step2 ih =>
        apply StepStar.trans
        . apply ArStep.mulRight _ _ _ step1
        . exact ih

theorem chasles_step_star {e₁ e₂ e3: ArExpr V}:
    ArStepStar V val e₁ e₂ ->
        ArStepStar V val e₂ e3 ->
            ArStepStar V val e₁ e3 := by
    intros h1 h2
    induction h1 with
    | refl e => exact h2
    | trans a b c step rest ihn =>
        have h3 := ihn h2
        have h4 := StepStar.trans _ _ _ step h3
        exact h4
