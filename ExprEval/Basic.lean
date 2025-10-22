variable (V: Type)

inductive ArExpr: Type
    | Const: Int -> ArExpr
    | Add: ArExpr -> ArExpr -> ArExpr
    | Sub: ArExpr -> ArExpr -> ArExpr
    | Mul: ArExpr -> ArExpr -> ArExpr
    | Var: V -> ArExpr


def eval (val: V -> Int) (e: ArExpr V) : Int :=
    match e with
        | ArExpr.Const x => x
        | ArExpr.Add lhs rhs => (eval val lhs) + (eval val rhs)
        | ArExpr.Sub lhs rhs => (eval val lhs) - (eval val rhs)
        | ArExpr.Mul lhs rhs => (eval val lhs) * (eval val rhs)
        | ArExpr.Var v => val v

-- My small steps semantic

inductive Step: (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | getVarValue (var: V) :
        Step
            val
            (ArExpr.Var var)
            (ArExpr.Const (val var))
    | addConstConst(n1 n2: Int) :
        Step
            val
            (ArExpr.Add (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 + n2))
    | subConstConst(n1 n2: Int) :
        Step
            val
            (ArExpr.Sub (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 - n2))
    | mulConstConst(n1 n2: Int) :
        Step
            val
            (ArExpr.Mul (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 * n2))
    | addLeft (e1 e1' e2) : Step val e1 e1' -> Step val (ArExpr.Add e1 e2) (ArExpr.Add e1' e2)

    | subLeft (e1 e1' e2) : Step val e1 e1' -> Step val (ArExpr.Sub e1 e2) (ArExpr.Sub e1' e2)

    | mulLeft (e1 e1' e2) : Step val e1 e1' -> Step val (ArExpr.Mul e1 e2) (ArExpr.Mul e1' e2)

    | addRight (n: Int) (e2 e2': ArExpr V) : Step val e2 e2' -> Step val (ArExpr.Add (ArExpr.Const n) e2)  (ArExpr.Add (ArExpr.Const n) e2')

    | subRight (n: Int) (e2 e2': ArExpr V) : Step val e2 e2' -> Step val (ArExpr.Sub (ArExpr.Const n) e2)  (ArExpr.Sub (ArExpr.Const n) e2')
    | mulRight (n: Int) (e2 e2': ArExpr V) : Step val e2 e2' -> Step val (ArExpr.Mul (ArExpr.Const n) e2)  (ArExpr.Mul (ArExpr.Const n) e2')

inductive StepStar : (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | refl val e : StepStar val e e
    | trans e₁ e₂ e₃ : (Step V val) e₁ e₂ -> StepStar val e₂ e₃ -> StepStar val e₁ e₃

theorem step_preserve_eval (e e': ArExpr V): (Step V val) e e' -> eval V val e = eval V val e' := by
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

    | getVarValue var => simp [eval]


theorem stepstar_preserves_eval (e e': ArExpr V) :
    StepStar V val e e' -> eval V val e = eval V val e' := by
    intro h
    induction h with
    | refl _ => rfl
    | trans _ _ _ h1 _ ih => rw [step_preserve_eval _ _ _ h1, ih]

theorem soundness (e: ArExpr V) (v: Int) :
    StepStar V val e (ArExpr.Const v) -> eval V val e = v := by
    exact stepstar_preserves_eval _ _ _

theorem stepstar_add_left (e1 e1' e2: ArExpr V) :
    StepStar V val e1 e1' -> StepStar V val (ArExpr.Add e1 e2) (ArExpr.Add e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.addLeft _ _ _ step
        . exact ih

theorem stepstar_add_right (n: Int) (e2 e2': ArExpr V) :
    StepStar V val e2 e2' ->
        StepStar V val
            (ArExpr.Add (ArExpr.Const n) e2)
            (ArExpr.Add (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.addRight _ _ _ step1
        . exact ih



theorem stepstar_sub_left (e1 e1' e2: ArExpr V) :
    StepStar V val e1 e1' ->
        StepStar V val
            (ArExpr.Sub e1 e2)
            (ArExpr.Sub e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.subLeft _ _ _ step
        . exact ih

theorem stepstar_sub_right (n: Int) (e2 e2': ArExpr V) :
    StepStar V val e2 e2' ->
        StepStar V val
            (ArExpr.Sub (ArExpr.Const n) e2)
            (ArExpr.Sub (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.subRight _ _ _ step1
        . exact ih



theorem stepstar_mul_left (e1 e1' e2: ArExpr V) :
    StepStar V val e1 e1' ->
        StepStar V val
            (ArExpr.Mul e1 e2)
            (ArExpr.Mul e1' e2) := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans _ _ _ step _ ih =>
        apply StepStar.trans
        . exact Step.mulLeft _ _ _ step
        . exact ih

theorem stepstar_mul_right (n: Int) (e2 e2': ArExpr V) :
    StepStar V val e2 e2' ->
        StepStar V val
            (ArExpr.Mul (ArExpr.Const n) e2)
            (ArExpr.Mul (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply StepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply StepStar.trans
        . apply Step.mulRight _ _ _ step1
        . exact ih

theorem chasles_step_star {e1 e2 e3: ArExpr V}:
    StepStar V val e1 e2 ->
        StepStar V val e2 e3 ->
            StepStar V val e1 e3 := by
    intros h1 h2
    induction h1 with
    | refl e => exact h2
    | trans a b c step rest ihn =>
        have h3 := ihn h2
        have h4 := StepStar.trans _ _ _ step h3
        exact h4

theorem completeness (e: ArExpr V) : StepStar V val e (ArExpr.Const (eval V val e)) := by
    induction e with
    | Const x =>
        simp [eval]
        exact StepStar.refl _ _
    | Add e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : StepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := stepstar_add_left _ _ _ e2 ih1
        have b := stepstar_add_right _ (eval V val e1) e2 _ ih2
        have c := Step.addConstConst (val := val) (eval V val e1) (eval V val e2)
        have d := StepStar.trans _ _ _ c (StepStar.refl _ (ArExpr.Const (eval V val e1 + eval V val e2)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Sub e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : StepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := stepstar_sub_left _ _ _ e2 ih1
        have b := stepstar_sub_right _ (eval V val e1) e2 _ ih2
        have c := Step.subConstConst (val := val) (eval V val e1) (eval V val e2)
        have d := StepStar.trans _ _ _ c (StepStar.refl _ (ArExpr.Const  (eval V val e1 - eval V val e2)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Mul e1 e2 ih1 ih2 =>
        -- ih1 : StepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : StepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := stepstar_mul_left _ _ _ e2 ih1
        have b := stepstar_mul_right _ (eval V val e1) e2 _ ih2
        have c := Step.mulConstConst (val := val) (eval V val e1) (eval V val e2)
        have d := StepStar.trans _ _ _ c (StepStar.refl _ (ArExpr.Const (eval  V val e1 * eval V val e2)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Var var =>
        simp [eval]
        have a := Step.getVarValue var (val := val)
        have b := StepStar.refl val (ArExpr.Const (val var))
        exact StepStar.trans (val := val) _ _ _ a b
