variable (V: Type)

-- Arithmetic Expressions

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

-- Small steps semantic for arithmetic expressions

inductive ArStep: (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | getVarValue (var: V) :
        ArStep
            val
            (ArExpr.Var var)
            (ArExpr.Const (val var))
    | addConstConst(n₁ n₂: Int) :
        ArStep
            val
            (ArExpr.Add (ArExpr.Const n₁) (ArExpr.Const n₂))
            (ArExpr.Const (n₁ + n₂))
    | subConstConst(n₁ n₂: Int) :
        ArStep
            val
            (ArExpr.Sub (ArExpr.Const n₁) (ArExpr.Const n₂))
            (ArExpr.Const (n₁ - n₂))
    | mulConstConst(n₁ n₂: Int) :
        ArStep
            val
            (ArExpr.Mul (ArExpr.Const n₁) (ArExpr.Const n₂))
            (ArExpr.Const (n₁ * n₂))
    | addLeft (e₁ e₁' e₂) : ArStep val e₁ e₁' -> ArStep val (ArExpr.Add e₁ e₂) (ArExpr.Add e₁' e₂)

    | subLeft (e₁ e₁' e₂) : ArStep val e₁ e₁' -> ArStep val (ArExpr.Sub e₁ e₂) (ArExpr.Sub e₁' e₂)

    | mulLeft (e₁ e₁' e₂) : ArStep val e₁ e₁' -> ArStep val (ArExpr.Mul e₁ e₂) (ArExpr.Mul e₁' e₂)

    | addRight (n: Int) (e₂ e₂': ArExpr V) : ArStep val e₂ e₂' -> ArStep val (ArExpr.Add (ArExpr.Const n) e₂)  (ArExpr.Add (ArExpr.Const n) e₂')

    | subRight (n: Int) (e₂ e₂': ArExpr V) : ArStep val e₂ e₂' -> ArStep val (ArExpr.Sub (ArExpr.Const n) e₂)  (ArExpr.Sub (ArExpr.Const n) e₂')
    | mulRight (n: Int) (e₂ e₂': ArExpr V) : ArStep val e₂ e₂' -> ArStep val (ArExpr.Mul (ArExpr.Const n) e₂)  (ArExpr.Mul (ArExpr.Const n) e₂')

inductive ArStepStar : (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | refl val e : ArStepStar val e e
    | trans e₁ e₂ e₃ : (ArStep V val) e₁ e₂ -> ArStepStar val e₂ e₃ -> ArStepStar val e₁ e₃

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
    | refl _ => apply ArStepStar.refl
    | trans _ _ _ step _ ih =>
        apply ArStepStar.trans
        . exact ArStep.addLeft _ _ _ step
        . exact ih

theorem arstepstar_add_right (n: Int) (e₂ e₂': ArExpr V) :
    ArStepStar V val e₂ e₂' ->
        ArStepStar V val
            (ArExpr.Add (ArExpr.Const n) e₂)
            (ArExpr.Add (ArExpr.Const n) e₂') := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans e₁ e₂ e3 step1 step2 ih =>
        apply ArStepStar.trans
        . apply ArStep.addRight _ _ _ step1
        . exact ih



theorem arstepstar_sub_left (e₁ e₁' e₂: ArExpr V) :
    ArStepStar V val e₁ e₁' ->
        ArStepStar V val
            (ArExpr.Sub e₁ e₂)
            (ArExpr.Sub e₁' e₂) := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans _ _ _ step _ ih =>
        apply ArStepStar.trans
        . exact ArStep.subLeft _ _ _ step
        . exact ih

theorem arstepstar_sub_right (n: Int) (e₂ e₂': ArExpr V) :
    ArStepStar V val e₂ e₂' ->
        ArStepStar V val
            (ArExpr.Sub (ArExpr.Const n) e₂)
            (ArExpr.Sub (ArExpr.Const n) e₂') := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans e₁ e₂ e3 step1 step2 ih =>
        apply ArStepStar.trans
        . apply ArStep.subRight _ _ _ step1
        . exact ih



theorem arstepstar_mul_left (e₁ e₁' e₂: ArExpr V) :
    ArStepStar V val e₁ e₁' ->
        ArStepStar V val
            (ArExpr.Mul e₁ e₂)
            (ArExpr.Mul e₁' e₂) := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans _ _ _ step _ ih =>
        apply ArStepStar.trans
        . exact ArStep.mulLeft _ _ _ step
        . exact ih

theorem arstepstar_mul_right (n: Int) (e₂ e₂': ArExpr V) :
    ArStepStar V val e₂ e₂' ->
        ArStepStar V val
            (ArExpr.Mul (ArExpr.Const n) e₂)
            (ArExpr.Mul (ArExpr.Const n) e₂') := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans e₁ e₂ e3 step1 step2 ih =>
        apply ArStepStar.trans
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
        have h4 := ArStepStar.trans _ _ _ step h3
        exact h4


theorem eval_soundness (e: ArExpr V) (v: Int) :
    ArStepStar V val e (ArExpr.Const v) -> eval V val e = v := by
    exact arstepstar_preserves_eval _ _ _


theorem eval_completeness (e: ArExpr V) : ArStepStar V val e (ArExpr.Const (eval V val e)) := by
    induction e with
    | Const x =>
        simp [eval]
        exact ArStepStar.refl _ _
    | Add e₁ e₂ ih1 ih2 =>
        -- ih1 : ArStepStar e₁ (ArExpr.Const (eval e₁))
        -- ih2 : ArStepStar e₂ (ArExpr.Const (eval e₂))
        simp [eval]
        have a := arstepstar_add_left _ _ _ e₂ ih1
        have b := arstepstar_add_right _ (eval V val e₁) e₂ _ ih2
        have c := ArStep.addConstConst (val := val) (eval V val e₁) (eval V val e₂)
        have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const (eval V val e₁ + eval V val e₂)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Sub e₁ e₂ ih1 ih2 =>
        -- ih1 : ArStepStar e₁ (ArExpr.Const (eval e₁))
        -- ih2 : ArStepStar e₂ (ArExpr.Const (eval e₂))
        simp [eval]
        have a := arstepstar_sub_left _ _ _ e₂ ih1
        have b := arstepstar_sub_right _ (eval V val e₁) e₂ _ ih2
        have c := ArStep.subConstConst (val := val) (eval V val e₁) (eval V val e₂)
        have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const  (eval V val e₁ - eval V val e₂)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Mul e₁ e₂ ih1 ih2 =>
        -- ih1 : ArStepStar e₁ (ArExpr.Const (eval e₁))
        -- ih2 : ArStepStar e₂ (ArExpr.Const (eval e₂))
        simp [eval]
        have a := arstepstar_mul_left _ _ _ e₂ ih1
        have b := arstepstar_mul_right _ (eval V val e₁) e₂ _ ih2
        have c := ArStep.mulConstConst (val := val) (eval V val e₁) (eval V val e₂)
        have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const (eval  V val e₁ * eval V val e₂)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Var var =>
        simp [eval]
        have a := ArStep.getVarValue var (val := val)
        have b := ArStepStar.refl val (ArExpr.Const (val var))
        exact ArStepStar.trans (val := val) _ _ _ a b


-- Boolean Expressions

inductive BoolExpr : Type
    | True: BoolExpr
    | False : BoolExpr
    | Less: ArExpr V -> ArExpr V -> BoolExpr
    | Eq: ArExpr V -> ArExpr V -> BoolExpr
    | Not : BoolExpr -> BoolExpr
    | And : BoolExpr -> BoolExpr -> BoolExpr
    | Or : BoolExpr -> BoolExpr -> BoolExpr

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
