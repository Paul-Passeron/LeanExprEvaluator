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

-- My small steps semantic

inductive ArStep: (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | getVarValue (var: V) :
        ArStep
            val
            (ArExpr.Var var)
            (ArExpr.Const (val var))
    | addConstConst(n1 n2: Int) :
        ArStep
            val
            (ArExpr.Add (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 + n2))
    | subConstConst(n1 n2: Int) :
        ArStep
            val
            (ArExpr.Sub (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 - n2))
    | mulConstConst(n1 n2: Int) :
        ArStep
            val
            (ArExpr.Mul (ArExpr.Const n1) (ArExpr.Const n2))
            (ArExpr.Const (n1 * n2))
    | addLeft (e1 e1' e2) : ArStep val e1 e1' -> ArStep val (ArExpr.Add e1 e2) (ArExpr.Add e1' e2)

    | subLeft (e1 e1' e2) : ArStep val e1 e1' -> ArStep val (ArExpr.Sub e1 e2) (ArExpr.Sub e1' e2)

    | mulLeft (e1 e1' e2) : ArStep val e1 e1' -> ArStep val (ArExpr.Mul e1 e2) (ArExpr.Mul e1' e2)

    | addRight (n: Int) (e2 e2': ArExpr V) : ArStep val e2 e2' -> ArStep val (ArExpr.Add (ArExpr.Const n) e2)  (ArExpr.Add (ArExpr.Const n) e2')

    | subRight (n: Int) (e2 e2': ArExpr V) : ArStep val e2 e2' -> ArStep val (ArExpr.Sub (ArExpr.Const n) e2)  (ArExpr.Sub (ArExpr.Const n) e2')
    | mulRight (n: Int) (e2 e2': ArExpr V) : ArStep val e2 e2' -> ArStep val (ArExpr.Mul (ArExpr.Const n) e2)  (ArExpr.Mul (ArExpr.Const n) e2')

inductive ArStepStar : (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | refl val e : ArStepStar val e e
    | trans e₁ e₂ e₃ : (ArStep V val) e₁ e₂ -> ArStepStar val e₂ e₃ -> ArStepStar val e₁ e₃

theorem arstep_preserve_eval (e e': ArExpr V): (ArStep V val) e e' -> eval V val e = eval V val e' := by
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


theorem arstepstar_preserves_eval (e e': ArExpr V) :
    ArStepStar V val e e' -> eval V val e = eval V val e' := by
    intro h
    induction h with
    | refl _ => rfl
    | trans _ _ _ h1 _ ih => rw [arstep_preserve_eval _ _ _ h1, ih]

theorem arstepstar_add_left (e1 e1' e2: ArExpr V) :
    ArStepStar V val e1 e1' -> ArStepStar V val (ArExpr.Add e1 e2) (ArExpr.Add e1' e2) := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans _ _ _ step _ ih =>
        apply ArStepStar.trans
        . exact ArStep.addLeft _ _ _ step
        . exact ih

theorem arstepstar_add_right (n: Int) (e2 e2': ArExpr V) :
    ArStepStar V val e2 e2' ->
        ArStepStar V val
            (ArExpr.Add (ArExpr.Const n) e2)
            (ArExpr.Add (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply ArStepStar.trans
        . apply ArStep.addRight _ _ _ step1
        . exact ih



theorem arstepstar_sub_left (e1 e1' e2: ArExpr V) :
    ArStepStar V val e1 e1' ->
        ArStepStar V val
            (ArExpr.Sub e1 e2)
            (ArExpr.Sub e1' e2) := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans _ _ _ step _ ih =>
        apply ArStepStar.trans
        . exact ArStep.subLeft _ _ _ step
        . exact ih

theorem arstepstar_sub_right (n: Int) (e2 e2': ArExpr V) :
    ArStepStar V val e2 e2' ->
        ArStepStar V val
            (ArExpr.Sub (ArExpr.Const n) e2)
            (ArExpr.Sub (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply ArStepStar.trans
        . apply ArStep.subRight _ _ _ step1
        . exact ih



theorem arstepstar_mul_left (e1 e1' e2: ArExpr V) :
    ArStepStar V val e1 e1' ->
        ArStepStar V val
            (ArExpr.Mul e1 e2)
            (ArExpr.Mul e1' e2) := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans _ _ _ step _ ih =>
        apply ArStepStar.trans
        . exact ArStep.mulLeft _ _ _ step
        . exact ih

theorem arstepstar_mul_right (n: Int) (e2 e2': ArExpr V) :
    ArStepStar V val e2 e2' ->
        ArStepStar V val
            (ArExpr.Mul (ArExpr.Const n) e2)
            (ArExpr.Mul (ArExpr.Const n) e2') := by
    intro h
    induction h with
    | refl _ => apply ArStepStar.refl
    | trans e1 e2 e3 step1 step2 ih =>
        apply ArStepStar.trans
        . apply ArStep.mulRight _ _ _ step1
        . exact ih

theorem chasles_step_star {e1 e2 e3: ArExpr V}:
    ArStepStar V val e1 e2 ->
        ArStepStar V val e2 e3 ->
            ArStepStar V val e1 e3 := by
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
    | Add e1 e2 ih1 ih2 =>
        -- ih1 : ArStepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : ArStepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := arstepstar_add_left _ _ _ e2 ih1
        have b := arstepstar_add_right _ (eval V val e1) e2 _ ih2
        have c := ArStep.addConstConst (val := val) (eval V val e1) (eval V val e2)
        have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const (eval V val e1 + eval V val e2)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Sub e1 e2 ih1 ih2 =>
        -- ih1 : ArStepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : ArStepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := arstepstar_sub_left _ _ _ e2 ih1
        have b := arstepstar_sub_right _ (eval V val e1) e2 _ ih2
        have c := ArStep.subConstConst (val := val) (eval V val e1) (eval V val e2)
        have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const  (eval V val e1 - eval V val e2)))
        have e := chasles_step_star _ a (chasles_step_star _ b d)
        exact e
    | Mul e1 e2 ih1 ih2 =>
        -- ih1 : ArStepStar e1 (ArExpr.Const (eval e1))
        -- ih2 : ArStepStar e2 (ArExpr.Const (eval e2))
        simp [eval]
        have a := arstepstar_mul_left _ _ _ e2 ih1
        have b := arstepstar_mul_right _ (eval V val e1) e2 _ ih2
        have c := ArStep.mulConstConst (val := val) (eval V val e1) (eval V val e2)
        have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const (eval  V val e1 * eval V val e2)))
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
