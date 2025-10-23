import ExprEval.Expr

variable (V: Type)

-- Arithmetic Expressions


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

def ArStepStar (V: Type) := StepStar (StepKind := ArStep V) V
def ArStepStar.refl {V: Type} (val: V -> Int) := StepStar.refl (StepKind := ArStep V) val
def ArStepStar.trans {V: Type} {val: V -> Int} e₁ e₂ e₃ := StepStar.trans e₁ e₂ e₃ (StepKind := ArStep V) (val := val)
