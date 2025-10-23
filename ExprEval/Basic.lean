import ExprEval.Arithmetic
import ExprEval.Boolean

import ExprEval.ArStepLemmas
import ExprEval.BoolStepLemmas

variable (V: Type)

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

theorem eval_bool_soundness (e: BoolExpr V) (b: Bool) :
    BoolStepStar V val e (BoolExpr.Const b) -> eval_bool val e = b := by
    intro h
    exact boolstepstar_preserves_eval_bool _ _ h

theorem eval_bool_completeness (e: BoolExpr V): BoolStepStar V val e (BoolExpr.Const (eval_bool val e)) := by
    induction e with
    | Const b =>
        simp [eval_bool]
        apply BoolStepStar.refl
    | Not e ihn =>
        simp [eval_bool]
        have h := BoolStepStar.notStep e _ ihn
        have h1 := BoolStep.notIsBoolNot (eval_bool val e) (val := val)
        have h2 := (step_to_stepstar V h1)
        apply chasles_step_star V h h2
    | _ => sorry
