import ExprEval.Expr
import ExprEval.Boolean

theorem boolstep_preserves_eval_bool (e e': BoolExpr V):
  BoolStep val e e' -> eval_bool val e = eval_bool val e' := by
  intro h
  induction h with
  | notIsBoolNot b => simp [eval_bool]
  | andLeftTrue e => simp [eval_bool]
  | orLeftFalse e => simp [eval_bool]
  | andLeftShortCircuit e => simp [eval_bool]
  | orLeftShortCircuit e => simp [eval_bool]
  | lessConstConstTrue n1 n2 h =>
    simp [eval_bool]
    simp [eval]
    exact h
  | lessConstConstFalse n1 n2 h =>
    simp [eval_bool]
    simp [eval]
    exact h
  | eqConstConstTrue n1 n2 h =>
    simp [eval_bool]
    simp [eval]
    exact h
  | eqConstConstFalse n1 n2 h =>
    simp [eval_bool]
    simp [eval]
    simp [bne_iff_ne] at h
    exact h
  | lessArStepLeft e₁ e₁' e₂ arstep
  | eqArStepLeft e₁ e₁' e₂ arstep
  | lessArStepRight e₁ e₂ e₂' arstep
  | eqArStepRight e₁ e₂ e₂' arstep =>
    simp [eval_bool]
    have h' := arstep_preserve_eval _ _ _ arstep
    rw [h']
  | orStepLeft e₁ e₁' e₂ step ihn
  | andStepLeft e₁ e₁' e₂ step ihn =>
    simp [eval_bool]
    rw [ihn]
  | notStep e e' step ihn =>
    simp[eval_bool]
    rw [ihn]

theorem boolstepstar_preserves_eval_bool (e e': BoolExpr V):
  BoolStepStar V val e e' -> eval_bool val e = eval_bool val e' := by
  intro h
  induction h with
  | refl => rfl
  | trans _ _ _ h_step _ ihn =>
    rw [<- ihn]
    exact boolstep_preserves_eval_bool _ _ h_step

theorem BoolStepStar.notStep {V: Type} {val: V -> Int}
  (e e': BoolExpr V):
    BoolStepStar V val e e' -> BoolStepStar V val (BoolExpr.Not e) (BoolExpr.Not e') := by
  intro h
  induction h with
  | refl => apply BoolStepStar.refl
  | trans e₁ e₂ e₃ step _ ihn =>
    have h':= BoolStep.notStep _ _ step
    apply BoolStepStar.trans _ _ _ h' ihn
