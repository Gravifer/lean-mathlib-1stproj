import Lean.Elab.Tactic
/-! # Tactics -/
/-! ## Exploring `TacticM` -/
#print Lean.Elab.Tactic.getMainTag
#print Lean.Elab.Tactic.getMainDecl
#print Lean.Elab.Tactic.getMainTarget
#print Lean.Elab.Tactic.getMainGoal
#print Lean.Elab.Tactic.closeMainGoal
#print Lean.Elab.Tactic.replaceMainGoal
#print Lean.Elab.Tactic.withMainContext
#print Lean.Elab.admitGoal
#print Lean.Elab.Tactic.getGoals
#print Lean.Elab.Tactic.setGoals

#print Lean.MonadLCtx.getLCtx
#print Lean.LocalDecl
#print Lean.Meta.inferType
#print Lean.Meta.mkAppM
#print Lean.Meta.isExprDefEq
#print Lean.Meta.mkEqRefl
#print Lean.Meta.mkEqTrans
#print Lean.Meta.mkEqSymm
#print Lean.Meta.mkCongrArg
#print Lean.Meta.mkCongrFun
#print Lean.Meta.mkLambdaFVars
#print Lean.Meta.mkLetFVars
#print Lean.Meta.getFVarLocalDecl
#print Lean.Meta.throwTacticEx

#print Lean.Elab.Tactic.evalTactic
#print Lean.Elab.Tactic.liftMetaTactic
#print Lean.MVarId.assert
