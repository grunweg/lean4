/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Command
import Lean.Elab.Tactic.Meta

/-!
Commands to validate tactic results.
-/

namespace Lean.Elab.CheckTactic

open Lean.Meta CheckTactic
open Lean.Elab.Tactic
open Lean.Elab.Command

private def matchCheckGoalType (stx : Syntax) (goalType : Expr) : MetaM (Expr × Expr × Level) := do
  let u ← mkFreshLevelMVar
  let type ← mkFreshExprMVar (some (.sort u))
  let val  ← mkFreshExprMVar (some type)
  let extType := mkAppN (.const ``CheckGoalType [u]) #[type, val]
  if !(← isDefEq goalType extType) then
    throwErrorAt stx "Goal{indentExpr goalType}\nis expected to match {indentExpr extType}"
  pure (val, type, u)

@[builtin_command_elab Lean.Parser.checkTactic]
def elabCheckTactic : CommandElab := fun stx => do
  let `(#check_tactic $t ~> $result by $tac) := stx | throwUnsupportedSyntax
  withoutModifyingEnv $ do
    runTermElabM $ fun _vars => do
      let u ← Lean.Elab.Term.elabTerm t none
      let type ← inferType u
      let lvl ← mkFreshLevelMVar
      let checkGoalType : Expr := mkApp2 (mkConst ``CheckGoalType [lvl]) type u
      let mvar ← mkFreshExprMVar (.some checkGoalType)
      let (goals, _) ← Lean.Elab.runTactic mvar.mvarId! tac.raw
      let expTerm ← Lean.Elab.Term.elabTerm result (.some type)
      match goals with
      | [] =>
        throwErrorAt stx
          m!"{tac} closed goal, but is expected to reduce to {indentExpr expTerm}."
      | [next] => do
        let (val, _, _) ← matchCheckGoalType stx (←next.getType)
        if !(← Meta.withReducible <| isDefEq val expTerm) then
          throwErrorAt stx
            m!"Term reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
      | _ => do
        throwErrorAt stx
          m!"{tac} produced multiple goals, but is expected to reduce to {indentExpr expTerm}."
      pure ()

@[builtin_command_elab Lean.Parser.checkTacticFailure]
def elabCheckTacticFailure : CommandElab := fun stx => do
  let `(#check_tactic_failure $t by $tactic) := stx | throwUnsupportedSyntax
  withoutModifyingEnv $ do
    runTermElabM $ fun _vars => do
      let val ← Lean.Elab.Term.elabTerm t none
      let type ← inferType val
      let lvl ← mkFreshLevelMVar
      let checkGoalType : Expr := mkApp2 (mkConst ``CheckGoalType [lvl]) type val
      let mvar ← mkFreshExprMVar (.some checkGoalType)
      let act := Lean.Elab.runTactic mvar.mvarId! tactic.raw
      match ← try (Term.withoutErrToSorry (some <$> act)) catch _ => pure none with
        | none =>
          pure ()
        | some (gls, _) =>
          let ppGoal (g : MVarId) := do
                let (val, _type, _u) ← matchCheckGoalType stx (← g.getType)
                pure m!"{indentExpr val}"
          let msg ←
            match gls with
              | [] => pure m!"{tactic} expected to fail on {val}, but closed goal."
              | [g] =>
                pure <| m!"{tactic} expected to fail on {val}, but returned: {←ppGoal g}"
              | gls =>
                let app m g := do pure <| m ++ (←ppGoal g)
                let init := m!"{tactic} expected to fail on {val}, but returned goals:"
                gls.foldlM (init := init) app
          throwErrorAt stx msg

@[builtin_macro Lean.Parser.checkSimp]
def expandCheckSimp : Macro := fun stx => do
  let `(#check_simp $t ~> $exp) := stx | Macro.throwUnsupported
  `(command|#check_tactic $t ~> $exp by simp)

@[builtin_macro Lean.Parser.checkSimpFailure]
def expandCheckSimpFailure : Macro := fun stx => do
  let `(#check_simp $t !~>) := stx | Macro.throwUnsupported
  `(command|#check_tactic_failure $t by simp)

end Lean.Elab.CheckTactic
