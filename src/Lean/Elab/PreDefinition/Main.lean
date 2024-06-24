/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.SCC
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural
import Lean.Elab.PreDefinition.WF.Main
import Lean.Elab.PreDefinition.MkInhabitant

namespace Lean.Elab
open Meta
open Term

private def addAndCompilePartial (preDefs : Array PreDefinition) (useSorry := false) : TermElabM Unit := do
  for preDef in preDefs do
    trace[Elab.definition] "processing {preDef.declName}"
    let all := preDefs.toList.map (·.declName)
    forallTelescope preDef.type fun xs type => do
      let value ← if useSorry then
        mkLambdaFVars xs (← mkSorry type (synthetic := true))
      else
        liftM <| mkInhabitantFor preDef.declName xs type
      addNonRec { preDef with
        kind  := DefKind.«opaque»
        value
      } (all := all)
  addAndCompilePartialRec preDefs

private def isNonRecursive (preDef : PreDefinition) : Bool :=
  Option.isNone $ preDef.value.find? fun
    | Expr.const declName _ => preDef.declName == declName
    | _ => false

private def partitionPreDefs (preDefs : Array PreDefinition) : Array (Array PreDefinition) :=
  let getPreDef    := fun declName => (preDefs.find? fun preDef => preDef.declName == declName).get!
  let vertices     := preDefs.toList.map (·.declName)
  let successorsOf := fun declName => (getPreDef declName).value.foldConsts [] fun declName successors =>
    if preDefs.any fun preDef => preDef.declName == declName then
      declName :: successors
    else
      successors
  let sccs := SCC.scc vertices successorsOf
  sccs.toArray.map fun scc => scc.toArray.map getPreDef

private def collectMVarsAtPreDef (preDef : PreDefinition) : StateRefT CollectMVars.State MetaM Unit := do
  collectMVars preDef.value
  collectMVars preDef.type

private def getMVarsAtPreDef (preDef : PreDefinition) : MetaM (Array MVarId) := do
  let (_, s) ← (collectMVarsAtPreDef preDef).run {}
  pure s.result

private def ensureNoUnassignedMVarsAtPreDef (preDef : PreDefinition) : TermElabM PreDefinition := do
  let pendingMVarIds ← getMVarsAtPreDef preDef
  if (← logUnassignedUsingErrorInfos pendingMVarIds) then
    let preDef := { preDef with value := (← mkSorry preDef.type (synthetic := true)) }
    if (← getMVarsAtPreDef preDef).isEmpty then
      return preDef
    else
      throwAbortCommand
  else
    return preDef

/--
  Letrec declarations produce terms of the form `(fun .. => ..) d` where `d` is a (partial) application of an auxiliary declaration for a letrec declaration.
  This method beta-reduces them to make sure they can be eliminated by the well-founded recursion module. -/
private def betaReduceLetRecApps (preDefs : Array PreDefinition) : MetaM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    let value ← Core.transform preDef.value fun e => do
      if e.isApp && e.getAppFn.isLambda && e.getAppArgs.all fun arg => arg.getAppFn.isConst && preDefs.any fun preDef => preDef.declName == arg.getAppFn.constName! then
        return .visit e.headBeta
      else
        return .continue
    return { preDef with value }

private def addAsAxioms (preDefs : Array PreDefinition) : TermElabM Unit := do
  for preDef in preDefs do
    let decl := Declaration.axiomDecl {
      name        := preDef.declName,
      levelParams := preDef.levelParams,
      type        := preDef.type,
      isUnsafe    := preDef.modifiers.isUnsafe
    }
    addDecl decl
    withSaveInfoContext do  -- save new env
      addTermInfo' preDef.ref (← mkConstWithLevelParams preDef.declName) (isBinder := true)
    applyAttributesOf #[preDef] AttributeApplicationTime.afterTypeChecking
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

def ensureFunIndReservedNamesAvailable (preDefs : Array PreDefinition) : MetaM Unit := do
  preDefs.forM fun preDef =>
    withRef preDef.ref <| ensureReservedNameAvailable preDef.declName "induct"
  withRef preDefs[0]!.ref <| ensureReservedNameAvailable preDefs[0]!.declName "mutual_induct"


/--
Checks consistency of a clique of TerminationHints:

* If one has a termination hint, all of them have one
* If one has `structurally`, all have it, and no `decreasing_by` may appear

-/
def checkTerminationByHints (preDefs : Array PreDefinition) : CoreM Unit := do
  let some preDefWith := preDefs.find? (·.termination.terminationBy?.isSome) | return
  let structurally :=
    preDefWith.termination.terminationBy? matches some {structurally := true, ..}
  for preDef in preDefs do
    if let .some ref := preDef.termination.terminationBy?? then
      throwErrorAt ref (m!"Useless `termination_by?`; this function is mutually " ++
        m!"recursive with {preDefWith.declName}, which already has a `termination_by` clause.")
    let .some termBy := preDef.termination.terminationBy?
      | throwErrorAt preDef.ref (m!"Missing `termination_by`; this function is mutually " ++
        m!"recursive with {preDefWith.declName}, which has a `termination_by` clause.")
    if structurally && ! termBy.structurally then
      throwErrorAt termBy.ref (m!"Invalid `termination_by`; this function is mutually " ++
        m!"recursive with {preDefWith.declName}, which has a `termination_by structurally` " ++
        m!"so this one also needs to be marked `structurally` clause.")
    if ! structurally && termBy.structurally then
      throwErrorAt termBy.ref (m!"Invalid `termination_by`; this function is mutually " ++
        m!"recursive with {preDefWith.declName}, which is not marked as `structurally` " ++
        m!"so this one canot be `structurally` either.")
    if termBy.structurally then
      if let .some decr := preDef.termination.decreasingBy? then
        throwErrorAt decr.ref (m!"Invalid `decreasing_by`; this function is marked as " ++
          m!"structurally recursive, so no explicit termination proof is needed.")

/--
Elaborates the `TerminationHint` in the clique to `TerminationArguments`
-/
def elabTerminationByHints (preDefs : Array PreDefinition) : TermElabM (Option TerminationArguments) := do
  -- if one has a terminationBy, then all do
  if preDefs[0]!.termination.terminationBy?.isSome then
    let tas ← preDefs.mapM fun preDef => do
      let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
      let hints := preDef.termination
      TerminationArgument.elab preDef.declName preDef.type arity hints.extraParams hints.terminationBy?.get!
    return some tas
  else
    return none

def shouldUseStructural (preDefs : Array PreDefinition) : Bool :=
  preDefs.any fun preDef =>
    preDef.termination.terminationBy? matches some {structurally := true, ..}

def shouldUseWF (preDefs : Array PreDefinition) : Bool :=
  preDefs.any fun preDef =>
    preDef.termination.terminationBy? matches some {structurally := false, ..} ||
    preDef.termination.decreasingBy?.isSome


def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := withLCtx {} {} do
  for preDef in preDefs do
    trace[Elab.definition.body] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
  let preDefs ← preDefs.mapM ensureNoUnassignedMVarsAtPreDef
  let preDefs ← betaReduceLetRecApps preDefs
  let cliques := partitionPreDefs preDefs
  for preDefs in cliques do
    trace[Elab.definition.scc] "{preDefs.map (·.declName)}"
    if preDefs.size == 1 && isNonRecursive preDefs[0]! then
      /-
      We must erase `recApp` annotations even when `preDef` is not recursive
      because it may use another recursive declaration in the same mutual block.
      See issue #2321
      -/
      let preDef ← eraseRecAppSyntax preDefs[0]!
      ensureEqnReservedNamesAvailable preDef.declName
      if preDef.modifiers.isNoncomputable then
        addNonRec preDef
      else
        addAndCompileNonRec preDef
      preDef.termination.ensureNone "not recursive"
    else if preDefs.any (·.modifiers.isUnsafe) then
      addAndCompileUnsafe preDefs
      preDefs.forM (·.termination.ensureNone "unsafe")
    else if preDefs.any (·.modifiers.isPartial) then
      for preDef in preDefs do
        if preDef.modifiers.isPartial && !(← whnfD preDef.type).isForall then
          withRef preDef.ref <| throwError "invalid use of 'partial', '{preDef.declName}' is not a function{indentExpr preDef.type}"
      addAndCompilePartial preDefs
      preDefs.forM (·.termination.ensureNone "partial")
    else
      ensureFunIndReservedNamesAvailable preDefs
      try
        checkTerminationByHints preDefs
        let termArgs ← elabTerminationByHints preDefs
        if shouldUseStructural preDefs then
          structuralRecursion preDefs termArgs
        else if shouldUseWF preDefs then
          wfRecursion preDefs termArgs
        else
          withRef (preDefs[0]!.ref) <| mapError
            (orelseMergeErrors
              (structuralRecursion preDefs termArgs)
              (wfRecursion preDefs termArgs))
            (fun msg =>
              let preDefMsgs := preDefs.toList.map (MessageData.ofExpr $ mkConst ·.declName)
              m!"fail to show termination for{indentD (MessageData.joinSep preDefMsgs Format.line)}\nwith errors\n{msg}")
      catch ex =>
        logException ex
        let s ← saveState
        try
          if preDefs.all fun preDef => preDef.kind == DefKind.def || preDefs.all fun preDef => preDef.kind == DefKind.abbrev then
            -- try to add as partial definition
            try
              addAndCompilePartial preDefs (useSorry := true)
            catch _ =>
              -- Compilation failed try again just as axiom
              s.restore
              addAsAxioms preDefs
          else if preDefs.all fun preDef => preDef.kind == DefKind.theorem then
            addAsAxioms preDefs
        catch _ => s.restore

builtin_initialize
  registerTraceClass `Elab.definition.body
  registerTraceClass `Elab.definition.scc

end Lean.Elab
