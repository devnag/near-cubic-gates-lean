import MainTheorem
import Lean.Util.CollectAxioms
open Lean Elab Command

/-! Run after `lake build`:  lake env lean Check.lean
It prints the paper's main theorem as stated in Lean, the published results it assumes (the fields of
`PublishedInputs`) with their full statements and the definitions each one uses, the main theorem, its axioms,
and PASS or FAIL. -/

-- (a) The statement: the published results imply the paper's main theorem (`thm:main`). Every definition it
-- uses is in `Statement.lean`; the ones below are those of the main theorem's conclusion.
#print NearCubicGates.Close.FinalStatement
#print NearCubicGates.Target.MainStatement
#print NearCubicGates.Target.MainAt
#print NearCubicGates.Target.MainBudget
#print NearCubicGates.Target.lambda
#print NearCubicGates.Target.mu
#print NearCubicGates.Target.agreement
#print NearCubicGates.Target.WeightedSymmetricCircuit
#print NearCubicGates.Target.WeightedSymmetricCircuit.topWeight
#print NearCubicGates.Target.WeightedSymmetricCircuit.score
#print NearCubicGates.Target.WeightedSymmetricCircuit.eval
#print NearCubicGates.Target.InENP

-- (b) The hypotheses: the published results, the fields of `PublishedInputs`, and each published statement.
#print NearCubicGates.Close.PublishedInputs
#print NearCubicGates.Published.Apostol.primeNumberTheorem
#print NearCubicGates.Published.Williams.RectangularProductLeaf
#print NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1
#print NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17
#print NearCubicGates.Published.STV.Theorem29
#print NearCubicGates.Published.CW19Proximity.Lemma22Half
#print NearCubicGates.Published.CW19Code.Lemma26

-- (c) For each published statement, the definitions of `Statement.lean` it uses (its closure).
run_cmd do
  let env ← getEnv
  let some stmt := env.getModuleIdx? `Statement | throwError "FAIL: module Statement not loaded"
  for f in getStructureFields env ``NearCubicGates.Close.PublishedInputs do
    let some p := env.find? (``NearCubicGates.Close.PublishedInputs ++ f) | throwError "FAIL: no projection {f}"
    let mut work : Array Name := p.type.getUsedConstants.filter (· != ``NearCubicGates.Close.PublishedInputs)
    let mut seen : NameSet := {}
    let mut names : Array Name := #[]
    while 0 < work.size do
      let n := work.back!
      work := work.pop
      if seen.contains n || env.getModuleIdxFor? n != some stmt then continue
      seen := seen.insert n
      unless n.isInternal || Meta.isMatcherCore env n do names := names.push n
      if let some ci := env.find? n then
        for u in ci.getUsedConstantsAsSet do work := work.push u
    let sorted := names.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{f} uses {sorted.size} declarations of Statement.lean: {sorted.toList}"

-- (d) The main theorem, its axioms, and PASS only if: the main theorem is stated as `FinalStatement`;
-- `FinalStatement` is `PublishedInputs → MainStatement`; the fields of `PublishedInputs` are exactly the published
-- statements below, in this order; `FinalStatement`, `PublishedInputs`, `MainStatement` and every published
-- statement are declared in `Statement.lean`; and the axioms are exactly Lean's standard three.
run_cmd do
  let env ← getEnv
  let thm := `NearCubicGates.Close.main_from_published
  let final := ``NearCubicGates.Close.FinalStatement
  let inputs := ``NearCubicGates.Close.PublishedInputs
  let target := ``NearCubicGates.Target.MainStatement
  let expected : List (Name × Expr) := [
    (`apostol_primeNumberTheorem, mkConst ``NearCubicGates.Published.Apostol.primeNumberTheorem []),
    (`williams_rectangularProductLeaf, mkConst ``NearCubicGates.Published.Williams.RectangularProductLeaf []),
    (`bcgt13_theorem11_1, mkConst ``NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1 []),
    (`shoup_findIrrPolyAlgorithm17, mkConst ``NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17 []),
    (`stv_theorem29, mkConst ``NearCubicGates.Published.STV.Theorem29 []),
    (`cw19Proximity_lemma22Half, mkConst ``NearCubicGates.Published.CW19Proximity.Lemma22Half []),
    (`cw19Code_lemma26, mkConst ``NearCubicGates.Published.CW19Code.Lemma26 [])]
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  let some stmt := env.getModuleIdx? `Statement | throwError "FAIL: module Statement not loaded"
  let some info := env.find? thm |
    let partialThm := `NearCubicGates.Close.main_from_published_of
    match env.find? partialThm with
    | some pi =>
      IO.println s!"{partialThm} : {← liftTermElabM <| Meta.ppExpr pi.type}"
      throwError "FAIL: {thm} is not proved yet; {partialThm} above still takes the fields of `NineInputs` that are not derived"
    | none => throwError "FAIL: {thm} not found"
  IO.println s!"{thm} : {← liftTermElabM <| Meta.ppExpr info.type}"
  let okThm := info matches .thmInfo _ && info.type == mkConst final
  let okFinal := match env.find? final with
    | some (.defnInfo d) => match d.value with
      | .forallE _ dom body _ => dom == mkConst inputs && body == mkConst target
      | _ => false
    | _ => false
  let okStruct := match env.find? inputs with
    | some (.inductInfo i) => i.type == mkSort Level.zero && i.numParams == 0 && isStructure env inputs
    | _ => false
  let mut found : List (Name × Expr) := []
  for f in getStructureFields env inputs do
    let some p := env.find? (inputs ++ f) | throwError "FAIL: no projection {inputs ++ f}"
    let t := match p.type with
      | .forallE _ _ b _ => b
      | e => e
    found := found ++ [(f, t)]
    IO.println s!"assumes {f} : {← liftTermElabM <| Meta.ppExpr t}"
  let okInputs := okStruct && found == expected
  let trusted := [final, inputs, target] ++ expected.map (fun (_, e) => e.constName!)
  let okTrusted := trusted.all (fun n => env.getModuleIdxFor? n == some stmt)
  let axs ← liftCoreM <| collectAxioms thm
  IO.println s!"axioms of {thm}: {axs.toList}"
  let okAxioms := axs.all std.contains && std.all axs.contains
  if okThm && okFinal && okInputs && okTrusted && okAxioms then
    IO.println s!"PASS: {thm} proves {final}: the {expected.length} published results above imply {target}; it depends on the axioms {axs.toList} only"
  else
    throwError "FAIL: stated as {final}: {okThm}; {final} = {inputs} → {target}: {okFinal}; the published results as listed: {okInputs}; all in Statement.lean: {okTrusted}; axioms exactly propext, Classical.choice, Quot.sound: {okAxioms} ({axs.toList})"
