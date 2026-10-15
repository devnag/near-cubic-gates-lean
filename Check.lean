import MainTheorem
import Lean.Util.CollectAxioms
open Lean Elab Command

/-! Run after `lake build`:  lake env lean Check.lean
It prints the paper's main theorem as stated in Lean, the nine published inputs it assumes, the main theorem, its
axioms, and PASS or FAIL. -/

-- (a) The statement: the nine published inputs imply the paper's main theorem (`thm:main`). Every definition it
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

-- (b) The hypotheses: the nine published inputs, the fields of `NineInputs`.
#print NearCubicGates.Close.NineInputs

-- (c) The main theorem.
#check @NearCubicGates.Close.main_from_inputs

-- (d) Its axioms. An unfinished proof would list `sorryAx` here.
#print axioms NearCubicGates.Close.main_from_inputs

-- (e) PASS only if the main theorem is stated as `FinalStatement`, `FinalStatement` is `NineInputs → MainStatement`,
-- the fields of `NineInputs` are exactly the nine statements below, in this order, and the axioms are exactly
-- Lean's standard three.
run_cmd do
  let env ← getEnv
  let thm := ``NearCubicGates.Close.main_from_inputs
  let final := ``NearCubicGates.Close.FinalStatement
  let inputs := ``NearCubicGates.Close.NineInputs
  let target := ``NearCubicGates.Target.MainStatement
  -- These are the only assumptions. Each is defined in `Statement.lean`; `SourceMapping/` shows each beside the
  -- published statement it transcribes.
  let expected : List (Name × Expr) := [
    (`normalization, mkConst ``NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2),
    (`restriction, mkConst ``NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction),
    (`bernstein, mkConst ``NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein
      [Level.zero, Level.zero]),
    (`primes, mkConst ``NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem),
    (`rectangularProduct, mkConst ``NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4),
    (`shortPCP, mkConst ``NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2),
    (`refuter, mkConst ``NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13),
    (`amplification, mkConst ``NearCubicGates.Close.CLW20_Lemma3_9_Multitape),
    (`threeQueryPCPP, mkConst ``NearCubicGates.PublishedSources.PCPP.ThreeQuerySourceGroup)]
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  let some info := env.find? thm | throwError "FAIL: {thm} not found"
  -- the main theorem is a theorem whose statement is literally `FinalStatement`
  let okThm := info matches .thmInfo _ && info.type == mkConst final
  -- `FinalStatement` is the implication `NineInputs → MainStatement`
  let okFinal := match env.find? final with
    | some (.defnInfo d) => match d.value with
      | .forallE _ dom body _ => dom == mkConst inputs && body == mkConst target
      | _ => false
    | _ => false
  -- `NineInputs` is a structure in `Prop`, without parameters, whose fields are exactly the nine statements above
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
  let axs ← liftCoreM <| collectAxioms thm
  let okAxioms := axs.all std.contains && std.all axs.contains
  if okThm && okFinal && okInputs && okAxioms then
    IO.println s!"PASS: {thm} proves {final}: the {expected.length} published inputs above imply {target}; it depends on the axioms {axs.toList} only"
  else
    throwError "FAIL: stated as {final}: {okThm}; {final} = {inputs} → {target}: {okFinal}; the nine inputs as listed: {okInputs}; axioms exactly propext, Classical.choice, Quot.sound: {okAxioms} ({axs.toList})"
