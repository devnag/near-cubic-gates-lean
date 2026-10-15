import Proof.Assembly.ActualGenerator

/-! Source-global SYM/THR programs composed at the actual physical mode bit.
Each branch carries exact native execution/rows on its own stated domain.
The full actual-call cost and domain-transfer proofs remain in GeneratedRecipe.
No asymptotic raw-generation claim is inferred from final lowered size. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace PhysicalModeBranches
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NativeRecipes FamilyInitGenerator
open NativeFamilyGenerator PrefixInitializerFront

/-- Printer choice is shared; each mode may use its own fixed private scratch.
Neither code nor the number of tapes depends on live input. -/
structure Fixed (a : WilliamsAlgorithm) where
  scratch : Nat
  states : Nat
  machine : Machine (tapes a (7+scratch)) states
  policy : Policy
  result : Input → Result (tapes a (7+scratch))

noncomputable def Fixed.code {a : WilliamsAlgorithm} (g : Fixed a) : PrefixCode :=
  { printer := a, scratch := g.scratch, states := g.states,
    machine := g.machine, policy := g.policy, result := g.result }

/-- Qualitative execution and exact native rows, with no universal resource
estimate. Every finite fuel here is still charged by the actual-call recipe.
This is the branch's OWN policy guard; a merged policy does not imply it. -/
noncomputable abbrev ModeExact (sources : EightSources) (mode : Bool)
    (g : PrefixCode) : Prop :=
  ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat),
  Admissible sources g.policy atoms L target recordWidth mode →
  let i := inputOf atoms L target recordWidth mode true
  let r := g.result i
  FrontProduced g i ∧
  NativeRows sources L target mode atoms g.printer r.S r.R r.B r.rowWidth
    r.ds r.total r.denominator ∧
  r.rowWidth ≤ recordWidth ∧ r.total < 2^recordWidth

/-- A complete genuine mode producer, not just an inhabitant of a code type.
Actual admitted calls must later establish this mode-specific domain and pay
this same result fuel. False/vacuous policy choices do not meet that task. -/
structure Mode (sources : EightSources) (mode : Bool) where
  fixed : Fixed (williamsOf sources)
  correct : ModeExact sources mode fixed.code

abbrev GlobalMode (mode : Bool) := (sources : EightSources) → (gamma : Real) →
  (hg : 0<gamma) → (hh : gamma<1/2) → (p : Parameters sources gamma) →
  Mode sources mode

/-- Core ports keep their numbers; only unused private scratch is appended. -/
noncomputable def slots (a : WilliamsAlgorithm) (small large : Nat)
    (h : small ≤ large) : Fin (tapes a (7+small)) → Fin (tapes a (7+large)) :=
  fun j => ⟨j.val, by have hj := j.isLt; unfold tapes at *; omega⟩

noncomputable def widen {a : WilliamsAlgorithm} (g : Fixed a)
    (large : Nat) (h : g.scratch ≤ large) : Fixed a :=
  { scratch := large
    states := g.states
    machine := RecoveryFocus.machine (slots a g.scratch large h) g.machine
    policy := g.policy
    result := fun i =>
      let r := g.result i
      { ds := r.ds, S := r.S, R := r.R, B := r.B,
        rowWidth := r.rowWidth, total := r.total, denominator := r.denominator,
        residual := r.residual, fuel := r.fuel,
        H := dockH (slots a g.scratch large h) (fun _ => 0) r.H,
        A := install (slots a g.scratch large h) (fun _ => []) r.A } }

noncomputable def modeSlot (a : WilliamsAlgorithm) (scratch : Nat) :
    Fin (tapes a (7+scratch)) :=
  ⟨r_tapes a+7, by unfold tapes; omega⟩

/-- Bookkeeping envelope only. Actual-call correctness must instantiate the
selected branch's own guard; maxima below do not justify a guard implication. -/
def joinedPolicy (sym thr : Policy) : Policy :=
  { width := fun mode q L target =>
      if mode then sym.width mode q L target else thr.width mode q L target
    degree := fun mode q L target =>
      if mode then sym.degree mode q L target else thr.degree mode q L target
    cacheCoefficient := max sym.cacheCoefficient thr.cacheCoefficient
    cacheDegree := max sym.cacheDegree thr.cacheDegree
    inputCoefficient := max sym.inputCoefficient thr.inputCoefficient
    inputDegree := max sym.inputDegree thr.inputDegree
    sourceCoefficient := max sym.sourceCoefficient thr.sourceCoefficient
    sourceDegree := max sym.sourceDegree thr.sourceDegree
    syntaxCoefficient := max sym.syntaxCoefficient thr.syntaxCoefficient
    syntaxDegree := max sym.syntaxDegree thr.syntaxDegree
    tableCoefficient := max sym.tableCoefficient thr.tableCoefficient
    tableDegree := max sym.tableDegree thr.tableDegree }

/-- Real fixed code: read the physical mode bit, run exactly that branch in
shared core ports, and retain its full endpoint/fuel plus the two switch ticks.
Terminal handling and final initialization remain the accepted outer stages. -/
noncomputable def combine {a : WilliamsAlgorithm} (sym thr : Fixed a) : Fixed a :=
  let large := sym.scratch+thr.scratch
  let s := widen sym large (by dsimp only [large]; omega)
  let t := widen thr large (by dsimp only [large]; omega)
  { scratch := large
    states := _
    machine := CloseoutRowsOriginalSwitch.machine s.machine t.machine (modeSlot a large)
    policy := joinedPolicy sym.policy thr.policy
    result := fun i =>
      let r := if i.mode then s.result i else t.result i
      { r with fuel := r.fuel+2 } }

noncomputable def global (sym : GlobalMode true) (thr : GlobalMode false) :
    ActualNativeCode.NativeCode :=
  fun sources gamma hg hh p =>
    (combine (sym sources gamma hg hh p).fixed
      (thr sources gamma hg hh p).fixed).code

end PhysicalModeBranches
