import Proof.Assembly.CacheCompose
import Proof.CaseAnalysis.RowsDegreeLoop

/-! Immediate local enclosure for the complete SYM descriptor suffix.
One fixed initialization, one fixed repeated row body, and one fixed finalizer
consume the actual prepared bank. No row stream is supplied as input advice.
Only the real loop/sequence composition is proved here; the components remain
explicit inputs of the local plan until its enclosing application is checked. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace SymSuffixLoop
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NativeRecipes FamilyInitGenerator
open NativeFamilyGenerator CacheComposition

/-- All finite code and the slot map are chosen before runtime Input.
The repeat driver is an additional local tape, excluded from the row body.
The body owns its runtime ordinal and preserves its actual reusable banks. -/
structure Code {sources : EightSources} {m : Bool} (a : Program sources m) where
  extra : Nat
  bodyTapes : Nat
  bodyStates : Nat
  rowMachine : Machine bodyTapes bodyStates
  loopSlots : Fin (bodyTapes+1) → Fin (tapes (williamsOf sources) (7+(11+a.scratch+extra)))
  loopSlots_injective : Function.Injective loopSlots
  initialStates : Nat
  initialMachine : Machine (tapes (williamsOf sources) (7+(11+a.scratch+extra))) initialStates
  finalStates : Nat
  finalMachine : Machine (tapes (williamsOf sources) (7+(11+a.scratch+extra))) finalStates
  result : Input → Result (tapes (williamsOf sources) (7+(11+a.scratch+extra)))
  rowH : Input → Nat → List Bool → Fin bodyTapes → Nat
  rowA : Input → Nat → List Bool → Fin bodyTapes → List Bool
  descriptor : Fin bodyTapes
  ordinal : Fin bodyTapes
  descriptor_ne_ordinal : descriptor ≠ ordinal
  rowDescriptor : ∀ (i : Input) (j : Nat) (pre : List Bool),
    rowH i j pre descriptor = pre.length ∧ rowA i j pre descriptor = pre
  rowOrdinal : ∀ (i : Input) (j : Nat), j ≤ (result i).ds.length → ∀ pre,
    rowH i j pre ordinal = j+1 ∧ rowA i j pre ordinal =
      ZeroPadding.pad ((result i).ds.length+1) (CompareMachine.word j)
  initialFuel : Input → Nat
  rowFuel : Input → Nat
  finalFuel : Input → Nat

noncomputable def count {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) := (c.result i).ds.length

/-- Each iteration appends a COMPLETE framed descriptor, including all
ReloadCore input fields, rather than only the binary request header. -/
noncomputable def emit {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) (j : Nat) :=
  ((c.result i).ds.map (P1TopDownPaidReusable.Datum.word (williamsOf sources))).getD j []

noncomputable def rowConfig {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) (j : Nat) (pre : List Bool) :
    Configuration c.bodyTapes c.bodyStates :=
  ⟨c.rowMachine.start, c.rowH i j pre, c.rowA i j pre⟩

noncomputable def loopEntry {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) :=
  RepeatMachine.cfg 0 (rowConfig c i 0 []) (count c i) 1

noncomputable def loopExit {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) :=
  RepeatMachine.cfg 3
    (rowConfig c i (count c i) ((List.range (count c i)).flatMap (emit c i))) (count c i) 1

noncomputable def entryH {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) :=
  dockH c.loopSlots (middleH a c.extra i) (loopEntry c i).heads

noncomputable def entryA {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) :=
  install c.loopSlots (middleA a c.extra i) (loopEntry c i).tapes

noncomputable def exitH {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) :=
  dockH c.loopSlots (middleH a c.extra i) (loopExit c i).heads

noncomputable def exitA {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) :=
  install c.loopSlots (middleA a c.extra i) (loopExit c i).tapes

/-- Includes the paid loop control and the terminal driver rewind.
Initialization/finalization and the two sequence ticks are separate below.
No universal asymptotic row-generation estimate is inferred from hmon. -/
noncomputable def loopFuel {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (i : Input) := count c i * (c.rowFuel i+3)+3

noncomputable def code {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) : SuffixCode a :=
  { extra := c.extra
    states := _
    machine := Composition.machine c.initialMachine
      (Composition.machine
        (RecoveryFocus.machine c.loopSlots (CloseoutRowsDegreeLoop.machine c.rowMachine))
        c.finalMachine)
    result := fun i => { c.result i with
      fuel := c.initialFuel i+1+(loopFuel c i+1+c.finalFuel i) } }

/-- Exact consumed component contract, with no arbitrary starting scratch.
Initialization is from the WHOLE accepted preparation endpoint; every row
has a full-bank Step; finalization supplies the SAME result and PrefixReady,
including descriptor rewind, seven drivers, framed denominator and blanks.
The finalizer also handles a zero-row family without invoking the row body. -/
noncomputable def Correct {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) : Prop :=
  ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat),
    Admissible sources a.policy atoms L target recordWidth m →
    let i := inputOf atoms L target recordWidth m true
    CacheReady sources m a.policy a.scratch atoms L target recordWidth (a.result i) →
    Step c.initialMachine (c.initialFuel i)
      (middleH a c.extra i) (middleA a c.extra i) (entryH c i) (entryA c i) ∧
    (∀ j < count c i, ∀ pre,
      Step c.rowMachine (c.rowFuel i) (c.rowH i j pre) (c.rowA i j pre)
        (c.rowH i (j+1) (pre++emit c i j)) (c.rowA i (j+1) (pre++emit c i j))) ∧
    Step c.finalMachine (c.finalFuel i) (exitH c i) (exitA c i)
      (c.result i).H (c.result i).A ∧
    PrefixReady (code c).fixed.code i ∧
    NativeRows sources L target m atoms (williamsOf sources)
      (c.result i).S (c.result i).R (c.result i).B (c.result i).rowWidth
      (c.result i).ds (c.result i).total (c.result i).denominator ∧
    (c.result i).rowWidth ≤ recordWidth ∧ (c.result i).total < 2^recordWidth

noncomputable def suffix {sources : EightSources} {m : Bool} {a : Program sources m}
    (c : Code a) (correct : Correct c) : Suffix a := by
  refine ⟨code c, ?_⟩
  intro q circuit pcpp atoms L target recordWidth hadm i hcache result
  obtain ⟨hin, hrow, hout, hready, hnative, hwidth, htotal⟩ :=
    correct atoms L target recordWidth hadm hcache
  have supplier : ∀ j < count c i, ∀ pre, ∃ r,
      runFrom c.rowMachine (c.rowFuel i) (rowConfig c i j pre) = some r ∧
      r.final.heads = (rowConfig c i (j+1) (pre++emit c i j)).heads ∧
      r.final.tapes = (rowConfig c i (j+1) (pre++emit c i j)).tapes ∧
      r.steps ≤ c.rowFuel i := by
    intro j hj pre
    exact hrow j hj pre
  obtain ⟨r, hr, he, _⟩ := CloseoutRowsDegreeLoop.loop_run c.rowMachine
    (rowConfig c i) (emit c i) (c.rowFuel i) (count c i)
    (by intro j hj pre; rfl) supplier []
  simp only [List.nil_append] at he
  have loop : Step (CloseoutRowsDegreeLoop.machine c.rowMachine) (loopFuel c i)
      (loopEntry c i).heads (loopEntry c i).tapes (loopExit c i).heads (loopExit c i).tapes := by
    exact Step.of_run hr (congrArg Configuration.heads he) (congrArg Configuration.tapes he)
  have focused := loop.focus c.loopSlots c.loopSlots_injective
    (middleH a c.extra i) (middleA a c.extra i)
  exact ⟨hin.seq (focused.seq hout), hready, hnative, hwidth, htotal⟩

abbrev GlobalCode (m : Bool) := (a : GlobalProgram m) → (sources : EightSources) →
  (gamma : Real) → (hg : 0<gamma) → (hh : gamma<1/2) →
  (p : Parameters sources gamma) → Code (a sources gamma hg hh p)

noncomputable def GlobalCorrect {m : Bool} (c : GlobalCode m) : Prop :=
  ∀ (a : GlobalProgram m) (sources : EightSources) (gamma : Real)
    (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma),
    Correct (c a sources gamma hg hh p)

noncomputable def global {m : Bool} (c : GlobalCode m) (hc : GlobalCorrect c) : SuffixBuilder m :=
  fun a sources gamma hg hh p => suffix (c a sources gamma hg hh p)
    (hc a sources gamma hg hh p)

end SymSuffixLoop
