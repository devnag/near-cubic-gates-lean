import SourceAdapters.Compile.BoundedInitial
import SourceAdapters.Compile.CircuitToCNF

/-!
proof of `lem:multitape-refuter`: a concrete circuit for bounded ordinary-verifier acceptance,
then the proved native exact-three-CNF tail. The prefix rank restriction and
single ordinary code-to-layout generator are separate constructions.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def acceptanceExpression {t s width : ℕ} (machine : Machine t s) (accepting : Fin s → Bool) :
    BoolExpr (windowBits t s width) :=
  anyExpression (List.ofFn (fun state : Fin s =>
    .and (.input (controlIndex state)) (.const (machine.halted state && accepting state))))

@[simp] theorem acceptanceExpression_eval {t s width : ℕ} (machine : Machine t s)
    (accepting : Fin s → Bool) (a : MachineWindow t s width) :
    (acceptanceExpression machine accepting).eval a.encode =
      (machine.halted a.control && accepting a.control) := by
  apply Bool.eq_iff_iff.mpr
  simp only [acceptanceExpression, anyExpression_true, List.mem_ofFn,
    exists_exists_eq_and, BoolExpr.eval, MachineWindow.encode_control,
    Bool.and_eq_true, decide_eq_true_eq]
  simp

@[simp] theorem acceptanceExpression_dead {t s width : ℕ} (machine : Machine t s)
    (accepting : Fin s → Bool) :
    (@acceptanceExpression t s width machine accepting).eval (fun _ => false) = false := by
  apply Bool.eq_false_iff.mpr
  simp [acceptanceExpression, BoolExpr.eval]

theorem acceptanceExpression_operations {t s width : ℕ} (machine : Machine t s)
    (accepting : Fin s → Bool) :
    expressionOperations (@acceptanceExpression t s width machine accepting) ≤ 3*s+1 := by
  unfold acceptanceExpression
  have h := anyExpression_operations
    (List.ofFn (fun state : Fin s =>
      BoolExpr.and (.input (@controlIndex t s width state))
        (.const (machine.halted state && accepting state)))) 2 (by
      intro e he
      obtain ⟨state, rfl⟩ := List.mem_ofFn.mp he
      rfl)
  simpa [Nat.mul_comm] using h

def verifierInitialValues (v : Verifier) (input : List Bool) (n fuel : ℕ) :=
  compileExternalVector (BooleanDAGBuilder.empty n)
    (windowBits v.tapeCount v.stateCount (fuel+1)) (verifierInitialExpression v input n fuel)

def verifierRoundValues (v : Verifier) (input : List Bool) (n fuel : ℕ) :=
  let initial := verifierInitialValues v input n fuel
  compileTransitionRounds v.machine initial.final initial.live fuel

def verifierVerdictWire (v : Verifier) (input : List Bool) (n fuel : ℕ) :=
  let rounds := verifierRoundValues v input n fuel
  compileOnWires rounds.final rounds.live (acceptanceExpression v.machine v.accepting)

/-- Fully explicit bounded acceptance circuit, with every emitted node counted. -/
def verifierCircuit (v : Verifier) (input : List Bool) (n fuel : ℕ) : BooleanCircuit n :=
  let verdict := verifierVerdictWire v input n fuel
  verdict.final.finish verdict.output

theorem verifierCircuit_eval (v : Verifier) (input : List Bool) {n : ℕ}
    (witness : BitInput n) (fuel : ℕ) :
    (verifierCircuit v input n fuel).eval witness =
      (verifierInitialWindow v input witness fuel).accepted v.machine v.accepting fuel := by
  rw [verifierCircuit, BooleanDAGBuilder.finish_eval, (verifierVerdictWire v input n fuel).correct]
  change (acceptanceExpression v.machine v.accepting).eval
    (transitionRounds v.machine fuel (fun i => (verifierInitialExpression v input n fuel i).eval witness)) = _
  simp only [verifierInitialExpression_eval]
  rw [transitionRounds_correct]
  cases hr : (verifierInitialWindow v input witness fuel).rounds v.machine fuel <;>
    simp [encodeWindowOption, MachineWindow.accepted, hr]

/-- proof of `lem:multitape-refuter`: exact real-machine semantics, without a compiler premise. -/
theorem verifierCircuit_correct (v : Verifier) (input : List Bool) {n : ℕ}
    (witness : BitInput n) (fuel : ℕ) :
    (verifierCircuit v input n fuel).eval witness = true ↔
      v.acceptsAt fuel input (List.ofFn witness) := by
  rw [verifierCircuit_eval, verifierInitialWindow_accepted]

/-- proof of `lem:multitape-refuter`: explicit finite table, window and clock node count. -/
theorem verifierCircuit_size (v : Verifier) (input : List Bool) (n fuel : ℕ) :
    (verifierCircuit v input n fuel).size ≤
      windowBits v.tapeCount v.stateCount (fuel+1) *
        (1 + fuel * transitionBitBound v.tapeCount v.stateCount (fuel+1)) + 3*v.stateCount+1 := by
  let initial := verifierInitialValues v input n fuel
  let rounds := verifierRoundValues v input n fuel
  let verdict := verifierVerdictWire v input n fuel
  have hi := compileExternalVector_added_le
    (windowBits v.tapeCount v.stateCount (fuel+1)) (BooleanDAGBuilder.empty n)
    (verifierInitialExpression v input n fuel) 1 (by intro i; simp)
  have hr := compileTransitionRounds_polynomial v.machine fuel initial.final initial.live
  have hv := acceptanceExpression_operations (width := fuel+1) v.machine v.accepting
  have hiel := initial.extension.length_eq
  have hrel := rounds.extension.length_eq
  have hvel := verdict.extension.length_eq
  have hvops : verdict.extension.suffix.length =
      expressionOperations (@acceptanceExpression v.tapeCount v.stateCount (fuel+1) v.machine v.accepting) :=
    compileOnWires_added _ _ _
  change initial.extension.suffix.length ≤ _ at hi
  change rounds.extension.suffix.length ≤ _ at hr
  simp only [BooleanDAGBuilder.empty, List.length_nil, zero_add] at hiel
  change verdict.final.nodes.length ≤ _
  nlinarith

/-- Full witness-range sourceSAT semantics; the [0,high) filter is added next. -/
theorem verifierCircuit_sourceSAT (v : Verifier) (input : List Bool) (n fuel : ℕ) :
    NearCubicWires.RepairSource.RecoveryOracle.sourceSAT
      (circuitSATCode (verifierCircuit v input n fuel)) = true ↔
      ∃ witness : BitInput n, v.acceptsAt fuel input (List.ofFn witness) := by
  rw [circuitSATCode_correct]
  exact exists_congr (fun witness => verifierCircuit_correct v input witness fuel)

end NearCubicGates.Adapters.Compile
