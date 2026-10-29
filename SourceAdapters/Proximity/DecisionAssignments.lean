import SourceAdapters.Proximity.SourceCallee
import SourceAdapters.Proximity.DecisionTable

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": fixed assignments in the exact predicate-table order,
and their restriction to the actual source query count. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecisionAssignments

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Proximity

def assignment {q : ℕ} (code : Fin (2 ^ q)) : BitInput q := fun i => code.val.testBit i.val

def inputs (q : ℕ) : List (List Bool) := List.ofFn fun code : Fin (2 ^ q) => List.ofFn (assignment code)

def rows {q : ℕ} (predicate : BitInput q → Bool) : List (List Bool × Bool) :=
  List.ofFn fun code : Fin (2 ^ q) => (List.ofFn (assignment code), predicate (assignment code))

theorem rows_inputs {q : ℕ} (predicate : BitInput q → Bool) :
    (rows predicate).map Prod.fst = inputs q := by
  simp only [rows, inputs, List.map_ofFn]
  rfl

theorem rows_values {q : ℕ} (predicate : BitInput q → Bool) :
    DecisionTable.values (rows predicate) = (List.ofFn (predicateTable predicate)).map Bool.toNat := by
  simp only [DecisionTable.values, rows, List.map_ofFn]
  rfl

@[simp] theorem rows_length {q : ℕ} (predicate : BitInput q → Bool) : (rows predicate).length = 2 ^ q := by
  simp [rows]

theorem row_width {q : ℕ} (predicate : BitInput q → Bool) (r : List Bool × Bool) (hr : r ∈ rows predicate) :
    r.1.length = q := by
  obtain ⟨code, rfl⟩ := List.mem_ofFn.mp hr
  simp

theorem take_assignment {q N : ℕ} (h : N ≤ q) (bits : BitInput q) :
    (List.ofFn bits).take N = List.ofFn (fun i : Fin N => bits (Fin.castLE h i)) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

theorem source_decision_input {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits)) (bits : BitInput q) :
    proofCallInput V (SourceCallee.decisionRequest V ⟨S, coins,
        fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩) =
      DecisionCalls.decisionTag ++ sourceCircuitWord S ++ frame coins.val.bits ++
        (List.ofFn bits).take ((V S).queryCount coins) := by
  rw [SourceCallee.decision_input, take_assignment ((V S).queryCount_le coins)]
  rfl

theorem source_decision_output {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits)) (bits : BitInput q) :
    normalizedProofOutput V proofLength honest (SourceCallee.decisionRequest V ⟨S, coins,
        fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩) = [rowPredicate (V S) coins bits] := rfl

end NearCubicGates.Adapters.Proximity.DecisionAssignments
