import SourceAdapters.Proximity.Trimming
import Proof.Foundations.OrdinaryStreaming

/-!
Model nonvacuity for CW19 Definition 20 / Lemma 24; `app:sources`, "Uniform three-query PCPP and code interfaces".
A one-input one-gate circuit has both an accepted and a rejected input. Its
verifier reads the input without a proof. A separate verifier checks that
arbitrarily large, repeated proof addresses trim to a single coordinate.
These are model examples, not a proof of the published uniform family leaf.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity.Vacuity

open NearCubicWires
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP

def oneGate : BooleanCircuit 1 where
  nodes := [.input 0]
  output := ⟨0, by simp⟩
  wellFormed := by intro i; simp [BooleanNode.WellFormedAt]

theorem oneGate_eval (input : BitInput 1) : oneGate.eval input = input 0 := rfl

def oneGateSource : SourceCircuit where
  arity := 1
  circuit := oneGate
  inputs_le_size := by decide

theorem oneGate_source_accepts : oneGateSource.circuit.eval (fun _ => true) = true := rfl

theorem oneGate_source_rejects : oneGateSource.circuit.eval (fun _ => false) = false := rfl

/-- The chosen source framing has its actual linear size, including the terminator. -/
theorem source_frame_length (word : List Bool) :
    (RepairOrdinary.frame word).length = 2 * word.length + 1 :=
  RepairOrdinary.frame_length word

/-- Actual source-model programs read and write arbitrary words, with a paid
linear bound. The word is not interpreted as an integer, so trailing zeros remain. -/
theorem ordinary_copy :
    Nonempty (RepairOrdinary.WordFunction (List Bool) id id (fun word => 4 * word.length + 2)) :=
  ⟨RepairOrdinary.Streaming.rewoundIdentityCopy.toWordFunction⟩

theorem source_poly_copy : SourcePolyTime (id : List Bool → List Bool) id := by
  refine ⟨4, 1, ⟨RepairOrdinary.Streaming.rewoundIdentityCopy.toWordFunction.enlargeBudget ?_⟩⟩
  intro word
  simp only [id_eq, pow_one]
  omega

theorem copy_trailing_zero :
    ∃ receipt,
      LocalBitMultitape.run RepairOrdinary.Streaming.copyProgram.machine 14
        (RepairOrdinary.Streaming.copyProgram.inputTapes [true, false, false]) = some receipt ∧
      receipt.final.tapes RepairOrdinary.Streaming.copyProgram.outputTape = [true, false, false] :=
  RepairOrdinary.Streaming.rewoundIdentityCopy.realizes [true, false, false]

def oneQuery : NonadaptiveVerifier 1 1 where
  randomBits := 0
  queryCount := fun _ => 1
  queryCount_le := fun _ => le_rfl
  query := fun _ _ => .inl 0
  decision := fun _ answers => answers 0

theorem oneQuery_eval (input : BitInput 1) (proof : ℕ → Bool) :
    oneQuery.accepts input proof 0 = oneGate.eval input := rfl

def repeatedInput : ThreeQueryVerifier 1 where
  randomBits := 0
  clause := fun _ _ => ⟨.inl 0, false⟩

theorem repeatedInput_eval (input : BitInput 1) (proof : ℕ → Bool)
    (coins : Fin (2 ^ repeatedInput.randomBits)) :
    repeatedInput.accepts input proof coins = oneGate.eval input := by
  simp [ThreeQueryVerifier.accepts, repeatedInput, SignedQuery.eval,
    oracleValue, List.ofFn_succ, oneGate_eval]

theorem oneGate_complete :
    ∀ coins, repeatedInput.accepts (fun _ => true) (fun _ => false) coins = true := by
  intro coins
  rw [repeatedInput_eval]
  rfl

theorem oneGate_rejects :
    ∀ proof coins, repeatedInput.accepts (fun _ => false) proof coins = false := by
  intro proof coins
  rw [repeatedInput_eval]
  rfl

theorem inputOnly_empty : usedProofAddresses repeatedInput = ∅ := by
  ext address
  simp [usedProofAddresses, proofAddressSet, repeatedInput]

theorem inputOnly_zero_proof : (trimVerifier repeatedInput).proofBits = 0 := by
  simp [trimVerifier, inputOnly_empty]

def repeatedProof (address : ℕ) : ThreeQueryVerifier 0 where
  randomBits := 0
  clause := fun _ _ => ⟨.inr address, false⟩

theorem repeatedProof_singleton (address : ℕ) :
    usedProofAddresses (repeatedProof address) = {address} := by
  ext a
  simp [usedProofAddresses, proofAddressSet, repeatedProof]

theorem repeatedProof_one (address : ℕ) :
    (trimVerifier (repeatedProof address)).proofBits = 1 := by
  simp [trimVerifier, repeatedProof_singleton]

theorem repeatedProof_eval (address : ℕ) (proof : ℕ → Bool)
    (coins : Fin (2 ^ (repeatedProof address).randomBits)) :
    (repeatedProof address).accepts Fin.elim0 proof coins = proof address := by
  simp [ThreeQueryVerifier.accepts, repeatedProof, SignedQuery.eval,
    oracleValue, List.ofFn_succ]

end NearCubicGates.Adapters.Proximity.Vacuity
