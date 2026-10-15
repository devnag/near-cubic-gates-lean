import Proof.Hierarchy.CompetitorWitnessHeaderTyped
import Proof.Amplification.RecoveryWitnessPolicy

/-! Paper C.10's one-sum-per-variable payload. The outer three-field grammar
is retained; its last field is a balanced list in the actual source's variable
order. The old single-sum witness codec is not reinterpreted. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open CanonicalBinary CanonicalWitnessCodec SupplierPipeline RecoveryWitnessPolicy ExecutableInterfaces
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure SumFamily (Circuit : SupplierPipeline.CircuitFamily)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits) (variableCount : ℕ) where
  sums : List (CheckedLegalCircuitSum Circuit wires description limits)
  length_eq : sums.length = variableCount

namespace SumFamily
variable {Circuit : SupplierPipeline.CircuitFamily} {wires description : {n : ℕ} → Circuit n → ℕ}
  {limits : LegalSumLimits} {variableCount : ℕ}

def getSum (family : SumFamily Circuit wires description limits variableCount) (i : Fin variableCount) :=
  family.sums.get (Fin.cast family.length_eq.symm i)

def code (codec : CanonicalCircuitCodec Circuit)
    (family : SumFamily Circuit wires description limits variableCount) : ℕ :=
  encodeBalancedList (family.sums.map (·.code codec))

private def decodeSums (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ} → Circuit n → ℕ) (limits : LegalSumLimits) :
    List ℕ → Option (List (CheckedLegalCircuitSum Circuit wires description limits))
  | [] => some []
  | c :: cs => do
      let s ← decodeLegalCircuitSum codec wires description limits c
      let ss ← decodeSums codec wires description limits cs
      pure (s :: ss)

private theorem decodeSums_encode (codec : CanonicalCircuitCodec Circuit)
    (ss : List (CheckedLegalCircuitSum Circuit wires description limits)) :
    decodeSums codec wires description limits (ss.map (·.code codec)) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp [decodeSums, decodeLegalCircuitSum_encode, ih]

def decode (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits) (variableCount code : ℕ) :
    Option (SumFamily Circuit wires description limits variableCount) := do
  let cs ← decodeBalancedList code
  let ss ← decodeSums codec wires description limits cs
  if h : ss.length = variableCount then
    let family : SumFamily Circuit wires description limits variableCount := ⟨ss, h⟩
    if family.code codec = code then some family else none
  else none

theorem decode_encode (codec : CanonicalCircuitCodec Circuit)
    (family : SumFamily Circuit wires description limits variableCount) :
    decode codec wires description limits variableCount (family.code codec) = some family := by
  cases family with
  | mk ss h =>
    simp [decode, code, decodeBalancedList_encode, decodeSums_encode, h]

theorem code_of_decode (codec : CanonicalCircuitCodec Circuit) {raw : ℕ}
    {family : SumFamily Circuit wires description limits variableCount}
    (h : decode codec wires description limits variableCount raw = some family) :
    family.code codec = raw := by
  unfold decode at h
  cases hc : decodeBalancedList raw with
  | none => simp [hc] at h
  | some cs =>
    simp only [hc, bind, Option.bind] at h
    cases hs : decodeSums codec wires description limits cs with
    | none => simp [hs] at h
    | some ss =>
      simp only [hs] at h
      split at h
      · split at h
        · rename_i hcode
          cases Option.some.inj h
          exact hcode
        · simp at h
      · simp at h

theorem code_bits (codec : CanonicalCircuitCodec Circuit)
    (family : SumFamily Circuit wires description limits variableCount) (bits : ℕ)
    (h : ∀ s ∈ family.sums, natBitLength (s.code codec) ≤ bits) :
    natBitLength (family.code codec) ≤ 1 + 2 * variableCount ^ 4 * (variableCount * bits + 1) := by
  apply encodeBalancedList_bits_le_of_bounds _ variableCount bits
  · simp only [List.length_map, family.length_eq, le_refl]
  · intro c hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact h s hs

noncomputable def value (eval : {n : ℕ} → Circuit n → BitInput n → Bool)
    (family : SumFamily Circuit wires description limits variableCount)
    (u : BitInput limits.expectedArity) (i : Fin variableCount) : ℝ :=
  ((family.getSum i).value.terms.map fun term => (term.coefficient : ℝ) *
    (if eval term.circuit (fun j => u (Fin.cast (family.getSum i).arity_eq j)) then 1 else 0)).sum

end SumFamily

inductive FamilyWitness (limits : RecoveryWitnessLimits)
    (variableCount : BooleanCircuit limits.oracleArity → ℕ)
  | symmetric (oracle : BooleanCircuit limits.oracleArity)
      (oracleSize_le : oracle.size ≤ limits.oracleSizeCap)
      (sums : SumFamily NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits limits.symmetric (variableCount oracle))
  | threshold (oracle : BooleanCircuit limits.oracleArity)
      (oracleSize_le : oracle.size ≤ limits.oracleSizeCap)
      (sums : SumFamily NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits limits.threshold (variableCount oracle))

namespace FamilyWitness
variable {limits : RecoveryWitnessLimits} {variableCount : BooleanCircuit limits.oracleArity → ℕ}

def oracle : FamilyWitness limits variableCount → BooleanCircuit limits.oracleArity
  | .symmetric c _ _ => c
  | .threshold c _ _ => c
def mode : FamilyWitness limits variableCount → ℕ
  | .symmetric _ _ _ => 0
  | .threshold _ _ _ => 1
def payload : FamilyWitness limits variableCount → ℕ
  | .symmetric _ _ ss => ss.code symmetricCircuitCodec
  | .threshold _ _ ss => ss.code thresholdCircuitCodec
def code (w : FamilyWitness limits variableCount) : ℕ :=
  encodeTaggedList [encodeNat w.mode, encodeBooleanCircuit w.oracle, w.payload]

theorem header_fields (w : FamilyWitness limits variableCount) (bits : List Bool)
    (h : value bits = w.code) :
    CompetitorWitnessTriple.headerValid bits ∧
    CompetitorWitnessTriple.field bits 3 = encodeBooleanCircuit w.oracle ∧
    CompetitorWitnessTriple.field bits 5 = w.payload := by
  obtain ⟨hstruct, hm, ho, hp⟩ := CompetitorWitnessTriple.extracted_values bits _ _ _ h
  refine ⟨⟨hstruct, ?_⟩, ho, hp⟩
  rw [hm]
  cases w <;> simp [mode, CompetitorWitnessTriple.encoded_modes]

theorem code_bits (w : FamilyWitness limits variableCount) (oracleBits payloadBits : ℕ)
    (ho : natBitLength (encodeBooleanCircuit w.oracle) ≤ oracleBits)
    (hp : natBitLength w.payload ≤ payloadBits) :
    natBitLength w.code ≤ taggedListBitBound [2, oracleBits, payloadBits] := by
  apply encodeTaggedList_three_bits_le _ ho hp
  cases w with
  | symmetric _ _ _ =>
    change natBitLength (encodeNat 0) ≤ 2
    rw [CompetitorWitnessTriple.encoded_modes.1]
    norm_num [natBitLength]
  | threshold _ _ _ =>
    change natBitLength (encodeNat 1) ≤ 2
    rw [CompetitorWitnessTriple.encoded_modes.2]
    norm_num [natBitLength]

end FamilyWitness

end NearCubicWires.RepairOrdinary.CloseoutWitness
