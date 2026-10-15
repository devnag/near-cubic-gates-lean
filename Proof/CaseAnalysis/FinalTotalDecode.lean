import Proof.CaseAnalysis.FinalTailVerdictUniform
import Proof.CaseAnalysis.FinalResidualLeaves
import Proof.CaseAnalysis.FinalDecidesBridge

/-! Paper A.8: "Systematic code coordinates are compiled as native parity atoms,
so no half-arity supplier call is required." The systematic constructor evaluates
definitionally to that parity. Paper C.10 guesses the oracle and one circuit sum
per proof coordinate; the decoded families below have exactly the policies in
`SymDecidesFrom` and `ThrDecidesFrom`, at C.10.2's delta = zeta. Empty sums supply
total defaults without assuming decoding succeeds. Successful decoding pins the
actual value used by the verdict. Cap 1 is the frozen Machine consumer's cap. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

inductive Atom {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
  | systematic (index : Fin pcpp.systematicBits)
  | symmetric (atom : NormalizedSymmetricThresholdCircuit n)
  | threshold (atom : NormalizedThresholdThresholdCircuit n)

def evaluate {n : ℕ} {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit} :
    Atom pcpp → BitInput n → Bool
  | .systematic index, input => parityOn (pcpp.systematicSupport index) input
  | .symmetric atom, input => atom.eval input
  | .threshold atom, input => atom.eval input

theorem hsystematic_rfl {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit) :
    ∀ index input, evaluate (Atom.systematic (pcpp := pcpp) index) input =
      parityOn (pcpp.systematicSupport index) input := fun _ _ => rfl

def trivialCircuit (n : ℕ) : BooleanCircuit n where
  nodes := [.const false]
  output := ⟨0, by simp⟩
  wellFormed := by intro i; fin_cases i; trivial

def emptySum {Circuit : SupplierPipeline.CircuitFamily}
    (wires description : {n : ℕ} → Circuit n → ℕ) (limits : LegalSumLimits)
    (hmass : 0 ≤ limits.coefficientMassCap) : CheckedLegalCircuitSum Circuit wires description limits where
  value := ⟨limits.expectedArity, []⟩
  arity_eq := rfl
  terms_le := Nat.zero_le _
  coefficient_bits_le := by intro term ht; cases ht
  mass_le := hmass
  wires_le := by intro term ht; cases ht
  description_le := by intro term ht; cases ht

def trivialFamily {Circuit : SupplierPipeline.CircuitFamily}
    (wires description : {n : ℕ} → Circuit n → ℕ) (limits : LegalSumLimits)
    (hmass : 0 ≤ limits.coefficientMassCap) (count : ℕ) :
    SumFamily Circuit wires description limits count :=
  ⟨List.replicate count (emptySum wires description limits hmass), List.length_replicate⟩

variable (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2)))

def oracleOf (oracleDegree n : ℕ) (bits : List Bool) :
    BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n) :=
  let decoded : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n) :=
    (decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)
      (RadixSemantics.value (BoundedFields.oracle bits))).getD (trivialCircuit _)
  if decoded.size ≤ oracleSizeBound oracleDegree
      ((outer sources k clock).result.pcp.nativeWidth n) then decoded else trivialCircuit _

theorem oracleOf_pin (oracleDegree n : ℕ) (bits : List Bool)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
    (h : decodeBooleanCircuit _ (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle)
    (hsize : oracle.size ≤ oracleSizeBound oracleDegree
      ((outer sources k clock).result.pcp.nativeWidth n)) :
    oracleOf sources k clock oracleDegree n bits = oracle := by simp [oracleOf, h, hsize]

variable {gamma : ℝ} (p : Parameters sources gamma)

abbrev symLimits {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
    (CloseoutWitnessPolicy.request sources k clock x oracle)
    (clauseWidth p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n))
    p.copies ⌊wireScale 1 5 ((outer sources k clock).result.pcp.nativeWidth n)⌋₊
    (zeta (constantsOf sources))

abbrev thrLimits {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
    (CloseoutWitnessPolicy.request sources k clock x oracle)
    (clauseWidth p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n))
    p.copies ⌊wireScale 1 9 ((outer sources k clock).result.pcp.nativeWidth n)⌋₊
    (zeta (constantsOf sources))

abbrev SymFamily {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  SumFamily NormalizedSymmetricThresholdCircuit NormalizedSymmetricThresholdCircuit.wireCount
    NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)

abbrev ThrFamily {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  SumFamily NormalizedThresholdThresholdCircuit NormalizedThresholdThresholdCircuit.wireCount
    NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)

variable {n : ℕ} (x : BitInput n)
  (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)

def symFamilyOf : SymFamily sources k clock p x oracle :=
  (SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
    NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
    (RadixSemantics.value (BoundedFields.family bits))).getD
      (trivialFamily _ _ _ (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies) _)

theorem symFamilyOf_pin (family : SymFamily sources k clock p x oracle)
    (h : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    symFamilyOf sources k clock p x oracle bits = family := by simp [symFamilyOf, h]

def thrFamilyOf : ThrFamily sources k clock p x oracle :=
  (SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
    NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
    (RadixSemantics.value (BoundedFields.family bits))).getD
      (trivialFamily _ _ _ (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies) _)

theorem thrFamilyOf_pin (family : ThrFamily sources k clock p x oracle)
    (h : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    thrFamilyOf sources k clock p x oracle bits = family := by simp [thrFamilyOf, h]

def proofValueOf : BitInput (CloseoutWitnessPolicy.request sources k clock x oracle).arity →
    Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle) → ℝ :=
  if BoundedFields.symmetric bits then
    SumFamily.value NormalizedSymmetricThresholdCircuit.eval (symFamilyOf sources k clock p x oracle bits)
  else
    SumFamily.value NormalizedThresholdThresholdCircuit.eval (thrFamilyOf sources k clock p x oracle bits)

theorem proofValueOf_sym (family : SymFamily sources k clock p x oracle)
    (hs : BoundedFields.symmetric bits = true)
    (h : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    proofValueOf sources k clock p x oracle bits =
      SumFamily.value NormalizedSymmetricThresholdCircuit.eval family := by
  simp [proofValueOf, hs, symFamilyOf_pin sources k clock p x oracle bits family h]

theorem proofValueOf_thr (family : ThrFamily sources k clock p x oracle)
    (hs : BoundedFields.symmetric bits = false)
    (h : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    proofValueOf sources k clock p x oracle bits =
      SumFamily.value NormalizedThresholdThresholdCircuit.eval family := by
  simp [proofValueOf, hs, thrFamilyOf_pin sources k clock p x oracle bits family h]

end
end NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
