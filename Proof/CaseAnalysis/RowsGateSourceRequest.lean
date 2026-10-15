import Proof.CaseAnalysis.RowsGateSourceRun
import Proof.CaseAnalysis.RawRowsChildLog

/-! The retained-top formula depends only on its supported gate. This
local abbreviation lets the all-raw source caller handle every accepted
gate; on an actual top it is definitionally the original retainedTopGate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces CanonicalBinary CanonicalWitnessCodec
open SupplierPipeline RadixSemantics CompilerSemantics CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compressedGate {n : ℕ} (g : SupportedNormalizedGate n) : NormalizedThresholdGate g.support.card where
  weight i := g.gate.weight (g.support.orderEmbOfFin rfl i)
  threshold := g.gate.threshold
def request {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) : ExactDecompositionRequest :=
  if compressed then ⟨g.support.card,nonStrictAsStrict (compressedGate g)⟩ else ⟨n,nonStrictAsStrict g.gate⟩

theorem retained_request {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) :
    request true c.top=⟨c.top.support.card,nonStrictAsStrict (retainedTopGate c)⟩ := rfl

theorem compressed_weights {n : ℕ} (g : SupportedNormalizedGate n) :
    CloseoutRowsGateNative.weights true (gateFields g.gate) (gateMembers g.support)=
      (List.ofFn (compressedGate g).weight).flatMap intWord := by
  unfold CloseoutRowsGateNative.weights
  rw [show (gateFields g.gate).length=n by simp [gateFields],gate_emission,selected_filter,sorted_members]
  rw [←Finset.listMap_orderEmbOfFin_finRange g.support rfl]
  simp only [List.flatMap_map,List.ofFn_eq_map,compressedGate]

theorem request_word {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (source : List Bool)
    (hs : readTapeBit source 1=decide (g.gate.threshold<0)) :
    CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support) source g.gate.threshold.natAbs=
      thresholdWord (request compressed g).gate := by
  cases compressed with
  | false => exact CloseoutRowsGateNative.ordinary_word g source hs
  | true =>
    change natWord (CloseoutRowsSupportCount.ones (gateMembers g.support))++
      CloseoutRowsGateNative.weights true (gateFields g.gate) (gateMembers g.support)++
      CloseoutRowsStrictNative.produced source g.gate.threshold.natAbs=_
    rw [CloseoutRowsSupportCount.support_card,compressed_weights,
      CloseoutRowsStrictNative.produced_eq source g.gate.threshold hs]
    rfl

theorem gate_parameter {n : ℕ} (g : NormalizedThresholdGate n) (B : ℕ)
    (hn : n≤B+1) (ht : intBitLength g.threshold≤B+2) (hw : ∀ i,intBitLength (g.weight i)≤B+2) :
    n+(nonStrictAsStrict g).encodingBits+1≤(B+3)^2 := by
  have hs := RepairSource.CloseoutRawRows.strict_gate_bits g
  have sum : (∑ i,intBitLength (g.weight i))≤n*(B+2) := by
    calc (∑ i,intBitLength (g.weight i))≤∑ _ : Fin n,(B+2) := Finset.sum_le_sum (fun i _ => hw i)
         _ = n*(B+2) := by simp
  have mul := Nat.mul_le_mul_right (B+2) hn
  have hgate : g.encodingBits≤B+2+n*(B+2) := by
    unfold NormalizedThresholdGate.encodingBits
    omega
  nlinarith

theorem request_parameter {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) :
    (request compressed g).arity+(request compressed g).gate.encodingBits+1≤(bits.length+3)^2 := by
  have hc := CloseoutRowsGateGuard.typed_components g bits h
  have hn : n≤bits.length+1 := by
    simpa only [CloseoutRowsGateFields.field_length,List.length_ofFn] using
      CloseoutRowsGateRawBounds.list_count _ _ hc.2.1
  have ht : intBitLength g.gate.threshold≤bits.length+2 := by
    have bits := CloseoutRowsGateRawBounds.integer_bits _ _ hc.2.2.1
    rw [CloseoutRowsGateFields.field_length] at bits
    have value := PCPSerializerMass.value_width g.gate.threshold.natAbs.bits
    rw [CanonicalPositiveOutput.nat_bits_value] at value
    change natBitLength g.gate.threshold.natAbs≤_
    omega
  have hw : ∀ i,intBitLength (g.gate.weight i)≤bits.length+2 := by
    intro i
    have bounds := CloseoutRowsGateRawBounds.list_bits _ _ hc.2.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    rw [CloseoutRowsGateFields.field_length] at bounds
    have value := PCPSerializerMass.value_width (g.gate.weight i).natAbs.bits
    rw [CanonicalPositiveOutput.nat_bits_value] at value
    change natBitLength (g.gate.weight i).natAbs≤_
    omega
  cases compressed with
  | false => exact gate_parameter g.gate bits.length hn ht hw
  | true =>
    have hcard : g.support.card≤n := (Finset.card_le_univ _).trans (by simp)
    exact gate_parameter (compressedGate g) bits.length (hcard.trans hn) ht (fun i => hw _)

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
