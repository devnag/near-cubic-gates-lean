import Proof.CaseAnalysis.RecoveryRowAddressRewind
import Proof.Amplification.RecoveryPCPFormulaResumeRowReusable

/-! The framed source projector and raw original-graph query consumer
name exactly the same addresses. The adapter uses the existing quadratic C. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit RepairSource RepairSource.ProjectionNormalization
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_original (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) :
    RecoveryProjectionRows.addressFields p R Q hr hq x randomness=
      (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness).map List.ofFn := by
  simp only [RecoveryProjectionRows.addressFields,projectedAddresses,List.map_ofFn]
  rfl

theorem flattened_original (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) :
    (RecoveryProjectionRows.addressFields p R Q hr hq x randomness).flatten=
      RecoveryBoundedQueries.addressWord (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness) := by
  rw [fields_original]
  rfl

theorem source_budget (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) (W : ℕ) (hR : R ≤ W) (hQ : Q ≤ W) :
    budget (RecoveryProjectionRows.addressFields p R Q hr hq x randomness) ≤ capacity W := by
  let fields:=RecoveryProjectionRows.addressFields p R Q hr hq x randomness
  have hlen : fields.length=Q:=by simp only [fields,RecoveryProjectionRows.addressFields,List.length_ofFn]
  have hw : ∀ field∈fields,field.length=R := by
    intro field hf
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hf
    exact List.length_ofFn
  have hs:=RecoveryPCPFormulaResumeRowReusable.stream_length fields R hw
  change (FieldList.stream fields).length+3*fields.length+3 ≤ capacity W
  rw [hs,hlen]
  have hm:=Nat.mul_le_mul hQ hR
  unfold capacity
  nlinarith [Nat.zero_le (W^2)]

theorem original_output (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) (tail : List Bool) (L : ℕ) :
    output (RecoveryProjectionRows.addressFields p R Q hr hq x randomness) tail L=
      (![FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)++tail,
        RecoveryBoundedQueries.addressWord (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness),
        VerifierDecoding.CompareMachine.word Q,List.replicate L false] : Fin 4→List Bool) := by
  funext i
  fin_cases i
  · rfl
  · exact flattened_original p R Q hr hq x randomness
  · change VerifierDecoding.CompareMachine.word (RecoveryProjectionRows.addressFields p R Q hr hq x randomness).length=
      VerifierDecoding.CompareMachine.word Q
    simp only [RecoveryProjectionRows.addressFields,List.length_ofFn]
  · rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
