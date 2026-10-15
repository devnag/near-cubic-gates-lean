import Proof.Hierarchy.HierarchyProjectionBounds
import Proof.MachineModel.UWholeLanguage
import Proof.PCP.ProjectionRealization

/-! The actual padded hierarchy word is consumed by the realized fixed U.
The normalized-PCP assembler now needs only its actual local constructor
and a common coefficient large enough for the proved numerical bounds. -/
namespace NearCubicWires.RepairSource.HierarchyEncode
open LocalBitMultitape RepairOrdinary VerifierEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem language {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    H.verifier.language H.time r.1 r.2 ↔
      UWhole.verifier.language UWhole.time (encode H Cpad r).1 (encode H Cpad r).2 :=
  (encoded_source_language H Cpad hcoeff hpad r).trans (UWhole.language_iff _ _).symm

theorem producer_language {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (n : ℕ) (x : BitInput n) :
    ∃ r,run (HierarchyReduction.machine k H.coefficient Cpad (code H.verifier))
      (HierarchyReduction.ordinaryBudget k H.coefficient Cpad (code H.verifier) (List.ofFn x))
      (HierarchyReduction.input k (List.ofFn x))=some r ∧
      r.final.tapes (HierarchyReduction.extra k 13)=List.ofFn (encode H Cpad ⟨n,x⟩).2 ∧
      r.final.tapes (HierarchyReduction.xTape k)=frame (List.ofFn x) ∧
      (∀ i,r.final.heads i=0) ∧
      r.steps ≤ HierarchyReduction.ordinaryBudget k H.coefficient Cpad (code H.verifier) (List.ofFn x) ∧
      (H.verifier.language H.time n x ↔
        UWhole.verifier.language UWhole.time (encode H Cpad ⟨n,x⟩).1 (encode H Cpad ⟨n,x⟩).2) := by
  obtain ⟨r,hr,ho,hx,hh,hs⟩ := HierarchyReduction.ordinary_run k H.coefficient Cpad
    (code H.verifier) (List.ofFn x) hpad
  refine ⟨r,hr,?_,hx,hh,hs,language H Cpad hcoeff hpad ⟨n,x⟩⟩
  rw [encode_word H Cpad hpad]
  exact ho

noncomputable def normalizedRun
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (inputExponent coefficient logExponent : ℕ) (hpositive : 0 < coefficient)
    (hproof : HierarchyProjection.proofCoefficient source H Cpad ≤ coefficient)
    (hquery : source.coefficient ≤ coefficient)
    (constructor : OrdinaryWordFunction InputRequest
      (fun r => frame (List.ofFn r.2) ++ frame (H.time r.1).bits)
      (fun r => pcpWord (normalizedSourcePCP source H (encode H Cpad)
        (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
        (HierarchyProjection.width_fits source H Cpad hpad)
        (HierarchyProjection.queries_fit source H Cpad hpad)) r.2)
      (fun r => coefficient*(r.1+1)^inputExponent*(natBitLength (H.time r.1)+1)^logExponent)) :
    NormalizedPCPRun source H (encode H Cpad)
      (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
      (HierarchyProjection.width_fits source H Cpad hpad)
      (HierarchyProjection.queries_fit source H Cpad hpad) inputExponent where
  coefficient := coefficient
  coefficientPositive := hpositive
  logTimeExponent := logExponent
  queryExponent := source.degrees.queries
  proofExponent := 5+source.degrees.proofLog
  length := encode_length H Cpad hpad
  language := language H Cpad hcoeff hpad
  proofBound := by
    intro n _
    exact (HierarchyProjection.proof_bound source H Cpad hcoeff hpad n).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hproof))
  queryBound := by
    intro n
    exact (HierarchyProjection.query_bound source H Cpad n).trans (Nat.mul_le_mul_right _ hquery)
  constructor := constructor

end NearCubicWires.RepairSource.HierarchyEncode
