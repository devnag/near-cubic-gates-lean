import Proof.Hierarchy.HierarchyNormalizedRun
import Proof.Foundations.OrdinaryFramedSource

/-! The one actual normalized constructor on the literal ordinary hierarchy
input. The native codec and source request are transported without change. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def pcp {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad) :=
  normalizedSourcePCP source H (HierarchyEncode.encode H Cpad)
    (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
    (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)
def word {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) := pcpWord (pcp source H Cpad hpad) r.2

theorem hierarchy_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    ∃ receipt,run (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2))
      (SourceHandoff.sourceTapes (HierarchySourceInput.hierarchyInput H r))=some receipt ∧
      receipt.final.tapes (output source k)=word source H Cpad hpad r ∧
      receipt.final.heads (output source k)=0 ∧
      receipt.steps ≤ budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) := by
  obtain ⟨receipt,hr,rt,rh,rs⟩ := raw_run source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) (List.ofFn r.2) (H.time r.1).bits hpad
  obtain ⟨he,hR,hQ⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  rw [he,hR,hQ] at rt
  refine ⟨receipt,hr,?_,rh,rs⟩
  exact rt.trans (Codec.source_word source H (HierarchyEncode.encode H Cpad)
    (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
    (HierarchyProjection.width_fits source H Cpad hpad)
    (HierarchyProjection.queries_fit source H Cpad hpad) r).symm

def constructor {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) :
    OrdinaryWordFunction InputRequest (HierarchySourceInput.hierarchyInput H) (word source H Cpad hpad)
      (HierarchyNormalizedBounds.framedBudget source H Cpad) :=
  FramedSource.ofRaw (by omega)
    (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) (output source k)
    (HierarchySourceInput.hierarchyInput H) (word source H Cpad hpad)
    (fun r => budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2))
    (by
      intro r
      obtain ⟨receipt,hr,rt,_rh,_rs⟩ := hierarchy_run source H Cpad hpad r
      exact ⟨receipt,hr,rt⟩)

def boundedConstructor {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    OrdinaryWordFunction InputRequest (HierarchySourceInput.hierarchyInput H) (word source H Cpad hpad)
      (fun r => HierarchyNormalizedBounds.coefficient source H Cpad*
        (r.1+1)^HierarchyNormalizedBounds.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyNormalizedBounds.logExponent source) :=
  (constructor source H Cpad hpad).enlargeBudget
    (HierarchyNormalizedBounds.budget_bound source H Cpad hcoeff hpad)

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
