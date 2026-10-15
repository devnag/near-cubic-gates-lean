import Proof.Hierarchy.HierarchySourceConstructor
import Proof.Hierarchy.HierarchySourceScales

/-! The actual constructor-prefix cost in the original input and clock
currencies, before any asymptotic exponent is selected. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceCost
open RepairOrdinary HierarchySourceScales
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def runtime {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  HierarchyReduction.runtimeCoefficient k H.coefficient Cpad (VerifierEncoding.code H.verifier)
def dimCoefficient (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) :=
  DimensionProducer.coefficient source.degrees.proofLog source.degrees.queries source.coefficient
def dimDegree (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) :=
  DimensionProducer.degree source.degrees.proofLog source.degrees.queries

theorem budget_bound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) :
    HierarchySourceInput.constructorBudget source H Cpad r ≤
      runtime H Cpad*(r.1+1)*PCPResourceLedger.q r.1^2+
      11658*(HierarchyEncode.length H Cpad r.1+1)*PCPResourceLedger.q (HierarchyEncode.length H Cpad r.1)^2+
      dimCoefficient source*(natBitLength (UWhole.time (HierarchyEncode.length H Cpad r.1))+1)^dimDegree source+
      2*source.coefficient*(HierarchyEncode.length H Cpad r.1+natBitLength (UWhole.time (HierarchyEncode.length H Cpad r.1))+1)^source.degrees.construction+
      64*(r.1+HierarchyEncode.length H Cpad r.1+natBitLength (UWhole.time (HierarchyEncode.length H Cpad r.1))+natBitLength (H.time r.1)+1) := by
  let y := HierarchyPadding.rawInput k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)
  let N := HierarchyEncode.length H Cpad r.1
  let u := natBitLength (UWhole.time N)
  have hy : y.length=N := by
    change (HierarchyEncode.padded H Cpad (List.ofFn r.2)).length=HierarchyEncode.length H Cpad r.1
    simpa only [List.length_ofFn] using HierarchyEncode.padded_length H Cpad hpad (List.ofFn r.2)
  have hd := DimensionsFromInput.budget_bound source.degrees.proofLog source.degrees.queries source.coefficient y
  rw [hy] at hd
  have hT := bits_length_le (UWhole.time N)
  have hB := bits_length_le (H.time r.1)
  have he : HierarchySourceInput.constructorBudget source H Cpad r=
      runtime H Cpad*(r.1+1)*PCPResourceLedger.q r.1^2+
      DimensionsFromInput.budget source.degrees.proofLog source.degrees.queries source.coefficient y+
      2*source.coefficient*(N+u+1)^source.degrees.construction+
      12*N+8*(UWhole.time N).bits.length+16*r.1+8*(H.time r.1).bits.length+42 := by
    unfold HierarchySourceInput.constructorBudget HierarchySourceInput.hierarchyInput HierarchySourceInput.budget
      HierarchySelectedSource.budget HierarchyPrefix.budget HierarchyFramedInput.budget
      SourceCall.budget SourceCall.sourceBudget
    simp only [HierarchySelectedSource.p,HierarchySelectedSource.q,HierarchySelectedSource.request,
      List.length_append,frame_length,List.length_ofFn,HierarchyReduction.ordinaryBudget]
    change (HierarchyPadding.rawInput k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)).length=N at hy
    rw [hy]
    dsimp only [runtime,u,y]
    ring
  rw [he]
  change _ ≤ runtime H Cpad*(r.1+1)*PCPResourceLedger.q r.1^2+
    11658*(N+1)*PCPResourceLedger.q N^2+dimCoefficient source*(u+1)^dimDegree source+
    2*source.coefficient*(N+u+1)^source.degrees.construction+
    64*(r.1+N+u+natBitLength (H.time r.1)+1)
  change _ ≤11658*(N+1)*PCPResourceLedger.q N^2+1+dimCoefficient source*(u+1)^dimDegree source at hd
  change (UWhole.time N).bits.length ≤ u at hT
  omega

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceCost
