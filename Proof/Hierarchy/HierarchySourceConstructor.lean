import Proof.Hierarchy.HierarchySourceInput
import Proof.Foundations.OrdinaryFramedSource

/-! The actual ordinary two-field hierarchy input invokes the same selected
PCP source at the exact hierarchy encoding request. Normalization follows
inside the retained raw core; this carrier certifies the enclosing prefix. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceInput
open LocalBitMultitape RepairOrdinary SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem request_ext (a b : InputRequest) (h : List.ofFn a.2=List.ofFn b.2) : a=b := by
  rcases a with ⟨n,x⟩
  rcases b with ⟨m,y⟩
  have hn : n=m := by simpa only [List.length_ofFn] using congrArg List.length h
  cases hn
  have he : x=y := List.ofFn_injective h
  cases he
  rfl

theorem encoded_request {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    HierarchySelectedSource.request (HierarchyPadding.rawInput k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) (List.ofFn r.2))=HierarchyEncode.encode H Cpad r := by
  apply request_ext
  simp only [HierarchySelectedSource.request,List.ofFn_get]
  exact (HierarchyEncode.encode_word H Cpad hpad r).symm

def hierarchyInput {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (r : InputRequest) :=
  frame (List.ofFn r.2)++frame (H.time r.1).bits
def constructorBudget (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (r : InputRequest) :=
  4*(hierarchyInput H r).length+3+
    budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)

noncomputable def constructor (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad) :
    OrdinaryWordFunction InputRequest (hierarchyInput H)
      (fun r => (source.output (HierarchyEncode.encode H Cpad r)).word) (constructorBudget source H Cpad) :=
  FramedSource.ofRaw (by dsimp [tapes]; omega)
    (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) (outputTape source k)
    (hierarchyInput H) (fun r => (source.output (HierarchyEncode.encode H Cpad r)).word)
    (fun r => budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2))
    (by
      intro r
      obtain ⟨out,hready,hfields,hout,hretained⟩ := raw_run source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) (List.ofFn r.2) (H.time r.1).bits hpad
      obtain ⟨receipt,hr,ht,hh,hs⟩ := hready
      refine ⟨receipt,hr,?_⟩
      rw [ht,hout,encoded_request H Cpad hpad r])

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceInput
