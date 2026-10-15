import Proof.PCP.PCPPNativeHierarchyNodes

/-! Exact original input word and scalar-port separation for the enclosing
descriptor and faithful-source consumer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem input_word (k : ℕ) (a oracle : List Bool) :
    input source k a oracle=SourceHandoff.sourceTapes (PCPPNativeInputFields.word a oracle) := by
  funext i
  refine Fin.addCases (m:=base source k) (n:=438) (fun j=>?_) (fun j=>?_) i
  · simp [input,PCPPNativeHierarchy.input,SourceHandoff.sourceTapes]
  · simp [input,SourceHandoff.sourceTapes,base,PCPPNativeHierarchy.tapes]
theorem scalar_distinct (k : ℕ) :
    slots source k 72≠slots source k 91 ∧ slots source k 72≠slots source k 89 ∧ slots source k 91≠slots source k 89 := by
  exact ⟨fun h=>(by decide : (72:Fin 438)≠91) (slots_injective source k h),
    fun h=>(by decide : (72:Fin 438)≠89) (slots_injective source k h),
    fun h=>(by decide : (91:Fin 438)≠89) (slots_injective source k h)⟩

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
