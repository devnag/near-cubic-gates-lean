import Proof.Hierarchy.HierarchyClauseFields
import Proof.PCP.PCPOuterDock

/-! The single physical normalized-PCP constructor and its exact raw
budget, before the independently checked ordinary framing wrapper. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def tapes (k : ℕ) := HierarchyClauses.tapes source k+129
def machine (k CH Cpad : ℕ) (code : List Bool) :=
  PCPOuterDock.machine (HierarchyClauses.machine source k CH Cpad code) (HierarchyClauses.fieldSlots source k)
def output (k : ℕ) : Fin (tapes source k) := PCPOuterDock.rawSlot (HierarchyClauses.tapes source k)
def entry (k CH Cpad : ℕ) (code x bound : List Bool) :=
  let c := TapeEmbedding.config (fun _ : Fin 129 => 0) (fun _ : Fin 129 => [])
    (HierarchyClauses.entry source k CH Cpad code x bound)
  (⟨(machine source k CH Cpad code).start,c.heads,c.tapes⟩ : Configuration (tapes source k) _)
def budget (k CH Cpad : ℕ) (code x : List Bool) :=
  HierarchyClauses.budget source k CH Cpad code x+1+
    PCPOuter.budget (PCPOuter.size (HierarchyClauses.words source k CH Cpad code x 0)
      (HierarchyClauses.words source k CH Cpad code x 1)
      (HierarchyClauses.words source k CH Cpad code x 2)
      (HierarchyClauses.words source k CH Cpad code x 3))

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
