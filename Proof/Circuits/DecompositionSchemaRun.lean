import Proof.Circuits.DecompositionGlobalRun
import Proof.Circuits.DecompositionNativeSemantics

/-! Exact source-child specialization of the whole physical serializer. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSchema
open LocalBitMultitape DecompositionCodeBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem word_eq {n : ℕ} (children : List (ExactThresholdGate n)) :
    DecompositionInputCounts.word n (groups children).length
      (DecompositionAtomLoop.stream (groups children).flatten)=payload children := by
  rw [payload_eq,groups_length]
  rfl

theorem field_count_bound {n : ℕ} (children : List (ExactThresholdGate n)) :
    (groups children).flatten.length ≤ measured children := by
  exact (native_count (values children)).trans
    (by rw [native_values]; exact native_measured children)

theorem child_count_bound {n : ℕ} (children : List (ExactThresholdGate n)) :
    (groups children).length ≤ measured children :=
  (groups_count _ (group_positive children)).trans (native_measured children)

def budget (D C : ℕ) {n : ℕ} (children : List (ExactThresholdGate n)) :=
  DecompositionGlobal.budget D C (C*(measured children+1)^D) n (groups children)

theorem schema_run (D C : ℕ) {n : ℕ} (children : List (ExactThresholdGate n))
    (hatom : ∀ z∈(groups children).flatten,
      DecompositionAtom.budget z+1 ≤ C*(measured children+1)^D)
    (hchild : ∀ xs∈groups children,PCPTraversal.budget
      (PCPSerializerMass.mass (DecompositionNesting.atomFields xs))+1 ≤ C*(measured children+1)^D) :
    ∃ r,run (DecompositionGlobal.machine D C) (budget D C children)
      (DecompositionGlobal.input D (payload children))=some r ∧
      r.final.tapes (DecompositionGlobal.outputSlot D)=(output children).bits ∧
      r.steps ≤ budget D C children := by
  obtain ⟨r,hr,ho,hs⟩ := DecompositionGlobal.global_run D C (C*(measured children+1)^D) n
    (groups children) (group_length children) (by rw [word_eq]; rfl) hatom hchild
  rw [word_eq] at hr
  rw [DecompositionNesting.outer_code] at ho
  exact ⟨r,hr,ho,hs⟩

theorem atom_capacity {n : ℕ} (children : List (ExactThresholdGate n)) :
    ∀ z∈(groups children).flatten,DecompositionAtom.budget z+1 ≤ globalEnvelope (measured children) := by
  intro z hz
  obtain ⟨xs,hxs,hz⟩ := List.mem_flatten.mp hz
  exact global_atom (groups children) xs z (measured children) hxs hz (native_measured children)

theorem child_capacity {n : ℕ} (children : List (ExactThresholdGate n)) :
    ∀ xs∈groups children,PCPTraversal.budget (PCPSerializerMass.mass
      (DecompositionNesting.atomFields xs))+1 ≤ globalEnvelope (measured children) := by
  intro xs hxs
  exact global_child (groups children) xs (measured children) hxs (native_measured children)

theorem outer_capacity {n : ℕ} (children : List (ExactThresholdGate n)) :
    PCPTraversal.budget (PCPSerializerMass.mass (childFields (groups children)))+1 ≤
      globalEnvelope (measured children) :=
  global_outer _ _ (group_positive children) (native_measured children)

end NearCubicWires.RepairOrdinary.DecompositionSchema
