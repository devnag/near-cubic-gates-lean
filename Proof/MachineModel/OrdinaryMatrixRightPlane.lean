import Proof.MachineModel.OrdinaryMatrixRightGrid

/-! The literal inner-major keyed grid is consumed by the actual selector
and padded to the Boolean right matrix, including empty inner dimensions. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGrid
open LocalBitMultitape SupplierPrinter CoordinateKey
open StablePartition (recordsBits)
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_length {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool) :
    (MatrixRightRows.fields (rows M payload)).length=Used*(U+U)*(4*M+3) := by
  rw [←rows_fields]
  have hw : ∀ r ∈ grid M M payload,(RadixSemantics.word r).length=M+M+1 := by
    intro r hr
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hr
    exact key_width _ _ _ _ _
  have h := SortCost.stream_length_of_width (grid M M payload) (M+M+1) hw
  have hl : (grid M M payload).length=Used*(U+U) := by simp [grid]
  have hm : 2*(M+M+1)+1=4*M+3 := by omega
  rw [hl,hm] at h
  simp only [StablePartition.stream,List.length_append,List.length_singleton] at h
  omega

def budget (M U Used Capacity : ℕ) :=
  Used*(U+U)*(4*M+3)+Used*(6*U+12)+2*((Capacity-Used)*U)+8

theorem plane_run {U Used Capacity : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (hcap : Used ≤ Capacity) (pre suffix out : List Bool) :
    ∃ actual : ExecutionReceipt 5 (MatrixRightPadding.rowStates+5),
      runFrom MatrixRightPadding.machine (budget M U Used Capacity)
        (MatrixRightPadding.cfg MatrixRightPadding.machine.start
          (pre++recordsBits (grid M M payload)++suffix) pre.length out U Used ((Capacity-Used)*U))=some actual ∧
      actual.final=MatrixRightPadding.cfg (Fin.natAdd MatrixRightPadding.rowStates (4 : Fin 5))
        (pre++recordsBits (grid M M payload)++suffix) (pre.length+Used*(U+U)*(4*M+3))
        (out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (right payload)))
        U Used ((Capacity-Used)*U) ∧ actual.steps ≤ budget M U Used Capacity := by
  obtain ⟨actual,hr,hf,hs⟩ := MatrixRightPadding.padding_run U ((Capacity-Used)*U)
    (rows M payload) pre suffix out (rows_width M payload)
  rw [fields_length,rows_length] at hr hf hs
  rw [←rows_fields] at hr hf
  have hout : (out++MatrixRightRows.output (rows M payload))++List.replicate ((Capacity-Used)*U) false=
      out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (right payload)) := by
    rw [List.append_assoc,literal_output M payload hcap]
  rw [hout] at hf
  exact ⟨actual,hr,hf,hs⟩

end NearCubicWires.RepairOrdinary.MatrixRightGrid
