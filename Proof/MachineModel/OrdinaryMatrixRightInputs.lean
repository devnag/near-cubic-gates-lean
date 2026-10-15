import Proof.MachineModel.OrdinaryMatrixRightCost
import Proof.MachineModel.OrdinaryMatrixCoordinateStream

/-! Arbitrary per-inner occurrence orders, including the rank-sort order,
supply the exact right-grid permutation after physical coordinate swap. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightInputs
open LocalBitMultitape SupplierPrinter CoordinateKey
open StablePartition (Record recordsBits)
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputs {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U))) : List Record :=
  (List.finRange Used).flatMap (fun inner => (order inner).map
    (fun id => key M M id.val inner.val (payload inner id)))
def original {U Used : ℕ} (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U))) : List MatrixCoordinateTranspose.Record :=
  (List.finRange Used).flatMap (fun inner => (order inner).map
    (fun id => (payload inner id,inner.val,id.val)))

theorem transposed_words {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U))) :
    MatrixCoordinateTranspose.output M (original payload order)=recordsBits (inputs M payload order) := by
  simp only [MatrixCoordinateTranspose.output,original,inputs,recordsBits,List.flatMap_assoc,
    List.flatMap_map]
  rfl

theorem inputs_perm_grid {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U)))
    (ho : ∀ inner,(order inner).Perm (List.finRange (U+U))) :
    (inputs M payload order).Perm (grid M M payload) := by
  have hp := List.Perm.flatMap_left (List.finRange Used)
    (fun inner _ => (ho inner).map (fun id => key M M id.val inner.val (payload inner id)))
  rw [grid_rows]
  simpa only [inputs,List.ofFn_eq_map,List.flatMap] using hp

def request {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U))) : SortCarrier.Request :=
  DominanceSort.fixedRequest (inputs M payload order) (M+M+1) (by
    intro r hr
    obtain ⟨inner,_,hm⟩ := List.mem_flatMap.mp hr
    obtain ⟨id,_,rfl⟩ := List.mem_map.mp hm
    exact key_width _ _ _ _ _)

theorem sorted_request {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U)))
    (ho : ∀ inner,(order inner).Perm (List.finRange (U+U)))
    (hi : U+U ≤ 2^M) (hk : Used ≤ 2^M) :
    SortCarrier.sorted (request M payload order)=grid M M payload :=
  sorted_eq_grid M M payload (request M payload order) (inputs_perm_grid M payload order ho) hi hk

theorem plane_run {U Used Capacity : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U)))
    (ho : ∀ inner,(order inner).Perm (List.finRange (U+U)))
    (hi : U+U ≤ 2^M) (hk : Used ≤ 2^M) (hcap : Used ≤ Capacity) (out : List Bool) :
    ∃ actual : ExecutionReceipt 11 (88+MatrixRightSort.planeStates),
      runFrom MatrixRightSort.machine (512*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2)
        (MatrixRightSort.input (request M payload order) out U Used ((Capacity-Used)*U))=some actual ∧
      actual.final.tapes 7=out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (MatrixRightGrid.right payload)) ∧
      actual.final.heads 7=(out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (MatrixRightGrid.right payload))).length ∧
      actual.steps ≤ 512*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2 := by
  have hgrid := sorted_request M payload order ho hi hk
  obtain ⟨actual,hr,ht,hh,hs⟩ := MatrixRightSort.joined_run M payload hcap (request M payload order) hgrid out
  have hb := MatrixRightSort.joined_budget (Capacity := Capacity) M payload (request M payload order) hgrid
  have hm := runFrom_moreFuel MatrixRightSort.machine _
    (512*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2-
      (2*SortCarrier.budget (request M payload order).records+3+MatrixRightGrid.budget M U Used Capacity)) _ actual hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨actual,hm,ht,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.MatrixRightInputs
