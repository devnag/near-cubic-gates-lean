import Proof.MachineModel.OrdinaryTransitionWalkTrace
import Proof.MachineModel.OrdinaryInitializedTrace

/-! Exact bridge from the appended chronological emitter word to the
existing raw memory checker. The chronological index is the list position;
no certificate-supplied timestamp or new checker is introduced. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog MemorySort
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure ListReady (I W : ℕ) (events : List Event) : Prop where
  positive : 0 < events.length
  indicesFit : events.length ≤ 2^I
  cellsFit : ∀ e ∈ events, cellCode W e.cell < 2^(I+2)
  addressesFit : ∀ e ∈ events, e.cell.2 < 2^W

def listRequest {I W : ℕ} {events : List Event} (h : ListReady I W events) : Request where
  count := events.length
  indexBits := I
  addressBits := W
  events := events.get
  positive := h.positive
  indicesFit := h.indicesFit
  cellsFit := fun i => h.cellsFit _ (List.get_mem events i)
  addressesFit := fun i => h.addressesFit _ (List.get_mem events i)

theorem chronological_records (I K W : ℕ) (events : List Event) :
    (events.zipIdx 0).map (fun p => encoded I K W p.2 p.1) =
      (List.finRange events.length).map (fun i => encoded I K W i.val (events.get i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
      List.getElem_finRange, Fin.val_cast, List.get_eq_getElem]

theorem chronological_events (events : List Event) :
    (List.finRange events.length).map events.get = events := by
  rw [List.finRange, List.map_ofFn]
  exact List.ofFn_get events

theorem list_input {I W : ℕ} {events : List Event} (h : ListReady I W events) :
    MemoryInitialEmission.fields I (I+2) W 0 events ++ [false] = (listRequest h).input := by
  change StablePartition.recordsBits
    ((events.zipIdx 0).map (fun p => encoded I (I+2) W p.2 p.1)) ++ [false] =
      StablePartition.recordsBits
        ((List.finRange events.length).map (fun i => encoded I (I+2) W i.val (events.get i))) ++ [false]
  rw [chronological_records]

theorem list_result {I W : ℕ} {events : List Event} (h : ListReady I W events) :
    (listRequest h).result = (MemoryLog.run (fun _ => false) events).isSome := by
  change (MemoryLog.run (fun _ => false) ((List.finRange events.length).map events.get)).isSome = _
  rw [chronological_events]

theorem initialized_positive (input witness : List Bool) (trace : List Event) :
    0 < (MemoryInitialization.events input witness ++ trace).length := by
  rw [List.length_append, MemoryInitialization.initial_count]
  omega

theorem initialized_input {I W : ℕ} (input witness : List Bool) (trace : List Event)
    (h : ListReady I W (MemoryInitialization.events input witness ++ trace)) :
    (MemoryInitialEmission.fields I (I+2) W 0 (MemoryInitialization.events input witness) ++
      MemoryInitialEmission.fields I (I+2) W
        (MemoryInitialization.events input witness).length trace) ++ [false] =
      (listRequest h).input := by
  have he := list_input h
  rw [MemoryInitialEmission.fields_append] at he
  simpa only [Nat.zero_add] using he

theorem list_raw_run {I W : ℕ} {events : List Event} (h : ListReady I W events) :
    ∃ r : ExecutionReceipt 21 138,
      run machine (rawBudget (listRequest h)) (SourceHandoff.sourceTapes
        (MemoryInitialEmission.fields I (I+2) W 0 events ++ [false])) = some r ∧
      r.final.tapes 19 = [(MemoryLog.run (fun _ => false) events).isSome] := by
  rw [list_input h]
  simpa only [list_result] using raw_run (listRequest h)

end NearCubicWires.RepairOrdinary.MemoryChecker
