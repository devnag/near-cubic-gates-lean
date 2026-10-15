import Proof.MachineModel.OrdinaryMemorySort

/-! The actual encoded sorter supplies the chronological-subsequence premise
of the computation-log memory checker. This is a bounded semantic/runtime
application, not the complete fixed universal verifier. -/
namespace NearCubicWires.RepairOrdinary.MemorySort
open LocalBitMultitape StablePartition MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cell_subsequence {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hcells : ∀ i, cellCode W (events i).cell < 2^K) (cell : Cell) :
    atCell cell ((sortedIndices I K W events).map events) =
      atCell cell ((List.finRange N).map events) := by
  let p : Fin N → Bool := fun i => (events i).cell == cell
  have hp := (sorted_perm I K W events hN).filter p
  have hs := (same_cell_order I K W events hN hcells).filter p
  have hsorted : ((sortedIndices I K W events).filter p).Pairwise (fun i j => i ≤ j) := by
    apply hs.imp_of_mem
    intro i j hi hj hij
    have hei : (events i).cell = cell := by simpa [p] using (List.mem_filter.mp hi).2
    have hej : (events j).cell = cell := by simpa [p] using (List.mem_filter.mp hj).2
    exact hij (hei.trans hej.symm)
  have hbase : (List.finRange N).Pairwise (fun i j => i ≤ j) := by
    rw [← List.ofFn_id, List.pairwise_ofFn]
    intro i j hij
    exact hij.le
  have he := hp.eq_of_pairwise' hsorted (hbase.filter p)
  simpa only [atCell, List.filter_map, Function.comp_def, p] using congrArg (List.map events) he

theorem sorted_checks_sound {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hcells : ∀ i, cellCode W (events i).cell < 2^K)
    (memory : Memory) (hchecks : valid memory ((sortedIndices I K W events).map events)) :
    ∃ finalMemory, MemoryLog.run memory ((List.finRange N).map events) = some finalMemory :=
  chronological_replay memory _ _ (cell_subsequence I K W events hN hcells) hchecks

theorem actual_sort_and_replay {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hcells : ∀ i, cellCode W (events i).cell < 2^K)
    (memory : Memory) (hchecks : valid memory ((sortedIndices I K W events).map events)) :
    ∃ r : ExecutionReceipt SortCost.carrier.program.tapeCount SortCost.carrier.program.stateCount,
      LocalBitMultitape.run SortCost.carrier.program.machine (128*(N+1)*(I+K+3)^2)
        (SortCost.carrier.program.inputTapes (stream (request I K W events).records)) = some r ∧
      r.final.tapes SortCost.carrier.program.outputTape =
        stream ((sortedIndices I K W events).map (fun i => encoded I K W i.val (events i))) ∧
      ∃ finalMemory, MemoryLog.run memory ((List.finRange N).map events) = some finalMemory := by
  obtain ⟨r, hr, hout⟩ := sort_run I K W events hN
  exact ⟨r, hr, hout, sorted_checks_sound I K W events hN hcells memory hchecks⟩

end NearCubicWires.RepairOrdinary.MemorySort
