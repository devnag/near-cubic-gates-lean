import Proof.MachineModel.OrdinaryMemoryLoop

/-! The actual memory loop at the literal sorter output. Its final sticky bit
is exactly chronological blank-memory consistency. This application starts
with the explicit prepared local workspace; producer and handoff costs are
not silently included in this receipt. -/
namespace NearCubicWires.RepairOrdinary.MemoryValidation
open LocalBitMultitape MemoryLog MemorySort MemoryCompare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def records {N : ℕ} (I W : ℕ) (events : Fin N → Event) :
    List MemoryLoop.Record :=
  (sortedIndices I (I+2) W events).map (fun i => (i.val, events i))

theorem records_length {N : ℕ} (I W : ℕ) (events : Fin N → Event) (hN : N ≤ 2^I) :
    (records I W events).length = N := by
  have h := (sorted_perm I (I+2) W events hN).length_eq
  simpa [records] using h

theorem literal_stream {N : ℕ} (I W : ℕ) (events : Fin N → Event) (hN : N ≤ 2^I) :
    MemoryLoop.stream I W (records I W events) =
      StablePartition.stream (SortCarrier.sorted (request I (I+2) W events)) := by
  rw [← sorted_output I (I+2) W events hN]
  simp [MemoryLoop.stream, MemoryLoop.fields, MemoryLoop.word, records,
    StablePartition.stream, StablePartition.recordsBits, List.flatMap_map]

theorem checks_eq_replay {N : ℕ} (I W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^(I+2))
    (ha : ∀ i, (events i).cell.2 < 2^W) :
    (MemoryLoop.checks MemoryScan.blank (records I W events)).all id =
      (MemoryLog.run (fun _ => false) ((List.finRange N).map events)).isSome := by
  rw [MemoryLoop.checks_scan]
  have he : (records I W events).map Prod.snd =
      (SortCarrier.sorted (request I (I+2) W events)).map (MemoryScan.decode I W) := by
    rw [MemoryScan.decoded_output I (I+2) W events hN hc ha]
    simp [records, List.map_map, Function.comp_def]
  rw [he]
  have h := MemoryScan.literal_scan_iff I (I+2) W events hN hc ha
  exact Bool.eq_iff_iff.mpr h

theorem checked_run {N : ℕ} (I W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^(I+2))
    (ha : ∀ i, (events i).cell.2 < 2^W) :
    ∃ r : ExecutionReceipt 14 43,
      runFrom MemoryLoop.machine (N*(240*(I+2)+182)+1)
        (MemoryBody.config MemoryLoop.machine.start I [] [] []
          (StablePartition.stream (SortCarrier.sorted (request I (I+2) W events))) 0
          (key I W MemoryScan.blank) false [] true) = some r ∧
      r.final.tapes 13 =
        [(MemoryLog.run (fun _ => false) ((List.finRange N).map events)).isSome] ∧
      r.final.heads 13 = 0 ∧ r.steps = N*(240*(I+2)+182)+1 := by
  have fits : ∀ r ∈ records I W events,
      cellCode W r.2.cell < 2^(I+2) ∧ r.2.cell.2 < 2^W := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact ⟨hc i, ha i⟩
  have ordered : (records I W events).Pairwise
      (fun r s => cellCode W r.2.cell ≤ cellCode W s.2.cell) := by
    have h := MemoryScan.sorted_cell_order I (I+2) W events hN hc
    simpa only [records, List.pairwise_map] using h
  obtain ⟨last, record, clone, rank, _, _, _, r, hr, hf, hs⟩ :=
    MemoryLoop.loop_run I W (records I W events) MemoryScan.blank [] [] [] [] [] true
      (by simp) (by simp) (by simp)
      (by simp [MemoryScan.blank, cellCode]) (by simp [MemoryScan.blank]) fits
      (by intro r _; simp [MemoryScan.blank, cellCode]) ordered
  have hcost : MemoryLoop.cost I (records I W events) = N*(240*(I+2)+182)+1 := by
    simp only [MemoryLoop.cost, records_length I W events hN, MemoryBody.bodyCost,
      MemoryCycle.copyCap]
    ring
  rw [hcost] at hr hs
  rw [literal_stream I W events hN] at hr
  refine ⟨r, ?_, ?_, ?_, hs⟩
  · have hstart : MemoryLoop.machine.start = RecordController.test 41 := rfl
    have hblank : MemoryScan.blank.after = false := rfl
    rw [hstart]
    simpa only [List.nil_append, List.length_nil, hblank] using hr
  · rw [hf]
    change [true && (MemoryLoop.checks MemoryScan.blank (records I W events)).all id] = _
    rw [Bool.true_and, checks_eq_replay I W events hN hc ha]
  · rw [hf]
    rfl

end NearCubicWires.RepairOrdinary.MemoryValidation
