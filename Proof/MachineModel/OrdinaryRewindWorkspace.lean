import Proof.MachineModel.OrdinaryZeroPadding
import Proof.MachineModel.OrdinaryPartitionWorkspace

/-! Reuse the same reset counter between record passes. The actual retained
zeros remain on the tape; padding invariance transports the interpreter run
and charges those cells. The final application uses four fixed tapes. -/
namespace NearCubicWires.RepairOrdinary.Rewind.Workspace
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (t capacity : ℕ) : Fin (t + 1) → ℕ :=
  Fin.addCases (fun _ => 0) (fun _ => capacity)

@[simp] theorem capacity_cells (t capacity : ℕ) : ZeroPadding.cells (capacities t capacity) = capacity := by
  simp [ZeroPadding.cells, capacities, Fin.sum_univ_add]

theorem pad_zeros (capacity n : ℕ) :
    ZeroPadding.pad capacity (List.replicate n false) = List.replicate (max capacity n) false := by
  simp only [ZeroPadding.pad, List.length_replicate, ← List.replicate_add]
  congr 1
  omega

theorem padded_finished {t s : ℕ} (tapes : Fin t → List Bool) (capacity n : ℕ) :
    ZeroPadding.config (capacities t capacity) (Rewind.finished (s := s) tapes n) =
      Rewind.finished (s := s) tapes (max capacity n) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ZeroPadding.config, capacities, Rewind.finished, Rewind.config, pad_zeros]

theorem reset_workspace {t s : ℕ} (p : Machine t s) (fuel : ℕ) (input : Fin t → List Bool)
    (source : ExecutionReceipt t s) (hr : run p fuel input = some source) (capacity : ℕ) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      run (Rewind.machine p) (2 * source.steps + 2)
        (Fin.addCases input (fun _ => List.replicate capacity false)) = some r ∧
      (∀ i : Fin t, r.final.tapes (i.castAdd 1) = source.final.tapes i) ∧
      r.final.tapes ((0 : Fin 1).natAdd t) = List.replicate (max capacity source.steps) false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 2 * source.steps + 2 ∧
      r.peakTapeCells ≤ source.peakTapeCells + source.steps + capacity := by
  obtain ⟨base, hb, hbf, hbs, hbp⟩ := Rewind.recorded_run p fuel (initialConfiguration p input)
    source hr 0 (by simp [initialConfiguration])
  have hb' : runFrom (Rewind.machine p) (2 * source.steps + 2)
      (Rewind.recording (initialConfiguration p input) 0) = some base := by simpa using hb
  obtain ⟨r, hrun, hf, hs, hp⟩ := ZeroPadding.run_config (Rewind.machine p)
    (capacities t capacity) (2 * source.steps + 2) _ base hb'
  have hinit : ZeroPadding.config (capacities t capacity)
        (Rewind.recording (initialConfiguration p input) 0) =
      initialConfiguration (Rewind.machine p)
        (Fin.addCases input (fun _ => List.replicate capacity false)) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [ZeroPadding.config, Rewind.recording, Rewind.config, initialConfiguration]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [ZeroPadding.config, capacities, Rewind.recording, Rewind.config,
          initialConfiguration, ZeroPadding.pad]
  have hfinal : r.final = Rewind.finished (s := s) source.final.tapes (max capacity source.steps) := by
    rw [hf, hbf, padded_finished]
    simp
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinit] at hrun
    exact hrun
  · intro i
    simp [hfinal, Rewind.finished, Rewind.config]
  · simp [hfinal, Rewind.finished, Rewind.config]
  · intro i
    rw [hfinal]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Rewind.finished, Rewind.config]
  · simp only [Nat.zero_add] at hbs
    exact hs.trans hbs
  · simp only [capacity_cells] at hp
    omega

open StablePartition StablePartition.Workspace

theorem partition_reset_fixed_workspace (rs : List Record) (junk : List Bool)
    (old : Bool → List Bool) (capacity : ℕ)
    (hi : (stream rs).length + junk.length ≤ capacity)
    (ho : ∀ tag, (old tag).length ≤ capacity) :
    ∃ r : ExecutionReceipt 4 11,
      run (Rewind.machine StablePartition.machine) (2 * ((stream rs).length + rs.length) + 2)
        (Fin.addCases
          (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk else old (i.val == 2))
          (fun _ => List.replicate (2 * capacity) false)) = some r ∧
      (∀ tag, r.final.tapes ((outputTape tag).castAdd 1) =
        overlay (stream (selected tag rs)) (old tag)) ∧
      (∀ i : Fin 3, (r.final.tapes (i.castAdd 1)).length ≤ capacity) ∧
      r.final.tapes 3 = List.replicate (2 * capacity) false ∧
      (∀ i, r.final.heads i = 0) ∧
      r.steps ≤ 4 * (stream rs).length + 2 ∧ r.peakTapeCells ≤ 8 * capacity + 1 := by
  obtain ⟨source, hr, hf, hout, _, hs, hp⟩ := partition_workspace rs junk old
  have hcost : source.steps ≤ 2 * (stream rs).length := by
    have hn := record_count_le rs
    simp only [stream, List.length_append, List.length_singleton] at hs ⊢
    omega
  have hcells : ∀ i, (source.final.tapes i).length ≤ capacity := by
    intro i
    fin_cases i
    · simpa [hf] using hi
    · have he := hout false
      have hl := selected_stream_length_le false rs
      change (source.final.tapes (outputTape false)).length ≤ capacity
      rw [he, overlay_length]
      exact max_le (by omega) (ho false)
    · have he := hout true
      have hl := selected_stream_length_le true rs
      change (source.final.tapes (outputTape true)).length ≤ capacity
      rw [he, overlay_length]
      exact max_le (by omega) (ho true)
  obtain ⟨r, hrun, he, hcounter, hheads, hsteps, hpeak⟩ := reset_workspace
    StablePartition.machine ((stream rs).length + rs.length) _ source hr (2 * capacity)
  refine ⟨r, ?_, ?_, ?_, ?_, hheads, ?_, ?_⟩
  · simpa only [hs] using hrun
  · intro tag
    exact (he (outputTape tag)).trans (hout tag)
  · intro i
    rw [he i]
    exact hcells i
  · have hn : max (2 * capacity) source.steps = 2 * capacity := max_eq_left (by omega)
    simpa [hn] using hcounter
  · omega
  · have h0 := ho false
    have h1 := ho true
    simp only [outCells] at hp
    omega

end NearCubicWires.RepairOrdinary.Rewind.Workspace
