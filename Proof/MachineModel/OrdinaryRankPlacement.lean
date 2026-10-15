import Proof.MachineModel.OrdinaryRankScalar

/-! Place the rank-scan macros on the same five physical tapes. All inactive
contents and cursors are retained, and their occupied cells are charged. -/
namespace NearCubicWires.RepairOrdinary.RankPlacement
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (input : List Bool) (sourceHead : ℕ)
    (output rank : List Bool) (rankHead : ℕ) (marks : List Bool) (marksHead : ℕ)
    (scratch : List Bool) (scratchHead : ℕ) : Configuration 5 s :=
  ⟨state, ![sourceHead, output.length, rankHead, marksHead, scratchHead],
    ![input, output, rank, marks, scratch]⟩

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (input : List Bool) (sourceHead : ℕ)
    (output rank : List Bool) (rankHead : ℕ) (marks : List Bool) (marksHead : ℕ)
    (scratch : List Bool) (scratchHead : ℕ) :
    (config state input sourceHead output rank rankHead marks marksHead scratch scratchHead).tapeCells =
      input.length + output.length + rank.length + marks.length + scratch.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

def copyLayout : Fin 5 ≃ Fin 5 := Equiv.swap 2 3
def appendLayout : Fin 5 ≃ Fin 5 := ((Equiv.swap 0 2).trans (Equiv.swap 0 3)).trans (Equiv.swap 0 4)
def scalarLayout : Fin 5 ≃ Fin 5 := ((Equiv.swap 0 2).trans (Equiv.swap 1 4)).trans (Equiv.swap 1 3)

@[simp] theorem copy_inverse : (copyLayout.symm : Fin 5 → Fin 5) = ![0, 1, 3, 2, 4] := by decide
@[simp] theorem append_inverse : (appendLayout.symm : Fin 5 → Fin 5) = ![4, 1, 0, 2, 3] := by decide
@[simp] theorem scalar_inverse : (scalarLayout.symm : Fin 5 → Fin 5) = ![2, 3, 0, 4, 1] := by decide

def copyMachine : Machine 5 3 := TapeRenaming.machine copyLayout (TapeEmbedding.machine 2 RankRecordCopy.machine)
def appendMachine : Machine 5 3 := TapeRenaming.machine appendLayout (TapeEmbedding.machine 1 RankAppend.machine)
def scalarMachine (p : Machine 2 4) : Machine 5 4 :=
  TapeRenaming.machine scalarLayout (TapeEmbedding.machine 3 p)

theorem copy_run (pre bits suffix output rank : List Bool) (hw : rank.length = bits.length) :
    ∃ r : ExecutionReceipt 5 3,
      runFrom copyMachine (2 * bits.length + 1)
        (config 0 (pre ++ frame bits ++ suffix) pre.length output rank 0
          (List.replicate bits.length false) 0 (List.replicate bits.length false) 0) = some r ∧
      r.final = config 2 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (output ++ Streaming.marks bits) rank 0 (List.replicate bits.length true) bits.length
        (List.replicate bits.length false) 0 ∧
      r.steps = 2 * bits.length + 1 ∧
      r.peakTapeCells ≤ (pre ++ frame bits ++ suffix).length + output.length + 6 * bits.length := by
  obtain ⟨base, hb, hf, hs, hp⟩ := RankWorkspace.copy_run pre bits suffix output
  let extra : Fin 2 → List Bool := ![rank, List.replicate bits.length false]
  have he := TapeEmbedding.run_embed RankRecordCopy.machine (fun _ : Fin 2 => 0) extra _ _ base hb
  have hr := TapeRenaming.run_rename copyLayout (TapeEmbedding.machine 2 RankRecordCopy.machine) _ _ _ he
  have hi : TapeRenaming.config copyLayout
      (TapeEmbedding.config (fun _ : Fin 2 => 0) extra (RankWorkspace.copyStart pre bits suffix output)) =
      config 0 (pre ++ frame bits ++ suffix) pre.length output rank 0
        (List.replicate bits.length false) 0 (List.replicate bits.length false) 0 := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankWorkspace.copyStart,
        ZeroPadding.config, RankRecordCopy.config, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankWorkspace.copyStart,
        ZeroPadding.config, RankWorkspace.copyCapacity, RankRecordCopy.config, config, Fin.addCases,
        ZeroPadding.pad, extra]
  refine ⟨TapeRenaming.receipt copyLayout (TapeEmbedding.receipt (fun _ : Fin 2 => 0) extra base),
    by rw [hi] at hr; exact hr, ?_, hs, ?_⟩
  · change TapeRenaming.config copyLayout (TapeEmbedding.config (e := 2) _ _ base.final) = _
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankRecordCopy.config, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankRecordCopy.config, config, Fin.addCases, extra]
  · change base.peakTapeCells + TapeEmbedding.extraCells extra ≤ _
    simp [TapeEmbedding.extraCells, extra, Fin.sum_univ_succ, hw]
    simp only [List.length_append, frame_length] at hp
    omega

theorem append_run (input output bits : List Bool) (sourceHead : ℕ) :
    ∃ r : ExecutionReceipt 5 3,
      runFrom appendMachine (2 * bits.length + 1)
        (config 0 input sourceHead output bits 0 (List.replicate bits.length true) (bits.length - 1)
          (List.replicate bits.length false) 0) = some r ∧
      r.final = config 2 input sourceHead (output ++ Streaming.marks bits ++ [false]) bits bits.length
        (List.replicate bits.length false) 0 (List.replicate bits.length true) bits.length ∧
      r.steps = 2 * bits.length + 1 ∧
      r.peakTapeCells ≤ input.length + output.length + 6 * bits.length + 1 := by
  obtain ⟨base, hb, hf, hs, hp⟩ := RankWorkspace.append_run bits output
  have he := TapeEmbedding.run_embed RankAppend.machine (fun _ : Fin 1 => sourceHead)
    (fun _ : Fin 1 => input) _ _ base hb
  have hr := TapeRenaming.run_rename appendLayout (TapeEmbedding.machine 1 RankAppend.machine) _ _ _ he
  have hi : TapeRenaming.config appendLayout
      (TapeEmbedding.config (fun _ : Fin 1 => sourceHead) (fun _ : Fin 1 => input)
        (RankWorkspace.appendStart bits output)) =
      config 0 input sourceHead output bits 0 (List.replicate bits.length true) (bits.length - 1)
        (List.replicate bits.length false) 0 := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankWorkspace.appendStart,
        ZeroPadding.config, RankAppend.config, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankWorkspace.appendStart,
        ZeroPadding.config, RankWorkspace.appendCapacity, RankAppend.config, config, Fin.addCases, ZeroPadding.pad]
  refine ⟨TapeRenaming.receipt appendLayout
    (TapeEmbedding.receipt (fun _ : Fin 1 => sourceHead) (fun _ : Fin 1 => input) base),
    by rw [hi] at hr; exact hr, ?_, hs, ?_⟩
  · change TapeRenaming.config appendLayout (TapeEmbedding.config (e := 1) _ _ base.final) = _
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankAppend.config, config, Fin.addCases,
        Streaming.marks]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankAppend.config, config, Fin.addCases]
  · change base.peakTapeCells + TapeEmbedding.extraCells (fun _ : Fin 1 => input) ≤ _
    simp only [TapeEmbedding.extraCells, Fin.sum_univ_one]
    omega

theorem scalar_config (state : Fin 4) (input output rank marks scratch : List Bool)
    (sourceHead rankHead marksHead scratchHead : ℕ) :
    TapeRenaming.config scalarLayout
      (TapeEmbedding.config ![sourceHead, output.length, marksHead] ![input, output, marks]
        (RankScalar.scalarConfig state rank rankHead scratch scratchHead)) =
      config state input sourceHead output rank rankHead marks marksHead scratch scratchHead := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankScalar.scalarConfig, config, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RankScalar.scalarConfig, config, Fin.addCases]

theorem scalar_run (p : Machine 2 4) (fuel : ℕ) (state finalState : Fin 4)
    (input output rank marks scratch nextRank nextScratch : List Bool)
    (sourceHead rankHead marksHead scratchHead nextRankHead nextScratchHead : ℕ)
    (base : ExecutionReceipt 2 4)
    (hb : runFrom p fuel (RankScalar.scalarConfig state rank rankHead scratch scratchHead) = some base)
    (hf : base.final = RankScalar.scalarConfig finalState nextRank nextRankHead nextScratch nextScratchHead) :
    ∃ r : ExecutionReceipt 5 4,
      runFrom (scalarMachine p) fuel
        (config state input sourceHead output rank rankHead marks marksHead scratch scratchHead) = some r ∧
      r.final = config finalState input sourceHead output nextRank nextRankHead marks marksHead nextScratch nextScratchHead ∧
      r.steps = base.steps ∧ r.peakTapeCells = base.peakTapeCells + input.length + output.length + marks.length := by
  have he := TapeEmbedding.run_embed p ![sourceHead, output.length, marksHead] ![input, output, marks] _ _ base hb
  have hr := TapeRenaming.run_rename scalarLayout (TapeEmbedding.machine 3 p) _ _ _ he
  refine ⟨TapeRenaming.receipt scalarLayout
    (TapeEmbedding.receipt ![sourceHead, output.length, marksHead] ![input, output, marks] base),
    by simpa only [scalarMachine, scalar_config] using hr, ?_, rfl, ?_⟩
  · change TapeRenaming.config scalarLayout (TapeEmbedding.config (e := 3) _ _ base.final) = _
    rw [hf, scalar_config]
  · change base.peakTapeCells + TapeEmbedding.extraCells ![input, output, marks] = _
    simp [TapeEmbedding.extraCells, Fin.sum_univ_succ]
    omega

end NearCubicWires.RepairOrdinary.RankPlacement
