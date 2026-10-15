import Proof.MachineModel.OrdinaryRankAppend

/-! The rank scan reuses its two width-sized scratch tapes. These are actual
applications of padding invariance, with exact final contents and charged
retained cells; neither stream cursor is reset. -/
namespace NearCubicWires.RepairOrdinary.RankWorkspace
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copyCapacity (width : ℕ) : Fin 3 → ℕ := fun i => if i.val = 2 then width else 0
def appendCapacity (width : ℕ) : Fin 4 → ℕ := fun i => if i.val = 3 then width else 0

def copyStart (pre bits suffix output : List Bool) : Configuration 3 3 :=
  ZeroPadding.config (copyCapacity bits.length)
    (RankRecordCopy.config 0 (pre ++ frame bits ++ suffix) pre.length output 0)

theorem copy_run (pre bits suffix output : List Bool) :
    ∃ r : ExecutionReceipt 3 3,
      runFrom RankRecordCopy.machine (2 * bits.length + 1) (copyStart pre bits suffix output) = some r ∧
      r.final = RankRecordCopy.config 2 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (output ++ Streaming.marks bits) bits.length ∧
      r.steps = 2 * bits.length + 1 ∧
      r.peakTapeCells ≤ (pre ++ frame bits ++ suffix).length + output.length + 4 * bits.length := by
  obtain ⟨base, hb, hf, hs, hp⟩ := RankRecordCopy.copy_run pre bits suffix output
  obtain ⟨r, hr, hrf, hrs, hrp⟩ := ZeroPadding.run_config RankRecordCopy.machine
    (copyCapacity bits.length) _ _ base hb
  refine ⟨r, hr, ?_, hrs.trans hs, ?_⟩
  · rw [hrf, hf]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, copyCapacity, RankRecordCopy.config, ZeroPadding.pad]
  · have hc : ZeroPadding.cells (copyCapacity bits.length) = bits.length := by
      simp [ZeroPadding.cells, copyCapacity, Fin.sum_univ_succ]
    rw [hc] at hrp
    omega

def appendStart (bits output : List Bool) : Configuration 4 3 :=
  ZeroPadding.config (appendCapacity bits.length)
    (RankAppend.config 0 bits 0 output bits.length 0 0)

theorem append_run (bits output : List Bool) :
    ∃ r : ExecutionReceipt 4 3,
      runFrom RankAppend.machine (2 * bits.length + 1) (appendStart bits output) = some r ∧
      r.final = RankAppend.config 2 bits bits.length (output ++ Streaming.marks bits ++ [false])
        0 bits.length bits.length ∧
      r.steps = 2 * bits.length + 1 ∧ r.peakTapeCells ≤ 6 * bits.length + output.length + 1 := by
  obtain ⟨base, hb, hf, hs, hp⟩ := RankAppend.append_run bits output
  obtain ⟨r, hr, hrf, hrs, hrp⟩ := ZeroPadding.run_config RankAppend.machine
    (appendCapacity bits.length) _ _ base hb
  refine ⟨r, hr, ?_, hrs.trans hs, ?_⟩
  · rw [hrf, hf]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, appendCapacity, RankAppend.config, ZeroPadding.pad]
  · have hc : ZeroPadding.cells (appendCapacity bits.length) = bits.length := by
      simp [ZeroPadding.cells, appendCapacity, Fin.sum_univ_succ]
    rw [hc] at hrp
    omega

end NearCubicWires.RepairOrdinary.RankWorkspace
