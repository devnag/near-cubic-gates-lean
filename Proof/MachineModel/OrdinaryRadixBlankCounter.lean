import Proof.MachineModel.OrdinaryRadixSort
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! The actual sorter with a fresh empty counter tape. Counter cells are
allocated by the existing executed writes, so no initialization pass is needed.
The record stream and unary width still come from the actual caller. -/
namespace NearCubicWires.RepairOrdinary.RadixBlankCounter
open LocalBitMultitape StablePartition RadixWorkspace RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (capacity : ℕ) : Fin 5 → ℕ := fun i => if i.val = 3 then 2 * capacity else 0

def tapes {capacity : ℕ} {rs : List Record} (w : State capacity rs) (width : ℕ) :
    Fin 5 → List Bool := fun i => if i.val = 3 then [] else
      (RadixIteration.boundary w false 0 width).tapes i

theorem padded_initial {capacity : ℕ} {rs : List Record} (w : State capacity rs) (width : ℕ) :
    ZeroPadding.config (capacities capacity) (initialConfiguration RadixIteration.machine (tapes w width)) =
      initialConfiguration RadixIteration.machine (RadixIteration.boundary w false 0 width).tapes := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;>
      simp [ZeroPadding.config, capacities, tapes, initialConfiguration,
        RadixIteration.boundary, UnaryController.boundary, State.phaseTapes, State.tapes,
        layout, Fin.addCases, ZeroPadding.pad]

theorem sort_run {capacity : ℕ} {rs : List Record} (w : State capacity rs)
    (width : ℕ) (hw : ∀ r ∈ rs, (word r).length = width) :
    ∃ sorted : List Record, ∃ junk : List Bool, ∃ r : ExecutionReceipt 5 80,
      sorted.Perm rs ∧ sorted.Pairwise (fun a b => value (word a) ≤ value (word b)) ∧
      run RadixIteration.machine (width * (10 * (stream rs).length + 12) + 1)
        (tapes w width) = some r ∧
      r.final.tapes (RadixSort.outputTape width) = stream sorted ++ junk ∧
      (stream sorted).length + junk.length ≤ capacity ∧
      (∀ i : Fin 4, r.final.heads (i.castAdd 1) = 0) ∧
      r.final.tapes 4 = RadixIteration.driver width ∧ r.final.heads 4 = width ∧
      r.steps ≤ width * (10 * (stream rs).length + 12) + 1 ∧
      r.peakTapeCells ≤ 8 * capacity + width + 2 := by
  obtain ⟨sorted, junk, padded, hperm, hsorted, hr, hout, hfit, hh, hd, hdh, hs, hp⟩ :=
    RadixSort.sort_run w width hw
  have hrun : runFrom RadixIteration.machine (width * (10 * (stream rs).length + 12) + 1)
      (ZeroPadding.config (capacities capacity)
        (initialConfiguration RadixIteration.machine (tapes w width))) = some padded := by
    rw [padded_initial]
    exact hr
  obtain ⟨r, hactual, hf, hsteps, hpeak⟩ := ZeroPadding.run_unpad RadixIteration.machine
    (capacities capacity) _ _ padded hrun
  have hc : capacities capacity (RadixSort.outputTape width) = 0 := by
    unfold RadixSort.outputTape
    cases RadixIteration.finalPhase width false <;> rfl
  have he := congrArg (fun c => c.tapes (RadixSort.outputTape width)) hf
  simp only [ZeroPadding.config, hc, ZeroPadding.pad_zero] at he
  refine ⟨sorted, junk, r, hperm, hsorted, hactual, he.trans hout, hfit,
    ?_, ?_, ?_, hsteps.trans_le hs, hpeak.trans hp⟩
  · intro i
    exact (congrArg (fun c => c.heads (i.castAdd 1)) hf).trans (hh i)
  · have he4 := congrArg (fun c => c.tapes 4) hf
    change ZeroPadding.pad 0 (r.final.tapes 4) = padded.final.tapes 4 at he4
    rw [ZeroPadding.pad_zero] at he4
    exact he4.trans hd
  · exact (congrArg (fun c => c.heads 4) hf).trans hdh

end NearCubicWires.RepairOrdinary.RadixBlankCounter
