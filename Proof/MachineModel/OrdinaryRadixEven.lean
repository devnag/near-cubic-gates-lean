import Proof.MachineModel.OrdinaryRadixBlankCounter

/-! Two full radix cycles return the sorted stream to a fixed physical tape.
This constant-factor choice keeps the interface independent of width parity. -/
namespace NearCubicWires.RepairOrdinary.RadixEven
open LocalBitMultitape StablePartition RadixWorkspace RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem records_add (a b : ℕ) (rs : List Record) :
    RadixIteration.records (a + b) rs = RadixIteration.records b (RadixIteration.records a rs) := by
  induction a generalizing rs with
  | zero => simp [RadixIteration.records]
  | succ a ih => simpa only [Nat.succ_add, RadixIteration.records] using ih (RadixRound.records rs)

theorem phase_even (width : ℕ) (phase : Bool) : RadixIteration.finalPhase (2 * width) phase = phase := by
  induction width generalizing phase with
  | zero => rfl
  | succ width ih =>
    rw [Nat.mul_add]
    change RadixIteration.finalPhase (2 * width) (!(!phase)) = phase
    simpa using ih phase

theorem even_sorted (width : ℕ) (rs : List Record)
    (hw : ∀ r ∈ rs, (word r).length = width) :
    (RadixIteration.records (2 * width) rs).Perm rs ∧
      (RadixIteration.records (2 * width) rs).Pairwise
        (fun a b => value (word a) ≤ value (word b)) := by
  obtain ⟨hp, _⟩ := sorted_permutation width rs hw
  have hwidth : ∀ r ∈ RadixIteration.records width rs, (word r).length = width :=
    fun r hr => hw r (hp.mem_iff.mp hr)
  obtain ⟨hq, hs⟩ := sorted_permutation width (RadixIteration.records width rs) hwidth
  have he : 2 * width = width + width := by omega
  rw [he, records_add]
  exact ⟨hq.trans hp, hs⟩

def fresh (rs : List Record) : State (stream rs).length rs where
  junk := []
  old := fun _ => []
  inputFit := by simp
  oldFit := by simp

def input (rs : List Record) (width : ℕ) : Fin 5 → List Bool :=
  fun i => if i.val = 0 then stream rs else if i.val = 4 then RadixIteration.driver (2 * width) else []

theorem padded_initial (rs : List Record) (width : ℕ) :
    ZeroPadding.config (RadixBlankCounter.capacities (stream rs).length)
      (initialConfiguration RadixIteration.machine (input rs width)) =
      initialConfiguration RadixIteration.machine
        (RadixIteration.boundary (fresh rs) false 0 (2 * width)).tapes := by
  have he : input rs width = RadixBlankCounter.tapes (fresh rs) (2 * width) := by
    funext i
    fin_cases i <;> simp [input, RadixBlankCounter.tapes, RadixIteration.boundary,
      UnaryController.boundary, State.phaseTapes, State.tapes, fresh, layout, Fin.addCases]
  rw [he]
  exact RadixBlankCounter.padded_initial (fresh rs) (2 * width)

theorem sort_run (rs : List Record) (width : ℕ)
    (hw : ∀ r ∈ rs, (word r).length = width) :
    ∃ sorted : List Record, ∃ r : ExecutionReceipt 5 80,
      sorted.Perm rs ∧ sorted.Pairwise (fun a b => value (word a) ≤ value (word b)) ∧
      run RadixIteration.machine (2 * width * (10 * (stream rs).length + 12) + 1)
        (input rs width) = some r ∧ r.final.tapes 0 = stream sorted ∧
      (∀ i : Fin 4, r.final.heads (i.castAdd 1) = 0) ∧
      r.steps ≤ 2 * width * (10 * (stream rs).length + 12) + 1 ∧
      r.peakTapeCells ≤ 8 * (stream rs).length + 2 * width + 2 := by
  obtain ⟨next, padded, hr, hf, hs, hp⟩ := RadixIteration.iteration_run (fresh rs) (2 * width)
  have hrun : runFrom RadixIteration.machine (2 * width * (10 * (stream rs).length + 12) + 1)
      (ZeroPadding.config (RadixBlankCounter.capacities (stream rs).length)
        (initialConfiguration RadixIteration.machine (input rs width))) = some padded := by
    rw [padded_initial]
    exact hr
  obtain ⟨r, hactual, hfinal, hsteps, hpeak⟩ := ZeroPadding.run_unpad RadixIteration.machine
    (RadixBlankCounter.capacities (stream rs).length) _ _ padded hrun
  obtain ⟨hperm, hsorted⟩ := even_sorted width rs hw
  have hfit := next.inputFit
  rw [RadixIteration.records_stream_length] at hfit
  have hjunk : next.junk = [] := List.length_eq_zero_iff.mp (by omega)
  have hout : padded.final.tapes 0 = stream (RadixIteration.records (2 * width) rs) := by
    rw [hf]
    simp [RadixIteration.finished, RadixIteration.boundary, UnaryController.boundary,
      phase_even, State.phaseTapes, State.tapes, layout, Fin.addCases, hjunk]
  have he := congrArg (fun c => c.tapes 0) hfinal
  change ZeroPadding.pad 0 (r.final.tapes 0) = padded.final.tapes 0 at he
  rw [ZeroPadding.pad_zero] at he
  refine ⟨RadixIteration.records (2 * width) rs, r, hperm, hsorted, hactual,
    he.trans hout, ?_, hsteps.trans_le hs, hpeak.trans hp⟩
  intro i
  have hh := congrArg (fun c => c.heads (i.castAdd 1)) hfinal
  rw [hf] at hh
  simpa only [ZeroPadding.config, RadixIteration.finished, RadixIteration.boundary,
    UnaryController.boundary, Fin.addCases_left] using hh

end NearCubicWires.RepairOrdinary.RadixEven
