import Proof.Amplification.RecoveryUnpairExecution

/-! Shared ordinary polynomial unpair supplier. Entry is a framed binary
word and entirely blank workspace; both padded binary components and all
head resets are obtained by one fixed finite local program. -/
namespace NearCubicWires.RepairOrdinary.RecoveryUnpair
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Rewind.machine rawMachine

def budget (bits : List Bool) := 2048 * (bits.length + 1) ^ 2

def leftWord (bits : List Bool) : List Bool :=
  SignedSortKey.binary (3 + 2 * bits.length) (Nat.unpair (value bits)).1

def rightWord (bits : List Bool) : List Bool :=
  SignedSortKey.binary (3 + 2 * bits.length) (Nat.unpair (value bits)).2

theorem result_words (bits : List Bool) :
    (resultStore bits).root = leftWord bits ∧ (resultStore bits).remainder = rightWord bits := by
  have hv := result_values bits
  have hleft := congrArg Prod.fst hv
  have hright := congrArg Prod.snd hv
  change value (resultStore bits).root = _ at hleft
  change value (resultStore bits).remainder = _ at hright
  obtain ⟨hl, hr⟩ := result_width bits
  constructor
  · have h := BoundedCounter.binary_of_value (resultStore bits).root
    rw [hl, hleft] at h
    exact h.symm
  · have h := BoundedCounter.binary_of_value (resultStore bits).remainder
    rw [hr, hright] at h
    exact h.symm

theorem unpair_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 16 (Fintype.card (RecoveryCalls.Control sizes) + 2),
      run machine (budget bits) (fun i => if i.val = 0 then frame bits else []) = some r ∧
      r.final.tapes 2 = frame (leftWord bits) ∧
      r.final.tapes 3 = frame (rightWord bits) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ budget bits := by
  obtain ⟨source, hr, ht, _, hs⟩ := raw_run bits
  obtain ⟨r, hrun, htapes, _, hh, hsteps, _⟩ :=
    Rewind.Workspace.reset_workspace rawMachine (rawTime bits) (input bits) source hr 0
  have hin : Fin.addCases (m := 15) (n := 1) (motive := fun _ => List Bool)
      (input bits) (fun _ => List.replicate 0 false) =
      (fun i : Fin 16 => if i.val = 0 then frame bits else []) := by
    funext i; fin_cases i <;> rfl
  rw [hin, hs] at hrun
  have htime : 2 * rawTime bits + 2 ≤ budget bits := by
    have hb := raw_time_bound bits
    unfold budget
    nlinarith [Nat.zero_le bits.length]
  have hmore := run_moreFuel machine (2 * rawTime bits + 2)
    (budget bits - (2 * rawTime bits + 2)) _ r hrun
  rw [Nat.add_sub_of_le htime] at hmore
  obtain ⟨hl, hr⟩ := result_words bits
  refine ⟨r, hmore, ?_, ?_, hh, ?_⟩
  · have h := htapes (2 : Fin 15)
    rw [ht] at h
    change r.final.tapes 2 = frame (resultStore bits).root at h
    rw [hl] at h
    exact h
  · have h := htapes (3 : Fin 15)
    rw [ht] at h
    change r.final.tapes 3 = frame (resultStore bits).remainder at h
    rw [hr] at h
    exact h
  · rw [hs] at hsteps
    exact hsteps.le.trans htime

theorem word_values (bits : List Bool) :
    value (leftWord bits) = (Nat.unpair (value bits)).1 ∧
      value (rightWord bits) = (Nat.unpair (value bits)).2 := by
  obtain ⟨hl, hr⟩ := result_words bits
  have hv := result_values bits
  rw [hl, hr] at hv
  exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩

theorem word_lengths (bits : List Bool) :
    (leftWord bits).length = 3 + 2 * bits.length ∧
      (rightWord bits).length = 3 + 2 * bits.length := by
  simp [leftWord, rightWord]

noncomputable def leftProgram : Program where
  tapeCount := 16
  stateCount := Fintype.card (RecoveryCalls.Control sizes) + 2
  twoTapes := by decide
  machine := machine
  outputTape := 2
  outputFresh := by decide

noncomputable def rightProgram : Program where
  tapeCount := 16
  stateCount := Fintype.card (RecoveryCalls.Control sizes) + 2
  twoTapes := by decide
  machine := machine
  outputTape := 3
  outputFresh := by decide

noncomputable def leftWordFunction : RewoundWordFunction (List Bool) id
    (fun bits => frame (leftWord bits)) budget where
  program := leftProgram
  realizes := by
    intro bits
    obtain ⟨r, hr, hl, _⟩ := unpair_run bits
    exact ⟨r, hr, hl⟩
  headsReset := by
    intro bits receipt hrun
    obtain ⟨r, hr, _, _, hh, _⟩ := unpair_run bits
    have he : receipt = r := Option.some.inj (hrun.symm.trans hr)
    subst receipt
    exact hh

noncomputable def rightWordFunction : RewoundWordFunction (List Bool) id
    (fun bits => frame (rightWord bits)) budget where
  program := rightProgram
  realizes := by
    intro bits
    obtain ⟨r, hr, _, hrout, _⟩ := unpair_run bits
    exact ⟨r, hr, hrout⟩
  headsReset := by
    intro bits receipt hrun
    obtain ⟨r, hr, _, _, hh, _⟩ := unpair_run bits
    have he : receipt = r := Option.some.inj (hrun.symm.trans hr)
    subst receipt
    exact hh

end NearCubicWires.RepairOrdinary.RecoveryUnpair
