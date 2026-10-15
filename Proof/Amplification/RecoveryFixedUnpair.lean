import Proof.Amplification.RecoveryFixedUnpairLayout

/-! One actual ordinary unpair program returns both components in the same
binary field width as its input. Every call starts with framed input and
blank workspace; repeated scalar decoding therefore has a global width. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFixedUnpair
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev nativeStates := Fintype.card (RecoveryCalls.Control RecoveryUnpair.sizes) + 2
def sizes : Fin 4 → Nat := ![nativeStates, 8, 10, 10]
noncomputable def programs : (j : Fin 4) → Machine 21 (sizes j)
  | ⟨0, _⟩ => nativeMachine
  | ⟨1, _⟩ => widthMachine
  | ⟨2, _⟩ => leftMachine
  | ⟨3, _⟩ => rightMachine
  | ⟨n + 4, h⟩ => False.elim (by omega)

def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 21 → Bool) : Option (Fin 4) :=
  if j.val = 0 then some 1 else if j.val = 1 then some 2 else if j.val = 2 then some 3 else none

noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def time (bits : List Bool) :=
  ((unpairTime bits + 1 + (8 * bits.length + 8 + 1)) + (8 * bits.length + 10 + 1)) +
    (8 * bits.length + 10 + 1)

def budget (bits : List Bool) := 4096 * (bits.length + 1) ^ 2

theorem fixed_unpair_ready (bits : List Bool) : ReadyRun machine (time bits) (input bits) (output3 bits) := by
  have hn := (native_ready bits).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hw := (width_ready bits).call sizes programs 0 next 1 2 (by intro q; rfl)
  have hl := (left_ready bits).call sizes programs 0 next 2 3 (by intro q; rfl)
  have hr := (right_ready bits).stop sizes programs 0 next 3 (by intro q; rfl)
  have h := ((hn.trans hw).trans hl).trans hr
  have hin : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) (input bits)) =
      initialConfiguration machine (input bits) := by rfl
  rw [hin] at h
  obtain ⟨r, hrun, hf, hs⟩ := h.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
  exact ⟨r, hrun, by simp [hf, RecoveryCalls.stopped], by intro i; simp [hf, RecoveryCalls.stopped], hs⟩

theorem time_bound (bits : List Bool) : time bits ≤ budget bits := by
  have ht := RecoveryUnpair.raw_time_bound bits
  unfold time unpairTime budget
  nlinarith

theorem fixed_unpair_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 21 (Fintype.card (RecoveryCalls.Control sizes)),
      run machine (budget bits) (fun i => if i.val = 0 then frame bits else []) = some r ∧
      r.final.tapes 17 = frame (leftWord bits) ∧ r.final.tapes 18 = frame (rightWord bits) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ budget bits := by
  obtain ⟨r, hr, ht, hh, hs⟩ := fixed_unpair_ready bits
  have hmore := run_moreFuel machine (time bits) (budget bits - time bits) _ r hr
  rw [Nat.add_sub_of_le (time_bound bits)] at hmore
  exact ⟨r, hmore, by rw [ht]; rfl, by rw [ht]; rfl, hh, hs.le.trans (time_bound bits)⟩

theorem word_values (bits : List Bool) :
    value (leftWord bits) = (Nat.unpair (value bits)).1 ∧
      value (rightWord bits) = (Nat.unpair (value bits)).2 := by
  exact ⟨SignedSortKey.binary_value bits.length _ ((Nat.unpair_left_le _).trans_lt (value_lt bits)),
    SignedSortKey.binary_value bits.length _ ((Nat.unpair_right_le _).trans_lt (value_lt bits))⟩

theorem word_lengths (bits : List Bool) :
    (leftWord bits).length = bits.length ∧ (rightWord bits).length = bits.length := by
  simp [leftWord, rightWord]

noncomputable def leftProgram : Program where
  tapeCount := 21
  stateCount := Fintype.card (RecoveryCalls.Control sizes)
  twoTapes := by decide
  machine := machine
  outputTape := 17
  outputFresh := by decide

noncomputable def rightProgram : Program where
  tapeCount := 21
  stateCount := Fintype.card (RecoveryCalls.Control sizes)
  twoTapes := by decide
  machine := machine
  outputTape := 18
  outputFresh := by decide

noncomputable def leftWordFunction : RewoundWordFunction (List Bool) id
    (fun bits => frame (leftWord bits)) budget where
  program := leftProgram
  realizes := by
    intro bits
    obtain ⟨r, hr, hl, _⟩ := fixed_unpair_run bits
    exact ⟨r, hr, hl⟩
  headsReset := by
    intro bits receipt hrun
    obtain ⟨r, hr, _, _, hh, _⟩ := fixed_unpair_run bits
    have he : receipt = r := Option.some.inj (hrun.symm.trans hr)
    subst receipt
    exact hh

noncomputable def rightWordFunction : RewoundWordFunction (List Bool) id
    (fun bits => frame (rightWord bits)) budget where
  program := rightProgram
  realizes := by
    intro bits
    obtain ⟨r, hr, _, hrout, _⟩ := fixed_unpair_run bits
    exact ⟨r, hr, hrout⟩
  headsReset := by
    intro bits receipt hrun
    obtain ⟨r, hr, _, _, hh, _⟩ := fixed_unpair_run bits
    have he : receipt = r := Option.some.inj (hrun.symm.trans hr)
    subst receipt
    exact hh

end NearCubicWires.RepairOrdinary.RecoveryFixedUnpair
