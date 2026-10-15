import Proof.Amplification.RecoveryRootLoopModel

/-! Actual digit read, arithmetic call, and return to the moving stream
cursor in the single fixed outer machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRootIteration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_call (lo hi : Bool) (original stream : List Bool) (s : Store) (position : Nat)
    (hv : Valid s) :
    Timed machine (roundTime lo hi s + 1)
      (boundary (bodyLabel lo hi) original stream s position)
      (boundary 0 original stream (advance (lo, hi) s) position) := by
  let resultStore := advance (lo, hi) s
  obtain ⟨base, hr, ht, hh, hs⟩ := advance_ready (lo, hi) s hv
  obtain ⟨r, hrun, hf, hsteps⟩ := RecoveryFocus.run_config bodySlots bodySlots_injective
    (roundMachine lo hi) (heads position) (tapes original stream s) (roundTime lo hi s)
      (initialConfiguration (roundMachine lo hi) s.tapes) base hr
  have hin := body_config original stream s s position (initialConfiguration (roundMachine lo hi) s.tapes)
    (by intro i; rfl) rfl
  have hout := body_config original stream s (advance (lo, hi) s) position base.final hh ht
  rw [hin] at hrun
  rw [hout] at hf
  obtain ⟨hp, hhalt⟩ := prefix_of_run (RecoveryFocus.machine bodySlots (roundMachine lo hi)) _ _ r hrun
  let label := bodyLabel lo hi
  cases lo <;> cases hi
  all_goals
    have hb := RecoveryCalls.body_timed sizes programs 0 next label ⟨r.peakTapeCells, hp⟩
    rw [hsteps, hs] at hb
    have hret := RecoveryCalls.return_step sizes programs 0 next label 0 r.final hhalt (by rfl)
    have he : RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes =
        config (programs 0).start original stream resultStore position := by rw [hf]; rfl
    rw [he] at hret
    exact hb.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

theorem read_call (lo hi : Bool) (original pre rest : List Bool) (s : Store) :
    Timed machine 5
      (boundary 0 original (pre ++ frame (hi :: lo :: rest)) s pre.length)
      (boundary (bodyLabel lo hi) original (pre ++ frame (hi :: lo :: rest)) s (pre.length + 4)) := by
  obtain ⟨base, hr, hbase, hs⟩ := RecoveryRootDigitInput.digit_run pre rest lo hi
  obtain ⟨r, hrun, hf, hsteps⟩ := RecoveryFocus.run_config readerSlots readerSlots_injective
    RecoveryRootDigitInput.machine (heads pre.length) (tapes original (pre ++ frame (hi :: lo :: rest)) s)
    4 _ base hr
  rw [reader_config] at hrun
  rw [hbase, reader_config] at hf
  obtain ⟨hp, hhalt⟩ := prefix_of_run (programs 0) 4 _ r hrun
  have hb := RecoveryCalls.body_timed sizes programs 0 next 0 ⟨r.peakTapeCells, hp⟩
  rw [hsteps, hs] at hb
  have hret := RecoveryCalls.return_step sizes programs 0 next 0 (bodyLabel lo hi) r.final hhalt
    (by rw [hf]; cases lo <;> cases hi <;> rfl)
  have he : RecoveryCalls.restarted (programs (bodyLabel lo hi)) r.final.heads r.final.tapes =
      config (programs (bodyLabel lo hi)).start original (pre ++ frame (hi :: lo :: rest)) s (pre.length + 4) := by
    rw [hf]; rfl
  rw [he] at hret
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

theorem finish_call (original pre : List Bool) (s : Store) :
    Timed machine 2 (boundary 0 original (pre ++ [false]) s pre.length)
      (RecoveryCalls.stopped sizes (heads pre.length) (tapes original (pre ++ [false]) s)) := by
  obtain ⟨base, hr, hbase, hs⟩ := RecoveryRootDigitInput.finish_run pre
  obtain ⟨r, hrun, hf, hsteps⟩ := RecoveryFocus.run_config readerSlots readerSlots_injective
    RecoveryRootDigitInput.machine (heads pre.length) (tapes original (pre ++ [false]) s) 1 _ base hr
  rw [reader_config] at hrun
  rw [hbase, reader_config] at hf
  obtain ⟨hp, hhalt⟩ := prefix_of_run (programs 0) 1 _ r hrun
  have hb := RecoveryCalls.body_timed sizes programs 0 next 0 ⟨r.peakTapeCells, hp⟩
  rw [hsteps, hs] at hb
  have hret := RecoveryCalls.stop_step sizes programs 0 next 0 r.final hhalt (by rw [hf]; rfl)
  have he : RecoveryCalls.stopped sizes r.final.heads r.final.tapes =
      RecoveryCalls.stopped sizes (heads pre.length) (tapes original (pre ++ [false]) s) := by rw [hf]; rfl
  rw [he] at hret
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

theorem digit_call (lo hi : Bool) (original pre rest : List Bool) (s : Store) (hv : Valid s) :
    Timed machine (roundTime lo hi s + 6)
      (boundary 0 original (pre ++ frame (hi :: lo :: rest)) s pre.length)
      (boundary 0 original (pre ++ frame (hi :: lo :: rest)) (advance (lo, hi) s) (pre.length + 4)) := by
  have h := (read_call lo hi original pre rest s).trans
    (body_call lo hi original (pre ++ frame (hi :: lo :: rest)) s (pre.length + 4) hv)
  have he : 5 + (roundTime lo hi s + 1) = roundTime lo hi s + 6 := by omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryRootLoop
