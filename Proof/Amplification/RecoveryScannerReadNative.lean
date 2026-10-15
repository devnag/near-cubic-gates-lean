import Proof.Amplification.RecoveryRawViewEntryAcceptedPosition
import Proof.Amplification.RecoveryScannerPrepare

/-! The scanner consumes its native cold bank through the existing raw-view
reader. Only false count padding is omitted in the physical configuration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdScanner
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_run (bits word : List Bool) (k : Nat)
    (g : Fin 66→Nat) (a : Fin 66→List Bool)
    (hc : ZeroPadding.config (nativeCaps bits)
      ⟨RecoveryRawViewEntry.machine.start,g,a⟩=
        RecoveryRawViewEnd.cfg (view bits word (2*k)) 0 RecoveryRawViewEntry.machine.start) :
    ∃ r,runFrom RecoveryRawViewEntry.machine (RecoveryRawViewEntry.budget (view bits word (2*k)))
        ⟨RecoveryRawViewEntry.machine.start,g,a⟩=some r ∧
      r.steps≤536870912*(width bits+1)^4 ∧ r.final.heads 28=0 ∧
      r.final.tapes 28=[RecoveryRawViewEntry.answer (view bits word (2*k)) word k] ∧
      (RecoveryRawViewEntry.answer (view bits word (2*k)) word k=true →
        ∃ pos,r.final.heads 29=2*pos ∧ r.final.tapes 29=frame word) := by
  let x := view bits word (2*k)
  have hv := view_valid bits word (2*k)
  obtain ⟨base,hbase,hbound,hh,ht,hf⟩ := RecoveryRawViewEntry.entry_run x word k hv rfl rfl
  rw [←hc] at hbase
  obtain ⟨r,hr,he,hn,_⟩ := ZeroPadding.run_unpad RecoveryRawViewEntry.machine (nativeCaps bits)
    (RecoveryRawViewEntry.budget x) ⟨RecoveryRawViewEntry.machine.start,g,a⟩ base hbase
  have heh (i : Fin 66) : r.final.heads i=base.final.heads i := congrArg (fun c=>c.heads i) he
  have het (i : Fin 66) (hi : (nativeCaps bits) i=0) : r.final.tapes i=base.final.tapes i := by
    have hh := congrArg (fun c=>c.tapes i) he
    simpa only [ZeroPadding.config,hi,ZeroPadding.pad_zero] using hh
  refine ⟨r,hr,?_,(heh 28).trans hh,(het 28 rfl).trans ht,?_⟩
  · rw [hn]
    have hb := RecoveryRawViewEntry.budget_bound x hv
    rw [view_width] at hb
    exact hbound.trans hb
  · intro ha
    obtain ⟨pos,hs,hp⟩ := RecoveryRawViewEntry.accepted_position x word k hv rfl rfl ha
    refine ⟨pos,?_,?_⟩
    · rw [heh 29,hf ha]
      exact hp
    · rw [het 29 rfl,hf ha]
      exact hs

end NearCubicWires.RepairOrdinary.RecoveryColdScanner
