import Proof.Amplification.RecoveryValuationLoopTapes

/-! Final physical status write and the rejection layout of the capped
count reader, on the same ten tapes as the enclosing valuation scan. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem count_preserves_flag (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (r : ExecutionReceipt 10 5)
    (hr : runFrom countMachine (3*cap+3) (cfg d 0 cap 0)=some r) :
    r.final.heads 7=0 ∧ r.final.tapes 7=[d.valid] := by
  obtain ⟨base,hbase,_,_,_⟩ := RecoveryCertificateCount.bounded_witness cap pre word
  obtain ⟨other,hother,hfinal,_⟩ := RecoveryFocus.run_config slots slots_injective
    RecoveryCertificateCount.machine (cfg d 0 cap (0 : Fin 5)).heads (cfg d 0 cap (0 : Fin 5)).tapes _ _ base hbase
  rw [count_input d pre word cap hs hp] at hother
  change runFrom countMachine (3*cap+3) (cfg d 0 cap 0)=some other at hother
  rw [hr] at hother
  have he := Option.some.inj hother
  cases he
  have hnot : ¬∃ j,slots j=7 := by decide
  have h7 : RecoveryFocus.pick slots 7=none := by simp [RecoveryFocus.pick,hnot]
  simp [hfinal,RecoveryFocus.config,h7,cfg,TapeEmbedding.config,Fin.addCases,Data.cfg]

def flagMachine (bit : Bool) : Machine 10 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=7 then some bit else none,fun _=>.stay⟩ else none

theorem flag_run {s : Nat} (c : Configuration 10 s) (old bit : Bool)
    (hh : c.heads 7=0) (ht : c.tapes 7=[old]) :
    ∃ r : ExecutionReceipt 10 2,
      runFrom (flagMachine bit) 1 (RecoveryCalls.restarted (flagMachine bit) c.heads c.tapes)=some r ∧
      r.final=(⟨1,c.heads,Function.update c.tapes 7 [bit]⟩ : Configuration 10 2) ∧ r.steps=1 := by
  have hs : step (flagMachine bit) (RecoveryCalls.restarted (flagMachine bit) c.heads c.tapes)=
      some (⟨1,c.heads,Function.update c.tapes 7 [bit]⟩ : Configuration 10 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=7
      · subst i
        simp [applyAction,flagMachine,RecoveryCalls.restarted,hh,ht,writeTapeBit]
      · simp [applyAction,flagMachine,RecoveryCalls.restarted,hi]
  exact (Timed.single (by rfl) hs).run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
