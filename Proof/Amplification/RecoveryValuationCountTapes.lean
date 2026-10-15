import Proof.Amplification.RecoveryValuationTableResult

/-! Literal capped-count and table-loop layout on ten tapes. The count
parser writes the very ninth-tape driver consumed by the repeat machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def cfg {s : Nat} (d : Data) (count cap : Nat) (q : Fin s) : Configuration 10 s :=
  TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word cap)
    (TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word count) (d.cfg q))
def counted (d : Data) (count : Nat) : Data := {d with pos:=d.pos+2*count+2}
def slots : Fin 3→Fin 10 := ![0,8,9]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def countMachine := RecoveryFocus.machine slots RecoveryCertificateCount.machine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem count_input (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length) :
    RecoveryFocus.config slots (cfg d 0 cap (0 : Fin 5)).heads (cfg d 0 cap (0 : Fin 5)).tapes
      (RecoveryCertificateCount.scan 0 (pre++frame word) pre.length 0 cap)=cfg d 0 cap 0 := by
  apply focus_configuration slots slots_injective
  · rfl
  · intro j; fin_cases j <;> simp [RecoveryCertificateCount.scan,RecoveryCertificateCount.cfg,cfg,Data.cfg,TapeEmbedding.config,Fin.addCases,slots,hp]
  · intro j; fin_cases j <;> simp [RecoveryCertificateCount.scan,RecoveryCertificateCount.cfg,cfg,Data.cfg,TapeEmbedding.config,Fin.addCases,slots,hs]
  · intro i _; rfl
  · intro i _; rfl

theorem count_output (d : Data) (pre word : List Bool) (count cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length) :
    RecoveryFocus.config slots (cfg d 0 cap (0 : Fin 5)).heads (cfg d 0 cap (0 : Fin 5)).tapes
      (RecoveryCertificateCount.cfg 3 (pre++frame word) (pre.length+2*count+2) count cap 1)=
      cfg (counted d count) count cap 3 := by
  apply focus_configuration slots slots_injective
  · rfl
  · intro j; fin_cases j <;> simp [RecoveryCertificateCount.cfg,cfg,Data.cfg,counted,TapeEmbedding.config,Fin.addCases,slots,hp]
  · intro j; fin_cases j <;> simp [RecoveryCertificateCount.cfg,cfg,Data.cfg,counted,TapeEmbedding.config,Fin.addCases,slots,hs]
  · intro i hi
    fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  · intro i hi
    fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl)

theorem count_run (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length) :
    ∃ r : ExecutionReceipt 10 5,
      runFrom countMachine (3*cap+3) (cfg d 0 cap 0)=some r ∧ r.steps≤3*cap+3 ∧
      (r.final.control=3 ↔ (readCount cap word).isSome=true) ∧
      ∀ count rest,readCount cap word=some (count,rest) →
        count≤cap ∧ r.final=cfg (counted d count) count cap 3 := by
  obtain ⟨base,hr,ht,hc,hf⟩ := RecoveryCertificateCount.bounded_witness cap pre word
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config slots slots_injective
    RecoveryCertificateCount.machine (cfg d 0 cap (0 : Fin 5)).heads (cfg d 0 cap (0 : Fin 5)).tapes _ _ base hr
  rw [count_input d pre word cap hs hp] at hrun
  refine ⟨r,hrun,by rw [hsteps]; exact ht,?_,?_⟩
  · simpa only [hfinal,RecoveryFocus.config] using hc
  · intro count rest hparse
    obtain ⟨hcap,hout⟩ := hf count rest hparse
    refine ⟨hcap,?_⟩
    rw [hfinal,hout]
    exact count_output d pre word count cap hs hp

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
