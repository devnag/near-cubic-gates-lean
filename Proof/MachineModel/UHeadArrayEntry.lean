import Proof.MachineModel.UHeadArray
import Proof.PCP.VerifierDecodingCap

/-! Remove proof-only zero backing at head-array entry, while retaining the
actual decoder-produced capped tape-count driver at head one. -/
namespace NearCubicWires.RepairOrdinary.UHeadArray
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev states := Fintype.card (RepeatMachine.Control 5)
def capacity (w : ℕ) : Fin 5 → ℕ := ![w,0,0,2*w+1,0]
def driverCapacity (c : ℕ) : Fin 5 → ℕ := ![0,0,0,0,c+2]
noncomputable def blankEntry (w t c : ℕ) : Configuration 5 states :=
  ⟨machine.start,![0,0,0,0,1],![[],List.replicate w true,[],[],CapMachine.counter c t]⟩
noncomputable def endpoint (w t c : ℕ) : Configuration 5 states :=
  ZeroPadding.config (driverCapacity c) (RepeatMachine.cfg 3 (source w (fields w t)) t 1)

theorem padded_entry (w t c : ℕ) :
    ZeroPadding.config (capacity w) (blankEntry w t c)=
      ZeroPadding.config (driverCapacity c) (RepeatMachine.cfg 0 (source w []) t 1) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,blankEntry,RepeatMachine.cfg,source,
      MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases]
  · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,driverCapacity,blankEntry,
      RepeatMachine.cfg,source,MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases,
      CapMachine.counter,CompareMachine.word,ZeroPadding.pad]

theorem endpoint_heads (w t c : ℕ) :
    (endpoint w t c).heads=![0,0,(fields w t).length,0,1] := by
  funext i; fin_cases i <;> rfl

theorem blank_run (w t c : ℕ) :
    ∃ r,runFrom machine (budget w t) (blankEntry w t c)=some r ∧ r.steps≤budget w t ∧
      r.final.heads=![0,0,(fields w t).length,0,1] ∧
      ZeroPadding.config (capacity w) r.final=endpoint w t c ∧ r.final.tapes 2=fields w t := by
  obtain ⟨base,hb,hs,hf⟩ := repeated_run w t
  obtain ⟨p,hp,hpf,hps,_⟩ := ZeroPadding.run_config machine (driverCapacity c) _ _ base hb
  rw [←padded_entry] at hp
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad machine (capacity w) _ _ p hp
  have hend : ZeroPadding.config (capacity w) r.final=endpoint w t c := by
    rw [hrf,hpf,hf]
    rfl
  have hh := congrArg Configuration.heads hend
  change r.final.heads=(endpoint w t c).heads at hh
  rw [endpoint_heads] at hh
  refine ⟨r,hr,hrs.trans_le (hps.trans_le hs),hh,hend,?_⟩
  have ht := congrArg (fun d => d.tapes 2) hend
  simpa [ZeroPadding.config,capacity,endpoint,driverCapacity,RepeatMachine.cfg,source,
    MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases] using ht

end NearCubicWires.RepairOrdinary.UHeadArray
