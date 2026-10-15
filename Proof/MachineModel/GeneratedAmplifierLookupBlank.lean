import Proof.MachineModel.GeneratedAmplifierLookup
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! The lookup's reset workspace is physically blank at entry. Zero-padding
transport removes only its logical zero capacity; the output tape is exact. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Lookup
open LocalBitMultitape RadixSemantics RecoveryCommittedBit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entry (query source : List Bool) (pos : ℕ) :=
  (⟨machine.start,![0,0,0,pos,0],![frame query,[false],[],source,[false]]⟩ :
    Configuration 5 (Fintype.card (RecoveryCalls.Control sizes)))
def capacity (query : List Bool) : Fin 5→ℕ := fun i => if i=2 then 2*query.length+1 else 0

theorem blank_run (query pre skip : List Bool) (bit : Bool) (tail : List Bool)
    (hq : value query=skip.length) :
    ∃ r,runFrom machine (cost query.length skip.length)
      (entry query (pre++skip++bit::tail) pre.length)=some r ∧ r.steps≤cost query.length skip.length ∧
      r.final.tapes 4=[bit] ∧ r.final.heads 4=0 := by
  let d : Data := ⟨query,pre++skip++bit::tail,pre.length,false,false,2*query.length+1⟩
  obtain ⟨base,hb,hs,hout,hhead⟩ := lookup_run skip bit tail d pre rfl rfl hq (by rfl)
  have he : ZeroPadding.config (capacity query) (entry query (pre++skip++bit::tail) pre.length)=d.cfg machine.start := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,entry,d,Data.cfg,ZeroPadding.pad]
  rw [←he] at hb
  obtain ⟨r,hr,hf,ht,_⟩ := ZeroPadding.run_unpad machine (capacity query) _ _ base hb
  have ho := congrArg (fun cfg : Configuration 5 (Fintype.card (RecoveryCalls.Control sizes)) => cfg.tapes 4) hf
  have hh := congrArg (fun cfg : Configuration 5 (Fintype.card (RecoveryCalls.Control sizes)) => cfg.heads 4) hf
  refine ⟨r,hr,ht.le.trans hs,?_,?_⟩
  · simpa [ZeroPadding.config,capacity,hout] using ho
  · simpa [ZeroPadding.config,hhead] using hh

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Lookup
