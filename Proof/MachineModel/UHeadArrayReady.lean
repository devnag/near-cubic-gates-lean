import Proof.MachineModel.UHeadArrayEntry

/-! The completed physical head-array producer also pays the final array
rewind. The decoder count head remains one and the width input is retained. -/
namespace NearCubicWires.RepairOrdinary.UHeadArray
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 5) : Bool := i.val==2
noncomputable def readyMachine := MaskedReset.machine machine selected
noncomputable def readyEntry (w t c : ℕ) := Rewind.recording (blankEntry w t c) 0
def readyCapacity (w : ℕ) : Fin 6 → ℕ :=
  fun i => Fin.addCases (capacity w) (fun _ : Fin 1 => 0) i

theorem ready_run (w t c : ℕ) :
    ∃ r,runFrom readyMachine (2*budget w t+2) (readyEntry w t c)=some r ∧
      r.steps≤2*budget w t+2 ∧ r.final.heads=![0,0,0,0,1,0] ∧
      r.final.tapes 1=List.replicate w true ∧ r.final.tapes 2=fields w t ∧
      r.final.tapes 4=CapMachine.counter c t ∧
      ∃ extra≤budget w t,
        (ZeroPadding.config (readyCapacity w) r.final).tapes=
          ![List.replicate w false,List.replicate w true,fields w t,List.replicate (2*w+1) false,
            CapMachine.counter c t,List.replicate extra false] := by
  obtain ⟨base,hb,hs,hh,hpad,hout⟩ := blank_run w t c
  obtain ⟨r,hr,hf,hrs,_⟩ := MaskedReset.reset_run machine selected (budget w t) (blankEntry w t c) base hb
    (by intro i hi
        have hi2 : i=2 := Fin.ext (by simpa [selected] using hi)
        subst i
        have h := SelectiveReset.prefix_head (prefix_of_run machine _ _ base hb).1 (2 : Fin 5)
        simpa [blankEntry] using h)
  have hm := runFrom_moreFuel readyMachine (2*base.steps+2)
    (2*budget w t+2-(2*base.steps+2)) _ r hr
  have hcost : 2*base.steps+2≤2*budget w t+2 := by omega
  rw [Nat.add_sub_of_le hcost] at hm
  have hend : r.final.heads=![0,0,0,0,1,0] := by
    rw [hf,hh]
    funext i; fin_cases i <;> rfl
  have hp (i : Fin 5) : ZeroPadding.pad (capacity w i) (base.final.tapes i)=(endpoint w t c).tapes i :=
    congrArg (fun d => d.tapes i) hpad
  have hwidth : base.final.tapes 1=List.replicate w true := by
    simpa [ZeroPadding.config,capacity,endpoint,driverCapacity,RepeatMachine.cfg,source,
      MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases] using hp 1
  have hcount : base.final.tapes 4=CapMachine.counter c t := by
    simpa [ZeroPadding.config,capacity,endpoint,driverCapacity,RepeatMachine.cfg,source,
      MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases,CapMachine.counter,
      CompareMachine.word] using hp 4
  refine ⟨r,hm,by omega,hend,?_,?_,?_,base.steps,hs,?_⟩
  · simpa [hf,SelectiveReset.finished,Rewind.config,Fin.addCases] using hwidth
  · simpa [hf,SelectiveReset.finished,Rewind.config,Fin.addCases] using hout
  · simpa [hf,SelectiveReset.finished,Rewind.config,Fin.addCases] using hcount
  · funext i
    fin_cases i
    all_goals simp [hf,ZeroPadding.config,readyCapacity,SelectiveReset.finished,Rewind.config,Fin.addCases]
    · simpa [ZeroPadding.config,capacity,endpoint,driverCapacity,RepeatMachine.cfg,source,
        MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases] using hp 0
    · simpa [capacity] using hwidth
    · simpa [capacity] using hout
    · simpa [ZeroPadding.config,capacity,endpoint,driverCapacity,RepeatMachine.cfg,source,
        MemoryEmitReady.config,controlConfig,TapeEmbedding.config,Fin.addCases] using hp 3
    · simpa [capacity] using hcount

end NearCubicWires.RepairOrdinary.UHeadArray
