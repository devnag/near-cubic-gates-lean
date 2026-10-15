import Proof.MachineModel.ClockFloorLogRaw

/-! The code guard's exact sentinel unary floorLog2 N, with its required
head1. Source binary N is retained, and all rewind/reset work is charged. -/
namespace NearCubicWires.RepairOrdinary.ClockFloorLog
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reset : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,fun _ => none,
    fun i => if i.val=1 then .right else .stay⟩ else none
def rewound := Rewind.machine raw
def machine := Composition.machine rewound reset
def input (bits : List Bool) : Fin 3 → List Bool := ![frame bits,[],[]]

theorem entry_run (bits : List Bool) :
    ∃ r,run machine (4*bits.length+8) (input bits)=some r ∧
      r.final.tapes 0=frame bits ∧
      r.final.tapes 1=RepairSource.VerifierDecoding.CompareMachine.word (bits.length-1) ∧
      r.final.tapes 2=List.replicate (2*bits.length+2) false ∧
      r.final.heads=![0,1,0] ∧ r.steps=4*bits.length+8 := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run bits
  obtain ⟨first,hfirst,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw
    (2*bits.length+2) ![frame bits,[]] base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![frame bits,[]] (fun _ : Fin 1 => []))=input bits := by
    funext i; fin_cases i <;> rfl
  change run rewound (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![frame bits,[]] (fun _ : Fin 1 => []))=some first at hfirst
  have htime : 2*base.steps+2=4*bits.length+6 := by omega
  rw [hi,htime] at hfirst
  let c : Configuration 3 2 := ⟨1,![0,1,0],first.final.tapes⟩
  have he : Composition.restart first.final reset.start=initialConfiguration reset first.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · rfl
  have hreset : step reset (initialConfiguration reset first.final.tapes)=some c := by
    simp [step,reset,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨last,hl,hlf,hls⟩ := (Timed.single (by rfl) hreset).run (by rfl)
  rw [← he] at hl
  have h := Composition.run_join rewound reset (4*bits.length+6) 1 _ first last hfirst hl
  have htotal : 4*bits.length+6+1+1=4*bits.length+8 := by omega
  rw [htotal] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,?_,?_,?_,?_⟩
  · simpa [Composition.joinedReceipt,Composition.rightConfig,hlf,c,hf,config] using ht 0
  · simpa [Composition.joinedReceipt,Composition.rightConfig,hlf,c,hf,config] using ht 1
  · simpa [Composition.joinedReceipt,Composition.rightConfig,hlf,c,hs] using hcounter
  · simp [Composition.joinedReceipt,Composition.rightConfig,hlf,c]
  · dsimp only [Composition.joinedReceipt]
    omega

theorem floor_value (N : ℕ) : (ClockBinary.word N).length-1=Nat.log 2 N := by
  by_cases hn : N=0
  · simp [hn,ClockBinary.word]
  · rw [ClockBinary.length_log N (by omega)]
    omega

theorem binary_run (N : ℕ) :
    ∃ r,run machine (4*PCPResourceLedger.ell N+8) (input (ClockBinary.word N))=some r ∧
      r.final.tapes 0=frame (ClockBinary.word N) ∧
      r.final.tapes 1=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 N) ∧
      r.final.tapes 2=List.replicate (2*PCPResourceLedger.ell N+2) false ∧
      r.final.heads=![0,1,0] ∧ r.steps=4*PCPResourceLedger.ell N+8 := by
  have h := entry_run (ClockBinary.word N)
  rw [floor_value,ClockDyadicLedger.bit_width] at h
  exact h

end NearCubicWires.RepairOrdinary.ClockFloorLog
