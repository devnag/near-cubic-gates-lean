import Proof.PCP.PCPPairColdRun
import Proof.PCP.ProjectionDimensionTrim

/-! Paid canonical output for a positive padded binary field. The first
phase trims only high zero pairs, then resets; the second copies the raw
payload to a fresh output tape and resets. False payload bits are preserved. -/
namespace NearCubicWires.RepairOrdinary.CanonicalPositiveOutput
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def trimProgram : Machine 2 7 := Rewind.machine DimensionTrim.machine
def trimCost (pre : List Bool) (z : ℕ) := 2*(pre.length+1+z)+2*z+2

theorem trim_ready (pre : List Bool) (z : ℕ) :
    ClockJoin.ReadyRun trimProgram (2*trimCost pre z+2)
      ![frame (pre++[true]++List.replicate z false),[]]
      ![DimensionTrim.backTape pre 0 z,List.replicate (trimCost pre z) false] := by
  obtain ⟨base,hr,hf,hs⟩ := DimensionTrim.trim_run pre z
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace
    DimensionTrim.machine _ _ base hr 0
  have he : base.steps=trimCost pre z := hs
  rw [he] at hrun hsteps hc
  refine ⟨r,?_,?_,hh,hsteps.le⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hf,DimensionTrim.cfg] using ht 0
    · simpa using hc

theorem copy_padded (bits : List Bool) (z : ℕ) :
    ClockJoin.ReadyRun Streaming.machine (4*bits.length+2)
      ![frame bits++List.replicate z false,[],[]]
      ![frame bits++List.replicate z false,bits,List.replicate bits.length false] := by
  obtain ⟨base,hr,hf,hs,_⟩ := Streaming.copy_run bits
  let caps : Fin 3 → ℕ := ![(frame bits).length+z,0,0]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config Streaming.machine caps _ _ base hr
  have hi : ZeroPadding.config caps
      (initialConfiguration Streaming.machine (fun t => if t.val=0 then frame bits else []))=
      initialConfiguration Streaming.machine ![frame bits++List.replicate z false,[],[]] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,caps,initialConfiguration,ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs.le⟩
  · rw [hfinal,hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,caps,Streaming.finished,Streaming.config,ZeroPadding.pad]
  · intro i
    rw [hfinal,hf]
    simp [ZeroPadding.config,Streaming.finished,Streaming.config]

theorem back_tape (pre : List Bool) (z : ℕ) :
    DimensionTrim.backTape pre 0 z=frame (pre++[true])++List.replicate (2*z) false := by
  have hf : frame (pre++[true])=Streaming.marks (pre++[true])++[false] := by
    simpa [frame] using Streaming.frame_append (pre++[true]) []
  rw [hf]
  simp only [DimensionTrim.backTape,List.replicate_zero,Streaming.marks,List.flatMap_nil,List.append_nil,
    List.append_assoc]
  rw [show 2*z+1=1+2*z by omega,List.replicate_add]
  rfl

def trimSlots : Fin 2 → Fin 4 := ![0,1]
def copySlots : Fin 3 → Fin 4 := ![0,2,3]
theorem trim_injective : Function.Injective trimSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def trimPhase := RecoveryFocus.machine trimSlots trimProgram
noncomputable def copyPhase := RecoveryFocus.machine copySlots Streaming.machine
noncomputable def machine := Composition.machine trimPhase copyPhase
def input (bits : List Bool) : Fin 4 → List Bool := ![frame bits,[],[],[]]
def middle (pre : List Bool) (z : ℕ) : Fin 4 → List Bool :=
  ![DimensionTrim.backTape pre 0 z,List.replicate (trimCost pre z) false,[],[]]
def output (pre : List Bool) (z : ℕ) : Fin 4 → List Bool :=
  ![DimensionTrim.backTape pre 0 z,List.replicate (trimCost pre z) false,
    pre++[true],List.replicate (pre.length+1) false]

theorem trim_phase (pre : List Bool) (z : ℕ) :
    ClockJoin.ReadyRun trimPhase (2*trimCost pre z+2)
      (input (pre++[true]++List.replicate z false)) (middle pre z) := by
  have h := CompetitorRationalProducts.bounded_focus trimSlots trim_injective _ _ _
    (trim_ready pre z) (input (pre++[true]++List.replicate z false))
    (by intro i; fin_cases i <;> rfl)
  have he : install trimSlots (input (pre++[true]++List.replicate z false))
      ![DimensionTrim.backTape pre 0 z,List.replicate (trimCost pre z) false]=middle pre z := by
    funext i
    fin_cases i
    · exact install_slot trimSlots trim_injective _ _ 0
    · exact install_slot trimSlots trim_injective _ _ 1
    · exact install_other trimSlots _ _ _ (by decide)
    · exact install_other trimSlots _ _ _ (by decide)
  exact he ▸ h

theorem copy_phase (pre : List Bool) (z : ℕ) :
    ClockJoin.ReadyRun copyPhase (4*(pre.length+1)+2) (middle pre z) (output pre z) := by
  have hcopy := copy_padded (pre++[true]) (2*z)
  rw [←back_tape pre z] at hcopy
  simp only [List.length_append,List.length_singleton] at hcopy
  have h := CompetitorRationalProducts.bounded_focus copySlots copy_injective _ _ _ hcopy
    (middle pre z) (by intro i; fin_cases i <;> rfl)
  have he : install copySlots (middle pre z)
      ![DimensionTrim.backTape pre 0 z,pre++[true],List.replicate (pre.length+1) false]=output pre z := by
    funext i
    fin_cases i
    · exact install_slot copySlots copy_injective _ _ 0
    · exact install_other copySlots _ _ _ (by decide)
    · exact install_slot copySlots copy_injective _ _ 1
    · exact install_slot copySlots copy_injective _ _ 2
  exact he ▸ h

theorem output_run (pre : List Bool) (z : ℕ) :
    ClockJoin.ReadyRun machine (8*(pre.length+1+z)+9)
      (input (pre++[true]++List.replicate z false)) (output pre z) := by
  have h := ClockJoin.join _ _ _ _ _ _ _ (trim_phase pre z) (copy_phase pre z)
  convert h using 1
  · rfl
  · unfold trimCost
    omega

end NearCubicWires.RepairOrdinary.CanonicalPositiveOutput
