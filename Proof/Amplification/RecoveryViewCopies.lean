import Proof.Amplification.RecoveryViewWidth
import Proof.MachineModel.UWalkUnary

/-! Reuse the physically allocated reset log across the cold bank copies.
The three callees copy framed fields, raw erase drivers and unary caps. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem padded_ready (bits : List Bool) (width reset : Nat) :
    ReadyRun RecoveryColdPaddedCopy.machine (4*width+8)
      ![frame bits,[],CompareMachine.word width,List.replicate reset false]
      ![frame bits,frame (RecoveryColdPaddedCopy.data bits width),CompareMachine.word width,
        List.replicate (max reset (2*width+3)) false] := by
  obtain ⟨base,hbase,hbt,hsteps⟩ := RecoveryColdPaddedCopy.raw_run bits width
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace RecoveryColdPaddedCopy.raw
    (2*width+3) ![frame bits,[],CompareMachine.word width] base hbase reset
  have he : 2*base.steps+2=4*width+8 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hs.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hbt] using ht 0
    · simpa [hbt] using ht 1
    · simpa [hbt] using ht 2
    · simpa [hsteps] using hcounter

theorem erase_copy_ready (n reset : Nat) :
    ReadyRun ClockUnarySum.machine (2*n+6)
      ![List.replicate n true,[],[],List.replicate reset false]
      ![List.replicate n true,[],List.replicate n true,List.replicate (max reset (n+2)) false] := by
  obtain ⟨base,hbase,hf,hsteps⟩ := ClockUnarySum.raw_run n 0
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace ClockUnarySum.raw
    (n+0+2) ![List.replicate n true,List.replicate 0 true,[]] base hbase reset
  have he : 2*base.steps+2=2*n+6 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hs.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hf,ClockUnarySum.cfg] using ht 0
    · simpa [hf,ClockUnarySum.cfg] using ht 1
    · simpa [hf,ClockUnarySum.cfg] using ht 2
    · simpa [hsteps] using hcounter

def unaryMachine := UWalkUnary.machine true false
theorem unary_ready (n reset : Nat) :
    ReadyRun unaryMachine (2*n+6)
      ![CompareMachine.word n,[],List.replicate reset false]
      ![CompareMachine.word n,CompareMachine.word n,List.replicate (max reset (n+2)) false] := by
  obtain ⟨base,hbase,hf,hsteps⟩ := UWalkUnary.raw_run true false 0 n
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace (UWalkUnary.raw true false)
    (n+2) ![UWalkUnary.source 0 n,[]] base hbase reset
  have he : 2*base.steps+2=2*n+6 := by omega
  rw [he] at hr
  simp only [UWalkUnary.source,ZeroPadding.pad_zero] at hr
  refine ⟨r,?_,?_,hh,hs.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hf,UWalkUnary.cfg,UWalkUnary.source,ZeroPadding.pad_zero] using ht 0
    · simpa [hf,UWalkUnary.cfg,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word] using ht 1
    · simpa [hsteps] using hcounter

end NearCubicWires.RepairOrdinary.RecoveryColdView
