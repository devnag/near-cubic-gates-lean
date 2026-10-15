import Proof.Amplification.RecoveryValuationCountLookup
import Proof.MachineModel.OrdinaryCompare

/-! Reusable physical comparison for the binary committed-prefix guard.
The count and index remain binary: no loop expands either numeric value. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixCompare
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clear : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,![none,none,some false],fun _=>.stay⟩ else none

def startCfg {s : Nat} (q : Fin s) (left right : List Bool) (bit : Bool) : Configuration 3 s :=
  ⟨q,fun _=>0,![frame left,frame right,[bit]]⟩

theorem clear_run (left right : List Bool) (old : Bool) :
    ∃ r : ExecutionReceipt 3 2,runFrom clear 1 (startCfg 0 left right old)=some r ∧
      r.final=startCfg 1 left right false ∧ r.steps=1 := by
  have h : step clear (startCfg 0 left right old)=some (startCfg 1 left right false) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem padded_compare (left right : List Bool) (hw : left.length=right.length) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom Compare.machine (2*left.length+1) (startCfg Compare.machine.start left right false)=some r ∧
      r.final=Compare.config 4 (frame left) (frame right) (2*left.length) (2*right.length)
        [decide (value left≤value right)] ∧ r.steps=2*left.length+1 := by
  obtain ⟨base,hr,hf,hs,_⟩ := Compare.compare_run [] [] left right [] [] [] hw
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hr hf
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config Compare.machine ![0,0,1] _ _ base hr
  have hi : ZeroPadding.config ![0,0,1] (Compare.config (Compare.scanState true) (frame left) (frame right) 0 0 [])=
      startCfg Compare.machine.start left right false := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,ZeroPadding.pad,Compare.config,startCfg]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,ZeroPadding.pad,Compare.config]

def raw := Composition.machine clear Compare.machine
def machine := Rewind.machine raw

theorem raw_run (left right : List Bool) (old : Bool) (hw : left.length=right.length) :
    ∃ r : ExecutionReceipt 3 7,run raw (2*left.length+3) ![frame left,frame right,[old]]=some r ∧
      r.final.tapes=![frame left,frame right,[decide (value left≤value right)]] ∧ r.steps=2*left.length+3 := by
  obtain ⟨r0,hr0,hf0,ht0⟩ := clear_run left right old
  obtain ⟨r1,hr1,hf1,ht1⟩ := padded_compare left right hw
  have hq : runFrom Compare.machine (2*left.length+1) (Composition.restart r0.final Compare.machine.start)=some r1 := by
    rw [hf0]
    exact hr1
  have hr := Composition.run_join clear Compare.machine 1 (2*left.length+1) _ r0 r1 hr0 hq
  have hi : Composition.leftConfig 5 (startCfg 0 left right old)=initialConfiguration raw ![frame left,frame right,[old]] := by
    apply configuration_ext <;> rfl
  rw [hi] at hr
  have hn : 1+1+(2*left.length+1)=2*left.length+3 := by omega
  rw [hn] at hr
  refine ⟨Composition.joinedReceipt r0 r1,hr,?_,?_⟩
  · simp only [Composition.joinedReceipt,Composition.rightConfig,hf1,Compare.config]
  · simp only [Composition.joinedReceipt,ht0,ht1]
    omega

theorem compare_ready (count index : List Bool) (old : Bool) (capacity : Nat)
    (hw : count.length=index.length) :
    ReadyRun machine (4*count.length+8)
      ![frame count,frame index,[old],List.replicate capacity false]
      ![frame count,frame index,[decide (value count≤value index)],
        List.replicate (max capacity (2*count.length+3)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := raw_run count index old hw
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr capacity
  have he : 2*base.steps+2=4*count.length+8 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf] using ht 0
    · simpa [hf] using ht 1
    · simpa [hf] using ht 2
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryPrefixCompare
