import Proof.Amplification.RecoveryFormulaPayload

/-! The concrete three-way normalized-projection selector. The original
projection code and decoded tag remain framed; the paid lookup supplies one
raw bit. Two tag bits choose positive, negated, or constant evaluation. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionSelect
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def result (tag code : List Bool) (picked : Bool) :=
  if readTapeBit tag 1 then readTapeBit code 0 else if readTapeBit tag 0 then !picked else picked
def source (tag code : List Bool) (picked out : Bool) : Fin 4→List Bool :=
  ![frame tag,frame code,[picked],[out]]
def cfg (q : Fin 7) (tag code : List Bool) (picked out : Bool) (tagPos codePos : Nat) : Configuration 4 7 :=
  ⟨q,![tagPos,codePos,0,0],source tag code picked out⟩

def raw : Machine 4 7 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=6
  rule := fun q scan=>match q.val with
    | 0 => some ⟨1,fun _=>none,![.right,.right,.stay,.stay]⟩
    | 1 => some ⟨if scan 0 then 3 else 2,fun _=>none,![.right,.stay,.stay,.stay]⟩
    | 2 => some ⟨4,fun _=>none,![.right,.stay,.stay,.stay]⟩
    | 3 => some ⟨5,fun _=>none,![.right,.stay,.stay,.stay]⟩
    | 4 => some ⟨6,![none,none,none,some (if scan 0 then scan 1 else scan 2)],fun _=>.stay⟩
    | 5 => some ⟨6,![none,none,none,some (if scan 0 then scan 1 else !(scan 2))],fun _=>.stay⟩
    | _ => none

theorem first_step (tag code : List Bool) (picked old : Bool) :
    step raw (cfg 0 tag code picked old 0 0)=some (cfg 1 tag code picked old 1 1) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem tag_step (tag code : List Bool) (picked old : Bool) :
    step raw (cfg 1 tag code picked old 1 1)=
      some (cfg (if readTapeBit tag 0 then 3 else 2) tag code picked old 2 1) := by
  have ht := RecoveryColdPaddedCopy.frame_data tag 0
  simp only [Nat.mul_zero,Nat.zero_add] at ht
  simp only [step,raw,cfg,Configuration.scanned,source,Matrix.cons_val_zero,ht]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem second_step (tag code : List Bool) (picked old : Bool) :
    step raw (cfg (if readTapeBit tag 0 then 3 else 2) tag code picked old 2 1)=
      some (cfg (if readTapeBit tag 0 then 5 else 4) tag code picked old 3 1) := by
  cases h : readTapeBit tag 0
  all_goals apply congrArg some
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem output_step (tag code : List Bool) (picked old : Bool) :
    step raw (cfg (if readTapeBit tag 0 then 5 else 4) tag code picked old 3 1)=
      some (cfg 6 tag code picked (result tag code picked) 3 1) := by
  have ht := RecoveryColdPaddedCopy.frame_data tag 1
  have hc := RecoveryColdPaddedCopy.frame_data code 0
  simp only [Nat.mul_zero,Nat.zero_add] at hc
  cases h0 : readTapeBit tag 0
  all_goals simp only [Bool.false_eq_true,if_false,if_true,step,raw,cfg,Configuration.scanned,
    source,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,ht,hc]
  all_goals apply congrArg some
  all_goals apply configuration_ext
  all_goals first | rfl | skip
  all_goals simp only [result,h0,Bool.false_eq_true,if_false,if_true]
  all_goals funext i; fin_cases i <;> simp [applyAction,writeTapeBit,readTapeBit,List.getD]

theorem raw_run (tag code : List Bool) (picked old : Bool) : ∃ r,
    run raw 4 (source tag code picked old)=some r ∧
      r.final.tapes=source tag code picked (result tag code picked) ∧ r.steps=4 := by
  have h0 := Timed.single (by rfl) (first_step tag code picked old)
  have h1 := Timed.single (by rfl) (tag_step tag code picked old)
  have h2 := Timed.single (by cases readTapeBit tag 0 <;> rfl) (second_step tag code picked old)
  have h3 := Timed.single (by cases readTapeBit tag 0 <;> rfl) (output_step tag code picked old)
  obtain ⟨r,hr,hf,hs⟩ := (h0.trans (h1.trans (h2.trans h3))).run (by rfl)
  have hstart : cfg 0 tag code picked old 0 0=initialConfiguration raw (source tag code picked old) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hstart] at hr
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

def machine := Rewind.machine raw

theorem ready (tag code : List Bool) (picked old : Bool) :
    ClockJoin.ReadyRun machine 10 ![frame tag,frame code,[picked],[old],[]]
      ![frame tag,frame code,[picked],[result tag code picked],List.replicate 4 false] := by
  obtain ⟨base,hbase,hbt,hbs⟩ := raw_run tag code picked old
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw 4
    (source tag code picked old) base hbase 0
  have he : 2*base.steps+2=10 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,by omega⟩
  · convert hr using 2 <;> first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hbt,source] using ht 0
    · simpa [hbt,source] using ht 1
    · simpa [hbt,source] using ht 2
    · simpa [hbt,source] using ht 3
    · simpa [hbs] using hcounter

end NearCubicWires.RepairSource.RecoveryProjectionSelect
