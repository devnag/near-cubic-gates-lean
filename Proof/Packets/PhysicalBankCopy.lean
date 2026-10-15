import Proof.Packets.PhysicalSupportReturn
import Proof.MachineModel.Runs

/-! A fixed three-tape overwrite of a resident fixed-width bank, followed by
physical restoration of the source, target, and retained width cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace FixedLivePackets.PhysicalBankCopy
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch

def cfg (q : Fin 3) (width index driver : Nat)
    (sourcePre source sourcePost targetPre target targetPost : List Bool) : Configuration 3 3 :=
  ⟨q, ![driver,sourcePre.length+index,targetPre.length+index],
    ![UnaryTemplate.tape width,sourcePre++source++sourcePost,targetPre++target++targetPost]⟩

def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then some (if bits 0 then
      ⟨0,![none,none,some (bits 1)],fun _ => .right⟩ else
      ⟨1,fun _ => none,![.left,.stay,.stay]⟩)
    else if q.val=1 then some (if bits 0 then
      ⟨1,fun _ => none,fun _ => .left⟩ else
      ⟨2,fun _ => none,![.right,.stay,.stay]⟩)
    else none

theorem write_at (pre tail : List Bool) (before after : Bool) :
    writeTapeBit (pre++before::tail) pre.length after=pre++after::tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [writeTapeBit,ih]

theorem copy_step (pre rest oldRest sourcePre sourcePost targetPre targetPost : List Bool)
    (bit oldBit : Bool) :
    step machine (cfg 0 (pre++bit::rest).length pre.length (pre.length+1)
      sourcePre (pre++bit::rest) sourcePost targetPre (pre++oldBit::oldRest) targetPost)=
    some (cfg 0 (pre++bit::rest).length (pre.length+1) (pre.length+2)
      sourcePre (pre++bit::rest) sourcePost targetPre (pre++bit::oldRest) targetPost) := by
  have hw := UnaryTemplate.tape_mark (pre++bit::rest).length pre.length (by simp)
  simp only [List.length_append,List.length_cons] at hw
  have hr := Streaming.read_append (sourcePre++pre) (rest++sourcePost) bit
  simp only [List.length_append,List.append_assoc] at hr
  have ht := write_at (targetPre++pre) (oldRest++targetPost) oldBit bit
  simp only [List.length_append,List.append_assoc] at ht
  simp [step,machine,cfg,Configuration.scanned,hw,List.append_assoc,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i <;> simp [applyAction,ht]

theorem turn_step (width : Nat)
    (sourcePre source sourcePost targetPre target targetPost : List Bool) :
    step machine (cfg 0 width width (width+1) sourcePre source sourcePost targetPre target targetPost)=
      some (cfg 1 width width width sourcePre source sourcePost targetPre target targetPost) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_step (width pos : Nat) (h : pos<width)
    (sourcePre source sourcePost targetPre target targetPost : List Bool) :
    step machine (cfg 1 width (pos+1) (pos+1) sourcePre source sourcePost targetPre target targetPost)=
      some (cfg 1 width pos pos sourcePre source sourcePost targetPre target targetPost) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark width pos h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (width : Nat)
    (sourcePre source sourcePost targetPre target targetPost : List Bool) :
    step machine (cfg 1 width 0 0 sourcePre source sourcePost targetPre target targetPost)=
      some (cfg 2 width 0 1 sourcePre source sourcePost targetPre target targetPost) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem copy_prefix (pre rest old : List Bool) (h : old.length=rest.length)
    (sourcePre sourcePost targetPre targetPost : List Bool) :
    Timed machine (rest.length+1)
      (cfg 0 (pre++rest).length pre.length (pre.length+1)
        sourcePre (pre++rest) sourcePost targetPre (pre++old) targetPost)
      (cfg 1 (pre++rest).length (pre++rest).length (pre++rest).length
        sourcePre (pre++rest) sourcePost targetPre (pre++rest) targetPost) := by
  induction rest generalizing pre old with
  | nil =>
    have ho : old=[] := List.length_eq_zero_iff.mp (by simpa using h)
    subst old
    simpa using Timed.single (by rfl) (turn_step pre.length sourcePre pre sourcePost targetPre pre targetPost)
  | cons bit rest ih =>
    cases old with
    | nil => simp at h
    | cons oldBit oldRest =>
      have hh : oldRest.length=rest.length := by simpa using h
      have first := Timed.single (by rfl) (copy_step pre rest oldRest sourcePre sourcePost targetPre targetPost bit oldBit)
      have tail := ih (pre++[bit]) oldRest hh
      have whole := first.trans (by simpa [List.append_assoc] using tail)
      simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using whole

theorem return_prefix (width pos : Nat) (h : pos≤width)
    (sourcePre source sourcePost targetPre target targetPost : List Bool) :
    Timed machine (pos+1)
      (cfg 1 width pos pos sourcePre source sourcePost targetPre target targetPost)
      (cfg 2 width 0 1 sourcePre source sourcePost targetPre target targetPost) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (stop_step width sourcePre source sourcePost targetPre target targetPost)
  | succ pos ih =>
    exact Timed.step (by rfl) (back_step width pos (by omega) sourcePre source sourcePost targetPre target targetPost)
      (ih (by omega))

theorem copy_run (source old : List Bool) (h : old.length=source.length)
    (sourcePre sourcePost targetPre targetPost : List Bool) :
    ∃ r, runFrom machine (2*source.length+2)
      (cfg 0 source.length 0 1 sourcePre source sourcePost targetPre old targetPost)=some r ∧
      r.final=cfg 2 source.length 0 1 sourcePre source sourcePost targetPre source targetPost ∧
      r.steps=2*source.length+2 := by
  have first := copy_prefix [] source old h sourcePre sourcePost targetPre targetPost
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at first
  have back := return_prefix source.length source.length le_rfl sourcePre source sourcePost targetPre source targetPost
  have whole := first.trans back
  have time : source.length+1+(source.length+1)=2*source.length+2 := by omega
  rw [time] at whole
  exact whole.run (by rfl)

theorem copy_step_boundary (source old : List Bool) (h : old.length=source.length)
    (sourcePre sourcePost targetPre targetPost : List Bool) :
    Step machine (2*source.length+2)
      (cfg 0 source.length 0 1 sourcePre source sourcePost targetPre old targetPost).heads
      (cfg 0 source.length 0 1 sourcePre source sourcePost targetPre old targetPost).tapes
      (cfg 2 source.length 0 1 sourcePre source sourcePost targetPre source targetPost).heads
      (cfg 2 source.length 0 1 sourcePre source sourcePost targetPre source targetPost).tapes := by
  obtain ⟨r,hr,hf,hs⟩ := copy_run source old h sourcePre sourcePost targetPre targetPost
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩

theorem append_bit_step (pre rest sourcePre sourcePost targetPre : List Bool) (bit : Bool) :
    step machine (cfg 0 (pre++bit::rest).length pre.length (pre.length+1)
      sourcePre (pre++bit::rest) sourcePost targetPre pre [])=
      some (cfg 0 (pre++bit::rest).length (pre.length+1) (pre.length+2)
        sourcePre (pre++bit::rest) sourcePost targetPre (pre++[bit]) []) := by
  have hw := UnaryTemplate.tape_mark (pre++bit::rest).length pre.length (by simp)
  simp only [List.length_append,List.length_cons] at hw
  have hr := Streaming.read_append (sourcePre++pre) (rest++sourcePost) bit
  simp only [List.length_append,List.append_assoc] at hr
  simp [step,machine,cfg,Configuration.scanned,hw,List.append_assoc,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i
    · rfl
    · rfl
    · simpa [applyAction,List.append_assoc] using Streaming.write_append (targetPre++pre) bit

theorem append_prefix (pre rest sourcePre sourcePost targetPre : List Bool) :
    Timed machine (rest.length+1)
      (cfg 0 (pre++rest).length pre.length (pre.length+1)
        sourcePre (pre++rest) sourcePost targetPre pre [])
      (cfg 1 (pre++rest).length (pre++rest).length (pre++rest).length
        sourcePre (pre++rest) sourcePost targetPre (pre++rest) []) := by
  induction rest generalizing pre with
  | nil => simpa using Timed.single (by rfl) (turn_step pre.length sourcePre pre sourcePost targetPre pre [])
  | cons bit rest ih =>
    have first := Timed.single (by rfl) (append_bit_step pre rest sourcePre sourcePost targetPre bit)
    have tail := ih (pre++[bit])
    have whole := first.trans (by simpa [List.append_assoc] using tail)
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using whole

/-- The same fixed machine also allocates an initially empty target by actual
writes. This is the initialization boundary needed before reusable overwrites. -/
theorem append_run (source sourcePre sourcePost targetPre : List Bool) :
    ∃ r, runFrom machine (2*source.length+2)
      (cfg 0 source.length 0 1 sourcePre source sourcePost targetPre [] [])=some r ∧
      r.final=cfg 2 source.length 0 1 sourcePre source sourcePost targetPre source [] ∧
      r.steps=2*source.length+2 := by
  have first := append_prefix [] source sourcePre sourcePost targetPre
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at first
  have back := return_prefix source.length source.length le_rfl sourcePre source sourcePost targetPre source []
  have whole := first.trans back
  have time : source.length+1+(source.length+1)=2*source.length+2 := by omega
  rw [time] at whole
  exact whole.run (by rfl)

end FixedLivePackets.PhysicalBankCopy
