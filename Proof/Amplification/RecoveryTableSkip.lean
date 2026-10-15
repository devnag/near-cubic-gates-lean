import Proof.Amplification.RecoveryTableSliceGraph

/-! The parsed row count drives actual table skipping. Each row uses the
already produced2W driver twice; no product counter is supplied for free. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTableSkip
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def body := Composition.machine (LookupWalk.machine .right) (LookupWalk.machine .right)
def bodyBudget (width : Nat) := 12*width+5
def source (word : List Bool) (width pos : Nat) : Configuration 2 8 :=
  Composition.leftConfig 4 (LookupWalk.cfg 0 word pos (2*width) 1)

theorem body_run (word : List Bool) (width pos : Nat) :
    ∃ r,runFrom body (bodyBudget width) (source word width pos)=some r ∧
      r.steps ≤ bodyBudget width ∧
      r.final.heads=(source word width (pos+8*width)).heads ∧
      r.final.tapes=(source word width (pos+8*width)).tapes := by
  obtain ⟨first,hfirst,hf,_⟩ := LookupWalk.walk_run .right word pos (2*width)
  have hpos : LookupWalk.shift .right pos (2*(2*width))=pos+4*width := by
    simp only [LookupWalk.shift]; omega
  rw [hpos] at hf
  obtain ⟨last,hlast,hl,_⟩ := LookupWalk.walk_run .right word (pos+4*width) (2*width)
  have hlastpos : LookupWalk.shift .right (pos+4*width) (2*(2*width))=pos+8*width := by
    simp only [LookupWalk.shift]; omega
  rw [hlastpos] at hl
  have hi : Composition.restart first.final (LookupWalk.machine .right).start=
      LookupWalk.cfg 0 word (pos+4*width) (2*width) 1 := by rw [hf]; rfl
  rw [←hi] at hlast
  have h := Composition.run_join (LookupWalk.machine .right) (LookupWalk.machine .right)
    (3*(2*width)+2) (3*(2*width)+2) _ first last hfirst hlast
  have hb : (3*(2*width)+2)+1+(3*(2*width)+2)=bodyBudget width := by unfold bodyBudget; omega
  rw [hb] at h
  let r := Composition.joinedReceipt first last
  refine ⟨r,h,runFrom_steps_le body (bodyBudget width) _ r h,?_,?_⟩
  · change last.final.heads=_
    rw [hl]; rfl
  · change last.final.tapes=_
    rw [hl]; rfl

def accepted (_ : Fin 8) (_ : Fin 2→Bool) := true
def advance (width pos : Nat) : Bool×Nat := (true,pos+8*width)
noncomputable def machine := RepeatMachine.machine body accepted
def budget (width total : Nat) := total*(12*width+8)+3

theorem iterate_advance (width total pos : Nat) :
    RepeatMachine.iterate (advance width) total pos=(true,pos+8*width*total) := by
  induction total generalizing pos with
  | zero=>simp [RepeatMachine.iterate]
  | succ n ih=>
    simp only [RepeatMachine.iterate,advance,if_true]
    rw [ih]
    congr 1
    ring

theorem skip_run (word : List Bool) (width total pos : Nat) :
    ∃ r,runFrom machine (budget width total)
        (RepeatMachine.cfg 0 (source word width pos) total 1)=some r ∧
      r.steps ≤ budget width total ∧
      r.final=RepeatMachine.cfg 3 (source word width (pos+8*width*total)) total 1 := by
  have hsupplier : ∀ p,True → ∃ r,runFrom body (bodyBudget width) (source word width p)=some r ∧
      r.steps ≤ bodyBudget width ∧
      r.final.heads=(source word width (advance width p).2).heads ∧
      r.final.tapes=(source word width (advance width p).2).tapes ∧
      accepted r.final.control r.final.scanned=(advance width p).1 ∧
      ((advance width p).1=true → True) := by
    intro p _
    obtain ⟨r,hr,hb,hh,ht⟩ := body_run word width p
    exact ⟨r,hr,hb,hh,ht,rfl,fun _=>True.intro⟩
  obtain ⟨r,hr,hb,hf⟩ := RepeatMachine.repeat_run body accepted (source word width)
    (advance width) (fun _=>True) (bodyBudget width) (by intro p _; rfl)
    hsupplier total pos True.intro
  have he : total*(bodyBudget width+3)+3=budget width total := by unfold bodyBudget budget; ring
  rw [he] at hr hb
  rw [iterate_advance] at hf
  exact ⟨r,hr,hb,hf⟩

end NearCubicWires.RepairOrdinary.RecoveryColdTableSkip
