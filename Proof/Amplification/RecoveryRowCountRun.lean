import Proof.Amplification.RecoveryRowCountMachine

/-! Complete retained count-relation scan and its reusable ordinary call,
including both overflow checks, all head rewinds and output-bit overwrite. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowCounts
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scan_trace (parent left right preParent preLeft preRight : List Bool) (s : State) (old : Bool)
    (hl : parent.length=left.length) (hr : left.length=right.length) :
    Timed machine (2*parent.length+1)
      (cfg (scanCode s) (preParent++frame parent) (preLeft++frame left) (preRight++frame right)
        preParent.length preLeft.length preRight.length old)
      (cfg haltCode (preParent++frame parent) (preLeft++frame left) (preRight++frame right)
        (preParent.length+2*parent.length) (preLeft.length+2*left.length) (preRight.length+2*right.length)
        (finish (iterate parent left right s))) := by
  induction parent generalizing left right preParent preLeft preRight s with
  | nil =>
    have hleft : left=[] := List.length_eq_zero_iff.mp hl.symm
    have hright : right=[] := List.length_eq_zero_iff.mp (hr.symm.trans hl.symm)
    subst left; subst right
    have h := stop_step s (preParent++frame []) (preLeft++frame []) (preRight++frame [])
      preParent.length preLeft.length preRight.length old (by
        simpa only [frame] using Streaming.read_append preParent [] false)
    simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero,iterate] using
      Timed.single (scan_halted s) h
  | cons p ps ih =>
    cases left with
    | nil => simp at hl
    | cons l ls =>
      cases right with
      | nil => simp at hr
      | cons r rs =>
        let psrc := preParent++frame (p::ps)
        let lsrc := preLeft++frame (l::ls)
        let rsrc := preRight++frame (r::rs)
        have htail : Timed machine (2*ps.length+1)
            (cfg (scanCode (advance s p l r)) psrc lsrc rsrc
              (preParent.length+2) (preLeft.length+2) (preRight.length+2) old)
            (cfg haltCode psrc lsrc rsrc (preParent.length+2*(p::ps).length)
              (preLeft.length+2*(l::ls).length) (preRight.length+2*(r::rs).length)
              (finish (iterate ps ls rs (advance s p l r)))) := by
          convert ih ls rs (preParent++[true,p]) (preLeft++[true,l]) (preRight++[true,r])
            (advance s p l r) (by simpa using hl) (by simpa using hr) using 1 <;>
            simp [psrc,lsrc,rsrc,frame,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm]
        have hmarker := marker_step s psrc lsrc rsrc preParent.length preLeft.length preRight.length old (by
          simpa only [psrc,frame,List.append_assoc] using Streaming.read_append preParent (p::frame ps) true)
        have hp : readTapeBit psrc (preParent.length+1)=p := by
          simpa [psrc,frame,List.append_assoc] using Streaming.read_append (preParent++[true]) (frame ps) p
        have hl' : readTapeBit lsrc (preLeft.length+1)=l := by
          simpa [lsrc,frame,List.append_assoc] using Streaming.read_append (preLeft++[true]) (frame ls) l
        have hr' : readTapeBit rsrc (preRight.length+1)=r := by
          simpa [rsrc,frame,List.append_assoc] using Streaming.read_append (preRight++[true]) (frame rs) r
        have hbit := bit_step s psrc lsrc rsrc (preParent.length+1) (preLeft.length+1) (preRight.length+1)
          old p l r hp hl' hr'
        have hb := Timed.single (bit_halted s) hbit
        have ht := (Timed.single (scan_halted s) hmarker).trans (hb.trans htail)
        have htime : 1+(1+(2*ps.length+1))=2*(p::ps).length+1 := by simp only [List.length_cons]; omega
        rw [htime] at ht
        simpa only [psrc,lsrc,rsrc,iterate] using ht

def input (parent left right : List Bool) (old : Bool) : Fin 4→List Bool :=
  ![frame parent,frame left,frame right,[old]]
def relation (parent left right : List Bool) : Bool :=
  value parent==value left+value right &&
    (value left==value right || value left==value right+1) && decide (0<value right)

theorem raw_run (parent left right : List Bool) (old : Bool)
    (hl : parent.length=left.length) (hr : left.length=right.length) :
    ∃ r,run machine (2*parent.length+1) (input parent left right old)=some r ∧
      r.final.tapes=input parent left right (relation parent left right) ∧ r.steps=2*parent.length+1 := by
  have h := scan_trace parent left right [] [] [] initial old hl hr
  obtain ⟨r,hrun,hf,hsteps⟩ := h.run halt_halted
  refine ⟨r,?_,?_,hsteps⟩
  · have hi : cfg (scanCode initial) ([]++frame parent) ([]++frame left) ([]++frame right) 0 0 0 old=
        initialConfiguration machine (input parent left right old) := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    simp only [List.length_nil] at hrun
    rw [hi] at hrun
    exact hrun
  · rw [hf]
    change input parent left right (finish (iterate parent left right initial))=_
    rw [finish_iterate parent left right hl hr]
    rfl

noncomputable def reusableMachine := Rewind.machine machine

theorem counts_ready (parent left right : List Bool) (old : Bool) (capacity : Nat)
    (hl : parent.length=left.length) (hr : left.length=right.length) :
    ReadyRun reusableMachine (4*parent.length+4)
      ![frame parent,frame left,frame right,[old],List.replicate capacity false]
      ![frame parent,frame left,frame right,[relation parent left right],
        List.replicate (max capacity (2*parent.length+1)) false] := by
  obtain ⟨base,hrun,hf,hs⟩ := raw_run parent left right old hl hr
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace machine _ _ base hrun capacity
  have he : 2*base.steps+2=4*parent.length+4 := by rw [hs]; omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · exact (ht 0).trans (congrFun hf 0)
    · exact (ht 1).trans (congrFun hf 1)
    · exact (ht 2).trans (congrFun hf 2)
    · exact (ht 3).trans (congrFun hf 3)
    · convert hc using 1 <;> simp only [hs] <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryRowCounts
