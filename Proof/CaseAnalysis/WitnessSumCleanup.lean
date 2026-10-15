import Proof.CaseAnalysis.WitnessSumWorkRun

/-! A successful sum returns the consumed field cursor, leaves the actual
count sentinel, and clears its one private bank with the same paid H
driver. Failed sums never enter this machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCleanup
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem count_heads_zero (counts : List Bool) (i : Fin 528) (hi : i≠526) :
    SumCountStream.heads counts i=0 := by
  revert hi
  refine Fin.addCases (m:=510) (n:=18) ?_ ?_ i
  · intro j _;simp only [SumCountStream.heads,Fin.addCases_left]
  · intro j hj
    have hn : j.val≠16 := by intro h;exact hj (Fin.ext (by change 510+j.val=526;omega))
    simp only [SumCountStream.heads,Fin.addCases_right,SumCountStream.extraHeads,if_neg hn]

theorem reset_heads (out native counts : List Bool) (i : Fin 526) :
    SumWork.heads 0 0 out native counts (SumReset.slots i)=0 := by
  refine Fin.addCases (m:=524) (n:=2) ?_ ?_ i
  · intro j
    simp only [SumReset.slots,Fin.addCases_left,SumReset.scratch]
    change SumDock.heads out native counts (SumDock.slots (SumReset.privateSlot j))=0
    rw [SumDock.heads_reader]
    exact count_heads_zero counts _ (by
      intro h
      have hn:=SumReset.private_not_retained j
      apply hn
      rw [h]
      exact Or.inr (Or.inr (Or.inr rfl)))
  · intro j
    fin_cases j <;> rfl

noncomputable def returned:=Composition.machine SumCursor.rewind (SumCursor.move .left)
noncomputable def machine:=Composition.machine returned SumReset.machine
def budget (H : ℕ):=4*H+9

theorem cleanup_run (H position : ℕ) (out native counts : List Bool) (input : Fin 3061 → List Bool)
    (hpos : position ≤ H) (hdriver : input 2530=List.replicate H true)
    (hlog : input 2531=List.replicate (H+1) false)
    (hbound : ∀ i,(input (SumReset.scratch i)).length ≤ H) :
    ∃ r,runFrom machine (budget H)
      ⟨machine.start,SumWork.heads position 1 out native counts,input⟩=some r ∧ r.steps ≤ budget H ∧
      r.final.heads=SumWork.heads 0 0 out native counts ∧
      (∀ i,r.final.tapes (SumReset.scratch i)=List.replicate H false) ∧
      r.final.tapes 2530=List.replicate H true ∧ r.final.tapes 2531=List.replicate (H+1) false ∧
      (∀ i,(∀ j,SumReset.slots j≠i) → r.final.tapes i=input i) := by
  obtain ⟨first,hfirst,fs,fh,ft⟩:=SumCursor.rewind_run H position (SumWork.heads position 1 out native counts) input
    hpos rfl rfl rfl hdriver hlog
  have firstHeads : first.final.heads=SumWork.heads 0 1 out native counts :=
    fh.trans (SumWork.position_update position 0 1 out native counts)
  obtain ⟨second,hsecond,ss,sh,st⟩:=SumCursor.move_run .left (SumWork.heads 0 1 out native counts) input
  have secondHeads : second.final.heads=SumWork.heads 0 0 out native counts := by
    rw [sh]
    exact SumWork.driver_update 0 1 0 out native counts
  have secondRun : runFrom (SumCursor.move .left) 1
      ⟨(SumCursor.move .left).start,first.final.heads,first.final.tapes⟩=some second := by
    rw [firstHeads,ft];exact hsecond
  obtain ⟨middle,hmiddle,ms,mh,mt⟩:=joined SumCursor.rewind (SumCursor.move .left) (2*H+2) 1
    _ _ first second hfirst secondRun (by omega) (by omega)
  have middleHeads : middle.final.heads=SumWork.heads 0 0 out native counts:=mh.trans secondHeads
  have middleTapes : middle.final.tapes=input:=mt.trans st
  obtain ⟨last,hlast,ls,lh,lt,ldriver,llog,lkeep⟩:=SumReset.reset_run H (SumWork.heads 0 0 out native counts) input
    (reset_heads out native counts) hdriver hlog hbound
  have lastRun : runFrom SumReset.machine (2*H+4)
      ⟨SumReset.machine.start,middle.final.heads,middle.final.tapes⟩=some last := by
    rw [middleHeads,middleTapes];exact hlast
  obtain ⟨r,run,rs,rh,rt⟩:=joined returned SumReset.machine (2*H+2+1+1) (2*H+4)
    _ _ middle last hmiddle lastRun ms ls
  have eq : (2*H+2+1+1)+1+(2*H+4)=budget H:=by unfold budget;omega
  rw [eq] at run rs
  refine ⟨r,run,rs,rh.trans lh,?_,?_,?_,?_⟩
  · intro i;rw [rt];exact lt i
  · rw [rt];exact ldriver
  · rw [rt];exact llog
  · intro i hi;rw [rt];exact lkeep i hi

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCleanup
