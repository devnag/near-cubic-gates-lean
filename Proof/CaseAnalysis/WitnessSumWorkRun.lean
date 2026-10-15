import Proof.CaseAnalysis.WitnessSumWork
import Proof.CaseAnalysis.RowsCircuitBottomReturned
import Proof.Amplification.RecoveryFocusRetained

/-! Enter the actual term driver with one physical move, then run the
whole sum body. The head identities also provide the successful return
boundary without traversing any retained output prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
open private hole_outside from Proof.CaseAnalysis.WitnessSumReader
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem driver_update (position old next : ℕ) (out native counts : List Bool) :
    Function.update (heads position old out native counts) 2532 next=heads position next out native counts := by
  funext i
  refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ j
    · intro k
      have hk : (k.castAdd 1).castAdd 528≠(2532 : Fin 3061) := by
        intro h;have hv:=congrArg Fin.val h;change k.val=2532 at hv;omega
      simp only [Function.update_of_ne hk,heads,SumDock.coreHeads,Fin.addCases_left]
    · intro k
      fin_cases k
      change Function.update (heads position old out native counts) 2532 next 2532=next
      rw [Function.update_self]
  · intro j
    have hj : j.natAdd 2533≠(2532 : Fin 3061) := by
      intro h;have hv:=congrArg Fin.val h;change 2533+j.val=2532 at hv;omega
    simp only [Function.update_of_ne hj,heads,Fin.addCases_right]

private theorem position_other (position next driver : ℕ) (out native counts : List Bool)
    (i : Fin 3061) (hi : i≠722) :
    heads position driver out native counts i=heads next driver out native counts i := by
  revert hi
  refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ i
  · intro j
    simp only [heads,Fin.addCases_left]
    refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ j
    · intro j
      simp only [SumDock.coreHeads,Fin.addCases_left]
      refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ j
      · intro j
        simp only [TermRound.heads,Fin.addCases_left]
        refine Fin.addCases (m:=826) (n:=1) ?_ ?_ j
        · intro j
          simp only [TermCommit.heads,Fin.addCases_left]
          refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
          · intro j hj
            simp only [TermMass.heads,Fin.addCases_left]
            exact TermRead.heads_other position next j (by intro h;subst j;exact hj rfl)
          · intro j _;simp only [TermMass.heads,Fin.addCases_right]
        · intro j _;simp only [TermCommit.heads,Fin.addCases_right]
      · intro j _;simp only [TermRound.heads,Fin.addCases_right]
    · intro j _;simp only [SumDock.coreHeads,Fin.addCases_right]
  · intro j _;simp only [heads,Fin.addCases_right]

theorem position_update (position next driver : ℕ) (out native counts : List Bool) :
    Function.update (heads position driver out native counts) 722 next=heads next driver out native counts := by
  funext i
  by_cases hi : i=722
  · subst i;rw [Function.update_self];rfl
  · rw [Function.update_of_ne hi]
    exact position_other position next driver out native counts i hi

theorem header_bounds (H T : ℕ) (bits arityBits : List Bool)
    (hraw : 2*bits.length+1 ≤ H) (hbudget : SumGuard.budget bits arityBits T+1 ≤ H) :
    ((SumHeader.words bits).flatMap frame++SumHeader.tail H bits).length ≤ H ∧
      (ZeroPadding.pad H (CompareMachine.word (SumFields.count bits))).length ≤ H := by
  obtain ⟨bank,_,_arity,_cap,stream,count,_rawCount,_flag,support⟩:=
    SumHeader.header_run H T bits arityBits hraw hbudget
  have hs:=support 357 (by decide) (by decide)
  have hc:=support 368 (by decide) (by decide)
  rw [stream] at hs
  rw [count] at hc
  exact ⟨hs,hc⟩

theorem hole_retained {s : ℕ} (p : Machine 528 s) (fuel : ℕ) (source : Configuration 3061 s)
    (r : ExecutionReceipt 3061 s) (hr : runFrom (RecoveryFocus.machine SumDock.slots p) fuel source=some r)
    (i : Fin 528) (hi : i.val=357 ∨ i.val=368 ∨ i.val=499) :
    r.final.tapes (i.natAdd 2533)=source.tapes (i.natAdd 2533) :=
  RecoveryFocus.run_other SumDock.slots p _ (hole_outside i hi) fuel source r hr

def enter {s : ℕ} (body : Machine 3061 s) := Composition.machine (SumCursor.move .right) body

theorem enter_run {s : ℕ} (body : Machine 3061 s) (fuel position : ℕ)
    (out native counts : List Bool) (input : Fin 3061 → List Bool) (last : ExecutionReceipt 3061 s)
    (hr : runFrom body fuel ⟨body.start,heads position 1 out native counts,input⟩=some last)
    (hs : last.steps ≤ fuel) :
    ∃ r,runFrom (enter body) (fuel+2)
      ⟨(enter body).start,heads position 0 out native counts,input⟩=some r ∧ r.steps ≤ fuel+2 ∧
      r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes := by
  obtain ⟨first,hfirst,fs,fh,ft⟩:=SumCursor.move_run .right (heads position 0 out native counts) input
  have firstHeads : first.final.heads=heads position 1 out native counts := by
    rw [fh]
    exact driver_update position 0 1 out native counts
  have lastRun : runFrom body fuel ⟨body.start,first.final.heads,first.final.tapes⟩=some last := by
    rw [firstHeads,ft];exact hr
  obtain ⟨r,run,rs,rh,rt⟩:=joined (SumCursor.move .right) body 1 fuel _ _ first last hfirst lastRun (by omega) hs
  have eq : 1+1+fuel=fuel+2 := by omega
  rw [eq] at run rs
  exact ⟨r,run,rs,rh,rt⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
