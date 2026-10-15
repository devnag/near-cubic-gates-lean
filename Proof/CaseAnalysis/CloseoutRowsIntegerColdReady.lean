import Proof.CaseAnalysis.RowsIntegerBudget

/-! Paid whole-list rewind for the enclosing supported-gate decoder. The
same complete native list, count and acceptance bit are physically retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readyMachine:=Rewind.machine machine
def readyInput (bits : List Bool) : Fin 460→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (459+1)=>List Bool) (input bits) (fun _=>[])
def readyBudget (bits : List Bool):=2*budget bits+2

theorem ready_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun readyMachine (readyBudget bits) (readyInput bits) output ∧
      output 213=produced bits ∧ output 220=CompareMachine.word (Reencode.fields bits).length ∧
      (readTapeBit (output 219) 0=true ↔ (CanonicalBinary.decodeIntList (value bits)).isSome) ∧
      (∀ values,CanonicalBinary.decodeIntList (value bits)=some values →
        output 213=values.flatMap RepairRepresentation.intWord ∧
          output 220=CompareMachine.word values.length):=by
  obtain ⟨a,ha,as,ao,_,af,ac,typed⟩:=native_run bits
  obtain ⟨r,hr,rt,_,rh,rs,_⟩:=Rewind.Workspace.reset_workspace machine _ _ a ha 0
  have hb:2*a.steps+2≤readyBudget bits:=by unfold readyBudget;omega
  have more:=run_moreFuel readyMachine _ (readyBudget bits-(2*a.steps+2)) (readyInput bits) r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r.final.tapes,⟨r,more,rfl,rh,rs.le.trans hb⟩,
    (rt 213).trans ao,(rt 220).trans ac,?_,?_⟩
  · change readTapeBit (r.final.tapes ((219 : Fin 459).castAdd 1)) 0=true ↔_
    rw [rt]
    exact af
  · intro values hv
    exact ⟨(rt 213).trans (typed values hv).1,(rt 220).trans (typed values hv).2⟩

theorem ready_budget_bound (bits : List Bool) :
    readyBudget bits≤3000000000000000000000000*(bits.length+2)^26:=by
  have h:=budget_bound bits
  have hp:1≤(bits.length+2)^26:=Nat.one_le_pow _ _ (by omega)
  unfold readyBudget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
