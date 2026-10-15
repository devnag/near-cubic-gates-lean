import Proof.Amplification.RecoveryPCPFormulaResumeSearchPair
import Proof.Amplification.RecoveryTseitinReadOnly

/-! Two retained frames become the exact raw native compound request. Both
original fields survive; their reads, output copy and all-head rewind are
charged. This is the original input word, with no additional outer frame. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.CompoundInput
open LocalBitMultitape RepairSource RecoveryRootRound RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem append_readonly : NoWrite CompetitorFrameAppend.machine 0:=by
  intro q bits action h
  simp only [CompetitorFrameAppend.machine] at h
  split_ifs at h <;>cases h <;>rfl
theorem pair_readonly (i : Fin 2) : NoWrite RecoveryPCPFormulaResumeSearchPair.machine (i.castAdd 3):=by
  fin_cases i
  · exact composition _ _ _
      (focus RecoveryPCPFormulaResumeSearchPair.leftSlots (by decide) _ 0 append_readonly)
      (unselected RecoveryPCPFormulaResumeSearchPair.rightSlots _ 0 (by decide))
  · exact composition _ _ _
      (unselected RecoveryPCPFormulaResumeSearchPair.leftSlots _ 1 (by decide))
      (focus RecoveryPCPFormulaResumeSearchPair.rightSlots (by decide) _ 0 append_readonly)
noncomputable def machine:=Rewind.machine RecoveryPCPFormulaResumeSearchPair.machine
def input (left right : List Bool) : Fin 6→List Bool:=![frame left,frame right,[],[],[],[]]
def budget (left right : List Bool):=2*RecoveryPCPFormulaResumeSearchPair.budget left right+2

theorem pair_ready (left right : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget left right) (input left right) out ∧
      out 2=frame left++frame right ∧ out 0=frame left ∧ out 1=frame right:=by
  obtain ⟨base,hb,bt,_bh,bs⟩:=RecoveryPCPFormulaResumeSearchPair.pair_run left right
  have h0:=run_tape _ _ (pair_readonly 0) _ _ base hb
  have h1:=run_tape _ _ (pair_readonly 1) _ _ base hb
  obtain ⟨r,hr,ht,hh,hs,_⟩:=Rewind.reset_run RecoveryPCPFormulaResumeSearchPair.machine _ _ base hb
  have hi : Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool)
      (RecoveryPCPFormulaResumeSearchPair.input left right) (fun _=>[])=input left right:=by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  have ready : ClockJoin.ReadyRun machine (2*base.steps+2) (input left right) r.final.tapes:=⟨r,hr,rfl,hh,hs.le⟩
  exact ⟨_,ClockJoin.enlarge _ _ _ _ _ ready (by unfold budget;omega),
    (ht 2).trans bt,(ht 0).trans h0,(ht 1).trans h1⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.CompoundInput
