import Proof.CaseAnalysis.ScheduleClauseWidth
import Proof.CaseAnalysis.ScheduleScale

/-! Complete cold arithmetic for the exact m_s used by the common language.
The actual native q is the only numerical input; copies and clause degree
are fixed finite-program parameters. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Width
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : Nat) := Clause.tapes D+10
def clauseSlots (D : Nat) : Fin (Clause.tapes D)→Fin (tapes D) := fun i=>i.castAdd 10
def scaleSlots (D : Nat) : Fin 12→Fin (tapes D) := fun i=>
  ⟨if i.val=0 then 0 else if i.val=1 then 24+2*D else 24+2*D+i.val,
    by have:=i.isLt;dsimp [tapes,Clause.tapes];split_ifs <;> omega⟩
theorem clause_injective (D : Nat) : Function.Injective (clauseSlots D) := by
  intro a b h
  have hv:=congrArg (fun i : Fin (tapes D)=>i.val) h
  exact Fin.ext hv
theorem scale_injective (D : Nat) : Function.Injective (scaleSlots D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [scaleSlots] at hv
  split_ifs at hv <;> omega
def clause (D : Nat) := RecoveryFocus.machine (clauseSlots D) (Clause.machine D)
def scale (D copies : Nat) := RecoveryFocus.machine (scaleSlots D) (Scale.machine copies)
def machine (D copies : Nat) := Composition.machine (clause D) (scale D copies)
def input (D q : Nat) : Fin (tapes D)→List Bool := fun i=>if i.val=0 then List.replicate q true else []
def outputSlot (D : Nat) := scaleSlots D 10
def budget (D copies q : Nat) := Clause.budget D q+1+
  Scale.budget copies (q+1) (CloseoutLanguage.clauseWidth D q)

theorem width_run (D copies q : Nat) (hD : 1 ≤ D) : ∃ out,
    ClockJoin.ReadyRun (machine D copies) (budget D copies q) (input D q) out ∧
      out (outputSlot D)=List.replicate (CloseoutLanguage.coreWidth copies D q) true := by
  obtain ⟨clauseOut,hc,hq,hr⟩:=Clause.clause_run D q hD
  have hcf:=hc.focus (clauseSlots D) (clause_injective D) (input D q) (by intro i;rfl)
  let middle:=install (clauseSlots D) (input D q) clauseOut
  change ClockJoin.ReadyRun (clause D) (Clause.budget D q) (input D q) middle at hcf
  obtain ⟨scaleOut,hs,hw⟩:=Scale.scale_run copies (q+1) (CloseoutLanguage.clauseWidth D q)
  have hsf:=hs.focus (scaleSlots D) (scale_injective D) middle (by
    intro i
    fin_cases i
    · change install (clauseSlots D) _ _ (clauseSlots D (Clause.qSlot D))=_
      rw [install_slot _ (clause_injective D)]
      exact hq
    · have he : scaleSlots D 1=clauseSlots D (Clause.widthSlot D) := by
        apply Fin.ext
        dsimp [scaleSlots,clauseSlots,Clause.widthSlot,Clause.clogSlots]
        omega
      change middle (scaleSlots D 1)=CompareMachine.word (CloseoutLanguage.clauseWidth D q)
      rw [he]
      change install (clauseSlots D) _ _ _=_
      rw [install_slot _ (clause_injective D)]
      exact hr
    all_goals
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
        dsimp [clauseSlots,scaleSlots,Clause.tapes] at hv this
        omega)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hcf hsf,?_⟩
  rw [outputSlot,install_slot _ (scale_injective D),hw]
  unfold CloseoutLanguage.coreWidth
  congr 2
  omega

end
end NearCubicWires.RepairSource.CloseoutSchedule.Width
