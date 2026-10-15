import Proof.CaseAnalysis.CaseTwoVariablePrep
import Proof.PCP.ProjectionDimensionPowerBounds
import Proof.Hierarchy.HierarchyFixedWord

/-! From the physically computed block width and native clause-count template,
produce the fixed block offset, the padded position offset, and raw native
clause width. All fixed constants and copies execute on ordinary tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BlockScalars
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def widthSlots : Fin 5→Fin 22:=![0,2,3,4,5]
def powerSlots : Fin 5→Fin 22:=![4,6,7,8,9]
def oneSlots : Fin 2→Fin 22:=![10,11]
def differenceSlots : Fin 4→Fin 22:=![4,10,12,13]
def positionSlots : Fin 5→Fin 22:=![12,14,15,16,17]
def clauseSlots : Fin 5→Fin 22:=![1,18,19,20,21]
def width:=RecoveryFocus.machine widthSlots MatrixRawDimension.resetMachine
def power (block : ℕ):=RecoveryFocus.machine powerSlots (DimensionPower.machine 1 block)
def one:=RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 1))
def difference:=RecoveryFocus.machine differenceSlots MatrixUnaryDifference.resetMachine
def position:=RecoveryFocus.machine positionSlots MatrixTemplateCopy.resetMachine
def clause:=RecoveryFocus.machine clauseSlots MatrixTemplateCopy.resetMachine
def machine (block : ℕ):=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine width (power block)) one) difference) position) clause
def input (length cb : ℕ) (i : Fin 22):=
  if i=0 then List.replicate length true else if i=1 then UnaryTemplate.tape cb else []
def budget (block position cb : ℕ):=(4*(position+1)+8)+1+DimensionPower.cost block (position+1) 1+1+8+1+
  (2*(position+1)+8)+1+(4*position+12)+1+(4*cb+12)

theorem scalars_run (block pos cb : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine block) (budget block pos cb) (input (pos+1) cb) out ∧
      out 2=List.replicate (pos+1) true ∧ out 8=List.replicate (block*(pos+1)) true ∧
      out 14=List.replicate pos true ∧ out 18=List.replicate cb true:=by
  obtain ⟨w,hw,w1,_,w3,wh,ws⟩:=MatrixRawDimension.reset_run (pos+1)
  have wr:ClockJoin.ReadyRun MatrixRawDimension.resetMachine _ _ w.final.tapes:=⟨w,hw,rfl,wh,ws.le⟩
  have wf:=wr.focus widthSlots (by decide) (input (pos+1) cb) (by intro j;fin_cases j <;>rfl)
  let A:=install widthSlots (input (pos+1) cb) w.final.tapes
  obtain ⟨pow,hp,p0,pv⟩:=DimensionPower.power_run 1 block (pos+1)
  simp only [pow_one] at pv
  have pf:=hp.focus powerSlots (by decide) A (by
    intro j;fin_cases j
    · exact (install_slot widthSlots (by decide) _ w.final.tapes 3).trans w3
    all_goals exact install_other widthSlots (input (pos+1) cb) w.final.tapes _ (by decide))
  let B:=install powerSlots A pow
  obtain ⟨o,ho,ot,oh,os⟩:=HierarchyFixedWord.word_ready (UnaryTemplate.tape 1)
  have or:ClockJoin.ReadyRun (HierarchyFixedWord.machine (UnaryTemplate.tape 1)) 8 (fun _=>[]) _:=⟨o,ho,ot,oh,os.le⟩
  have of:=or.focus oneSlots (by decide) B (by
    intro j
    rw [show B (oneSlots j)=A (oneSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide),
      show A (oneSlots j)=input (pos+1) cb (oneSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide)]
    fin_cases j <;>rfl)
  let C:=install oneSlots B ![UnaryTemplate.tape 1,List.replicate 3 false]
  obtain ⟨d,hd,_,_,d2,dh,ds⟩:=MatrixUnaryDifference.reset_run (pos+1) 1 (by omega)
  simp only [Nat.add_sub_cancel] at d2
  have dr:ClockJoin.ReadyRun MatrixUnaryDifference.resetMachine _ _ d.final.tapes:=⟨d,hd,rfl,dh,ds.le⟩
  have df:=dr.focus differenceSlots (by decide) C (by
    intro j
    by_cases h0 : j=0
    · subst j;exact (install_other oneSlots B _ 4 (by decide)).trans ((install_slot powerSlots (by decide) A pow 0).trans p0)
    by_cases h1 : j=1
    · subst j;exact install_slot oneSlots (by decide) B _ 0
    rw [show C (differenceSlots j)=B (differenceSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide),
      show B (differenceSlots j)=A (differenceSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide),
      show A (differenceSlots j)=input (pos+1) cb (differenceSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide)]
    fin_cases j <;>first | contradiction | rfl)
  let D:=install differenceSlots C d.final.tapes
  obtain ⟨p,hpRun,_,p1,_,_,ph,ps⟩:=MatrixTemplateCopy.reset_run pos
  have pr:ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine _ _ p.final.tapes:=⟨p,hpRun,rfl,ph,ps.le⟩
  have ppf:=pr.focus positionSlots (by decide) D (by
    intro j
    by_cases h0 : j=0
    · subst j;exact (install_slot differenceSlots (by decide) C d.final.tapes 2).trans d2
    rw [show D (positionSlots j)=C (positionSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide),
      show C (positionSlots j)=B (positionSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide),
      show B (positionSlots j)=A (positionSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide),
      show A (positionSlots j)=input (pos+1) cb (positionSlots j) from install_other _ _ _ _ (by fin_cases j <;>first | contradiction | decide)]
    fin_cases j <;>first | contradiction | rfl)
  let E:=install positionSlots D p.final.tapes
  obtain ⟨c,hc,_,c1,_,_,ch,cs⟩:=MatrixTemplateCopy.reset_run cb
  have cr:ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine _ _ c.final.tapes:=⟨c,hc,rfl,ch,cs.le⟩
  have cf:=cr.focus clauseSlots (by decide) E (by
    intro j
    rw [show E (clauseSlots j)=D (clauseSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide),
      show D (clauseSlots j)=C (clauseSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide),
      show C (clauseSlots j)=B (clauseSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide),
      show B (clauseSlots j)=A (clauseSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide),
      show A (clauseSlots j)=input (pos+1) cb (clauseSlots j) from install_other _ _ _ _ (by fin_cases j <;>decide)]
    fin_cases j <;>rfl)
  have whole:=ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
      (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ wf pf) of) df) ppf) cf
  refine ⟨_,whole,?_,?_,?_,?_⟩
  · exact (install_other clauseSlots E c.final.tapes 2 (by decide)).trans
      ((install_other positionSlots D p.final.tapes 2 (by decide)).trans
        ((install_other differenceSlots C d.final.tapes 2 (by decide)).trans
          ((install_other oneSlots B _ 2 (by decide)).trans
            ((install_other powerSlots A pow 2 (by decide)).trans
              ((install_slot widthSlots (by decide) _ w.final.tapes 1).trans w1)))))
  · exact (install_other clauseSlots E c.final.tapes 8 (by decide)).trans
      ((install_other positionSlots D p.final.tapes 8 (by decide)).trans
        ((install_other differenceSlots C d.final.tapes 8 (by decide)).trans
          ((install_other oneSlots B _ 8 (by decide)).trans
            ((install_slot powerSlots (by decide) A pow 3).trans pv))))
  · exact (install_other clauseSlots E c.final.tapes 14 (by decide)).trans
      ((install_slot positionSlots (by decide) D p.final.tapes 1).trans p1)
  · exact (install_slot clauseSlots (by decide) E c.final.tapes 1).trans c1

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BlockScalars
