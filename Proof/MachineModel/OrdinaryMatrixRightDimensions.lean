import Proof.MachineModel.OrdinaryMatrixRightRecords

/-! U, Used and Capacity-Used survive the complete original-request right
record producer as actual finite templates with heads zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightDimensions
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 348 := ![285,287,39]
def values (r : Request) : Fin 3 → ℕ := ![r.Used,r.Capacity-r.Used,r.U]

theorem source_fields (r : Request) : ∃ actual,
    run MatrixBatchRightPass.machine (MatrixBatchRightPass.budget r) (MatrixBatchRightPass.input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=UnaryTemplate.tape (values r j)) ∧
    (∀ j,actual.final.heads (slots j)=0) ∧ actual.steps≤MatrixBatchRightPass.budget r := by
  obtain ⟨_,_,bank,actual,hbank,ha,_,_,_,_,_,_,passOld,steps⟩ := MatrixBatchRightPass.raw_run r
  obtain ⟨ret,same,hret,hs,_,_,bankT,bankH,_⟩ := MatrixBatchRightBank.raw_run r
  have he : same=bank := Option.some.inj (hs.symm.trans hbank)
  subst same
  obtain ⟨_,_,left,same,hleft,hs,retT,_,_,_,retH,retOld,_⟩ := MatrixBatchRightReturn.raw_run r
  have he : same=ret := Option.some.inj (hs.symm.trans hret)
  subst same
  obtain ⟨sorted,same,hsort,hs,_,_,leftOld,_⟩ := MatrixBatchLeftPlane.raw_run r
  have he : same=left := Option.some.inj (hs.symm.trans hleft)
  subst same
  obtain ⟨same,hs,_,_,t285,h285,t287,h287,t39,h39,_⟩ := MatrixBatchLeftFields.source_fields r
  have he : same=sorted := Option.some.inj (hs.symm.trans hsort)
  subst same
  have retained (i : Fin 3) : actual.final.tapes (slots i)=sorted.final.tapes (![285,287,39] i) ∧
      actual.final.heads (slots i)=0 := by
    have hp := passOld (![285,287,39] i) (by fin_cases i <;> decide)
    have ht := bankT (![285,287,39] i) (by fin_cases i <;> decide)
    have hh := bankH (![285,287,39] i)
    have hl := leftOld (![285,287,39] i)
    constructor
    · fin_cases i
      all_goals exact hp.1.trans (ht.trans ((congrFun retT _).trans hl.1))
    · fin_cases i
      · exact hp.2.trans (hh.trans ((retOld 285 (by decide)).trans (hl.2.trans h285)))
      · exact hp.2.trans (hh.trans ((retOld 287 (by decide)).trans (hl.2.trans h287)))
      · exact hp.2.trans (hh.trans (retH 2))
  refine ⟨actual,ha,?_,fun i => (retained i).2,steps⟩
  intro i
  apply (retained i).1.trans
  fin_cases i
  · exact t285
  · exact t287
  · exact t39

end NearCubicWires.RepairOrdinary.MatrixRightDimensions
