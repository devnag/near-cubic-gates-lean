import Proof.MachineModel.OrdinaryMatrixBatchNativeDimensions

/-! Used inner coordinates and zero-padding length are produced by the
actual gate/bucket product and physical capacity-minus-used difference. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketUsage
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 12) : Fin 15 := i.castAdd 3
def differenceSlots : Fin 4 → Fin 15 := ![12,10,13,14]
noncomputable def product := RecoveryFocus.machine native MatrixTemplateProduct.machine
noncomputable def difference := RecoveryFocus.machine differenceSlots MatrixUnaryDifference.resetMachine
noncomputable def machine := Composition.machine product difference
def input (G B C : ℕ) : Fin 15 → List Bool := fun i =>
  if i=0 then UnaryTemplate.tape G else if i=5 then UnaryTemplate.tape B else if i=12 then UnaryTemplate.tape C else []
def budget (G B C : ℕ) := (8*G*B+10*G+28)+1+(2*C+8)

theorem usage_run (G B C : ℕ) (hused : G*B≤C) :
    ∃ out,ClockJoin.ReadyRun machine (budget G B C) (input G B C) out ∧
      out 0=UnaryTemplate.tape G ∧ out 5=UnaryTemplate.tape B ∧ out 12=UnaryTemplate.tape C ∧
      out 10=UnaryTemplate.tape (G*B) ∧ out 13=UnaryTemplate.tape (C-G*B) := by
  obtain ⟨base,hb,b0,b5,b10,bh,bs⟩ := MatrixTemplateProduct.product_run G B
  have ready : ClockJoin.ReadyRun MatrixTemplateProduct.machine (8*G*B+10*G+28)
      (MatrixTemplateProduct.input G B) base.final.tapes := ⟨base,hb,rfl,bh,bs.le⟩
  have hn : Function.Injective native := by
    intro i j h
    exact Fin.ext (congrArg (fun a : Fin 15 => a.val) h)
  let prepared := install native (input G B C) base.final.tapes
  have hp := bounded_focus native hn _ _ _ ready (input G B C)
    (by intro i; fin_cases i <;> rfl)
  have localT (i : Fin 12) : prepared (native i)=base.final.tapes i := install_slot native hn _ _ i
  have extra (i : Fin 15) (hi : 12 ≤ i.val) : prepared i=input G B C i := by
    apply install_other
    intro j h
    have hv := congrArg Fin.val h
    dsimp [native] at hv
    omega
  obtain ⟨diff,hd,d0,d1,d2,dh,ds⟩ := MatrixUnaryDifference.reset_run C (G*B) hused
  have dr : ClockJoin.ReadyRun MatrixUnaryDifference.resetMachine (2*C+8)
      (MatrixUnaryDifference.resetInput C (G*B)) diff.final.tapes := ⟨diff,hd,rfl,dh,ds.le⟩
  have di : ∀ i,prepared (differenceSlots i)=MatrixUnaryDifference.resetInput C (G*B) i := by
    intro i; fin_cases i
    · exact extra 12 (by decide)
    · exact (localT 10).trans b10
    · exact extra 13 (by decide)
    · exact extra 14 (by decide)
  let out := install differenceSlots prepared diff.final.tapes
  have hdifference := bounded_focus differenceSlots (by decide) _ _ _ dr prepared di
  have whole := ClockJoin.join product difference _ _ _ _ _ hp hdifference
  exact ⟨out,whole,
    (install_other differenceSlots _ _ 0 (by decide)).trans ((localT 0).trans b0),
    (install_other differenceSlots _ _ 5 (by decide)).trans ((localT 5).trans b5),
    (install_slot differenceSlots (by decide) _ _ 0).trans d0,
    (install_slot differenceSlots (by decide) _ _ 1).trans d1,
    (install_slot differenceSlots (by decide) _ _ 2).trans d2⟩

end NearCubicWires.RepairOrdinary.MatrixBucketUsage
