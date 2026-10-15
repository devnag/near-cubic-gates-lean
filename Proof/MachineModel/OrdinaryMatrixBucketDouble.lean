import Proof.MachineModel.OrdinaryMatrixBucketPredecessor

/-! Produce the two physical 2U numerators and its sentinel from the
retained U template. The constant factor and every copy are executed. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketDouble
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def constantSlots : Fin 2 → Fin 10 := ![2,3]
def productSlots : Fin 4 → Fin 10 := ![2,0,4,5]
def copySlots : Fin 5 → Fin 10 := ![4,6,7,8,9]
noncomputable def constant := RecoveryFocus.machine constantSlots (HierarchyFixedWord.machine [true,true])
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def copy := RecoveryFocus.machine copySlots MatrixRawDimension.resetMachine
noncomputable def tail := Composition.machine product copy
noncomputable def machine := Composition.machine constant tail
def input (U : ℕ) : Fin 10 → List Bool := fun i => if i=0 then UnaryTemplate.tape U else []
def budget (U : ℕ) := 6+1+(WilliamsUnaryProduct.budget 2 U+1+(4*(2*U)+8))

theorem double_run (U : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget U) (input U) out ∧
    out 0=UnaryTemplate.tape U ∧ out 6=List.replicate (2*U) true ∧
    out 7=List.replicate (2*U) true ∧ out 8=UnaryTemplate.tape (2*U) := by
  obtain ⟨fixed,hfixed,ft,fh,fs⟩ := HierarchyFixedWord.word_ready [true,true]
  have fixedReady : ClockJoin.ReadyRun (HierarchyFixedWord.machine [true,true]) 6
      (fun _ => []) ![[true,true],[false,false]] := ⟨fixed,hfixed,ft,fh,fs.le⟩
  let printed := install constantSlots (input U) ![[true,true],[false,false]]
  have hf := bounded_focus constantSlots (by decide) _ _ _ fixedReady (input U)
    (by intro i; fin_cases i <;> rfl)
  have hiProduct : ∀ i,printed (productSlots i)=WilliamsUnaryProduct.input 2 U i := by
    intro i; fin_cases i
    · exact install_slot constantSlots (by decide) _ _ 0
    all_goals exact install_other constantSlots _ _ _ (by decide)
  let multiplied := install productSlots printed (WilliamsUnaryProduct.output 2 U)
  have hp := bounded_focus productSlots (by decide) _ _ _ (CompetitorDimensions.unary_ready 2 U)
    printed hiProduct
  have m0 : multiplied 0=UnaryTemplate.tape U := install_slot productSlots (by decide) _ _ 1
  have m4 : multiplied 4=List.replicate (2*U) true := install_slot productSlots (by decide) _ _ 2
  have fresh (i : Fin 10) (hi : 6 ≤ i.val) : multiplied i=[] := by
    have hprod : ∀ j,productSlots j≠i := by intro j; fin_cases j <;> intro h <;> have hv := congrArg Fin.val h <;> simp [productSlots] at hv <;> omega
    have hc : ∀ j,constantSlots j≠i := by intro j; fin_cases j <;> intro h <;> have hv := congrArg Fin.val h <;> simp [constantSlots] at hv <;> omega
    exact (install_other productSlots _ _ i hprod).trans
      ((install_other constantSlots _ _ i hc).trans (by simp [input]; intro h; subst i; omega))
  obtain ⟨base,hbase,b1,b2,b3,bh,bs⟩ := MatrixRawDimension.reset_run (2*U)
  have ready : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*(2*U)+8)
      (MatrixRawDimension.resetInput (2*U)) base.final.tapes := ⟨base,hbase,rfl,bh,bs.le⟩
  have hiCopy : ∀ i,multiplied (copySlots i)=MatrixRawDimension.resetInput (2*U) i := by
    intro i; fin_cases i
    · exact m4
    all_goals exact fresh _ (by decide)
  let out := install copySlots multiplied base.final.tapes
  have hc := bounded_focus copySlots (by decide) _ _ _ ready multiplied hiCopy
  have ht := ClockJoin.join product copy _ _ _ _ _ hp hc
  have hall := ClockJoin.join constant tail _ _ _ _ _ hf ht
  exact ⟨out,hall,(install_other copySlots _ _ 0 (by decide)).trans m0,
    (install_slot copySlots (by decide) _ _ 1).trans b1,
    (install_slot copySlots (by decide) _ _ 2).trans b2,
    (install_slot copySlots (by decide) _ _ 3).trans b3⟩

end NearCubicWires.RepairOrdinary.MatrixBucketDouble
