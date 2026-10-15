import Proof.MachineModel.OrdinaryMatrixTemplateEntries

/-! Product of two physical sentinel templates. All raw operands, the
product and its reusable template are constructed by the executed calls. -/
namespace NearCubicWires.RepairOrdinary.MatrixTemplateProduct
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (d e : ℕ) : Fin 12 → List Bool :=
  fun i => if i=0 then UnaryTemplate.tape d else if i=5 then UnaryTemplate.tape e else []
def productSlots : Fin 4 → Fin 12 := ![1,5,6,7]
def outputSlots : Fin 5 → Fin 12 := ![6,8,9,10,11]
def copy : Machine 12 8 := TapeEmbedding.machine 7 MatrixTemplateCopy.resetMachine
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def first := Composition.machine copy product
noncomputable def finish := RecoveryFocus.machine outputSlots MatrixRawDimension.resetMachine
noncomputable def machine := Composition.machine first finish

theorem product_run (d e : ℕ) :
    ∃ r : ExecutionReceipt 12 21,
      run machine (8*d*e+10*d+28) (input d e)=some r ∧
      r.final.tapes 0=UnaryTemplate.tape d ∧ r.final.tapes 5=UnaryTemplate.tape e ∧
      r.final.tapes 10=UnaryTemplate.tape (d*e) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=8*d*e+10*d+28 := by
  obtain ⟨base,hb,h0,h1,_,_,hh,hs⟩ := MatrixTemplateCopy.reset_run d
  let extras : Fin 7 → List Bool := ![UnaryTemplate.tape e,[],[],[],[],[],[]]
  have he := TapeEmbedding.run_embed MatrixTemplateCopy.resetMachine (fun _ : Fin 7 => 0) extras _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 7 => 0) extras base.final
  have ah (i : Fin 12) : ambient.heads i=0 := by fin_cases i <;> first | exact hh _ | rfl
  obtain ⟨mid,hmid,hmt,hmh,hms⟩ := WilliamsUnaryProduct.product_ready d e
  have hpi : RecoveryFocus.config productSlots ambient.heads ambient.tapes
      (initialConfiguration ClockUnaryProduct.machine (WilliamsUnaryProduct.input d e)) =
      Composition.restart ambient product.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact ah _
    · intro i; fin_cases i
      · exact h1
      all_goals rfl
  obtain ⟨pf,hpf,hpff,hpfs⟩ := RecoveryFocus.run_config productSlots (by decide) ClockUnaryProduct.machine
    ambient.heads ambient.tapes _ _ mid hmid
  rw [hpi] at hpf
  have hj := Composition.run_join copy product (4*d+12) (WilliamsUnaryProduct.budget d e) _
    (TapeEmbedding.receipt (fun _ : Fin 7 => 0) extras base) pf he hpf
  let prep := Composition.joinedReceipt (TapeEmbedding.receipt (fun _ : Fin 7 => 0) extras base) pf
  have hpick (i : Fin 4) : RecoveryFocus.pick productSlots (productSlots i)=some i :=
    RecoveryFocus.pick_slot productSlots (by decide) i
  have ph (i : Fin 12) : prep.final.heads i=0 := by
    change pf.final.heads i=0
    rw [hpff]
    simp only [RecoveryFocus.config]
    split <;> first | exact ah _ | exact hmh _
  have pother (i : Fin 12) (hi : RecoveryFocus.pick productSlots i=none) :
      prep.final.tapes i=ambient.tapes i := by
    change pf.final.tapes i=_
    rw [hpff]; simp only [RecoveryFocus.config,hi]
  have p0 : prep.final.tapes 0=UnaryTemplate.tape d := (pother 0 (by decide)).trans h0
  have p5 : prep.final.tapes 5=UnaryTemplate.tape e := by
    change pf.final.tapes (productSlots 1)=_
    rw [hpff]
    simp only [RecoveryFocus.config,hpick]
    rw [hmt]; rfl
  have p6 : prep.final.tapes 6=List.replicate (d*e) true := by
    change pf.final.tapes (productSlots 2)=_
    rw [hpff]
    simp only [RecoveryFocus.config,hpick]
    rw [hmt]; rfl
  obtain ⟨last,hl,_,_,hl3,hlh,hls⟩ := MatrixRawDimension.reset_run (d*e)
  have hli : RecoveryFocus.config outputSlots prep.final.heads prep.final.tapes
      (initialConfiguration MatrixRawDimension.resetMachine (MatrixRawDimension.resetInput (d*e))) =
      Composition.restart prep.final finish.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact ph _
    · intro i; fin_cases i
      · exact p6
      · exact pother 8 (by decide)
      · exact pother 9 (by decide)
      · exact pother 10 (by decide)
      · exact pother 11 (by decide)
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config outputSlots (by decide) MatrixRawDimension.resetMachine
    prep.final.heads prep.final.tapes _ _ last hl
  rw [hli] at hfocus
  have hwhole := Composition.run_join first finish ((4*d+12)+1+WilliamsUnaryProduct.budget d e)
    (4*(d*e)+8) _ prep focused hj hfocus
  have htime : ((4*d+12)+1+WilliamsUnaryProduct.budget d e)+1+(4*(d*e)+8)=8*d*e+10*d+28 := by
    unfold WilliamsUnaryProduct.budget
    ring
  rw [htime] at hwhole
  have hin : Composition.leftConfig 6 (Composition.leftConfig 7
      (TapeEmbedding.config (fun _ : Fin 7 => 0) extras
        (initialConfiguration MatrixTemplateCopy.resetMachine (MatrixTemplateCopy.resetInput d)))) =
      initialConfiguration machine (input d e) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hwhole
  have opick (i : Fin 5) : RecoveryFocus.pick outputSlots (outputSlots i)=some i :=
    RecoveryFocus.pick_slot outputSlots (by decide) i
  have other (i : Fin 12) (hi : RecoveryFocus.pick outputSlots i=none) :
      focused.final.tapes i=prep.final.tapes i := by rw [hff]; simp only [RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt prep focused,hwhole,(other 0 (by decide)).trans p0,
    (other 5 (by decide)).trans p5,?_,?_,?_⟩
  · change focused.final.tapes (outputSlots 3)=_
    rw [hff]; simpa only [RecoveryFocus.config,opick] using hl3
  · intro i
    change focused.final.heads i=0
    rw [hff]
    simp only [RecoveryFocus.config]
    split <;> first | exact ph _ | exact hlh _
  · change base.steps+1+pf.steps+1+focused.steps=_
    rw [hs,hpfs,hms,hfs,hls]
    exact htime

end NearCubicWires.RepairOrdinary.MatrixTemplateProduct
