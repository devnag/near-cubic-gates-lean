import Proof.MachineModel.OrdinaryWilliamsDimensions

/-! Physical copies of a sentinel dimension template. The source is
retained, two raw unary copies and another template are allocated, and
all five cursors are restored by the actual replay log. -/
namespace NearCubicWires.RepairOrdinary.MatrixTemplateCopy
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n : ℕ) : Fin 4 → List Bool := ![UnaryTemplate.tape n,[],[],[]]
def bootstrap : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,![.right,.stay,.stay,.stay]⟩ else none
def machine := Composition.machine bootstrap MatrixDimensionHeader.machine

theorem copy_run (n : ℕ) :
    ∃ r : ExecutionReceipt 4 6,
      run machine (2*n+5) (input n)=some r ∧
      r.final.tapes 0=UnaryTemplate.tape n ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧ r.steps=2*n+5 := by
  let after : Configuration 4 2 := ⟨1,![1,0,0,0],input n⟩
  have hstep : step bootstrap (initialConfiguration bootstrap (input n))=some after := by
    simp [step,bootstrap,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,after]
    · funext i; fin_cases i <;> simp [applyAction,after]
  obtain ⟨base,hb,hf,hs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨last,hl,hlf,hls⟩ := MatrixDimensionHeader.header_run [false] [] n
  have hmid : Composition.restart base.final MatrixDimensionHeader.machine.start =
      MatrixDimensionHeader.input ([false]++List.replicate n true++false::[]) [false].length := by
    rw [hf]
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [Composition.restart,after,input,MatrixDimensionHeader.input,UnaryTemplate.tape]
  rw [←hmid] at hl
  have hj := Composition.run_join bootstrap MatrixDimensionHeader.machine 1 (2*n+3) _ base last hb hl
  have htime : 1+1+(2*n+3)=2*n+5 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt base last,hj,?_,?_,?_,?_,?_⟩
  · change last.final.tapes 0=_
    rw [hlf]; simp [MatrixDimensionHeader.output,UnaryTemplate.tape]
  · change last.final.tapes 1=_
    rw [hlf]; rfl
  · change last.final.tapes 2=_
    rw [hlf]; rfl
  · change last.final.tapes 3=_
    rw [hlf]; rfl
  · change base.steps+1+last.steps=_
    omega

def resetMachine := Rewind.machine machine
def resetInput (n : ℕ) : Fin 5 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (4+1) => List Bool) (input n) (fun _ : Fin 1 => [])

theorem reset_run (n : ℕ) :
    ∃ r : ExecutionReceipt 5 8,
      run resetMachine (4*n+12) (resetInput n)=some r ∧
      r.final.tapes 0=UnaryTemplate.tape n ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*n+12 := by
  obtain ⟨base,hb,h0,h1,h2,h3,hs⟩ := copy_run n
  obtain ⟨r,hr,ht,hh,hsteps,_⟩ := Rewind.reset_run machine (2*n+5) (input n) base hb
  have htime : 2*base.steps+2=4*n+12 := by omega
  rw [htime] at hr hsteps
  exact ⟨r,hr,(ht 0).trans h0,(ht 1).trans h1,(ht 2).trans h2,(ht 3).trans h3,hh,hsteps⟩

end NearCubicWires.RepairOrdinary.MatrixTemplateCopy
