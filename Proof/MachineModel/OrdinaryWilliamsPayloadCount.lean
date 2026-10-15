import Proof.MachineModel.OrdinaryMatrixPayloadCountLoop

/-! Canonical request application of the executed payload counter. Its
only dimension input is U; c is the number of physically scanned 2*U-bit
groups in the actual two matrix words. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPayloadCount
open LocalBitMultitape RecoveryExecution SourceInterfaces ExecutableInterfaces RepairRepresentation
open WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,![none,none,some false],![.stay,.stay,.right]⟩ else none
def input (u : ℕ) (source : List Bool) (pos : ℕ) : Configuration 3 2 :=
  ⟨0,![1,pos,0],![UnaryTemplate.tape u,source,[]]⟩
noncomputable def machine := Composition.machine boot MatrixPayloadCount.machine

theorem boot_run (u : ℕ) (source : List Bool) (pos : ℕ) :
    ∃ r : ExecutionReceipt 3 2, runFrom boot 1 (input u source pos)=some r ∧
      r.final=MatrixPayloadCount.config 1 u source pos 0 ∧ r.steps=1 := by
  have hs : step boot (input u source pos)=some (MatrixPayloadCount.config 1 u source pos 0) := by
    simp [step,boot,input]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,MatrixPayloadCount.config]
    · funext i; fin_cases i <;> simp [applyAction,writeTapeBit,MatrixPayloadCount.config]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem count_run (pre bits : List Bool) (u count : ℕ) (hu : 0<u)
    (hbits : bits.length=2*u*count) :
    ∃ r : ExecutionReceipt 3 (2+Fintype.card (RecoveryCalls.Control MatrixPayloadCount.sizes)),
      runFrom machine (count*(6*u+15)+9)
        (Composition.leftConfig _ (input u (pre++frame bits) pre.length))=some r ∧
      r.final=Composition.rightConfig 2
        (MatrixPayloadCount.result u (pre++frame bits) (pre.length+2*bits.length) count) ∧
      r.steps≤count*(6*u+15)+9 := by
  obtain ⟨first,hr,hf,hs⟩ := boot_run u (pre++frame bits) pre.length
  obtain ⟨last,hl,hlf,hls⟩ := MatrixPayloadCount.count_run pre bits u count hu hbits
  have hi : Composition.restart first.final MatrixPayloadCount.machine.start =
      MatrixPayloadCount.boundary 0 u (pre++frame bits) pre.length 0 := by rw [hf]; rfl
  rw [← hi] at hl
  have hj := Composition.run_join boot MatrixPayloadCount.machine 1 (count*(6*u+15)+7) _ first last hr hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_⟩
  · have he : 1+1+(count*(6*u+15)+7)=count*(6*u+15)+9 := by omega
    rw [he] at hj
    exact hj
  · change Composition.rightConfig 2 last.final=_
    rw [hlf]
  · change first.steps+1+last.steps≤_
    omega

def payload (r : RectangularProductRequest) : List Bool := rowMajorBitMatrix r.left ++ rowMajorBitMatrix r.right

theorem payload_length (r : RectangularProductRequest) :
    (payload r).length=2*r.dimension*rectangularInnerDimension r.dimension := by
  rw [payload,List.length_append,WilliamsLoader.matrix_length,WilliamsLoader.matrix_length]
  ring

theorem request_run (r : RectangularProductRequest) (hr : 1≤r.dimension) (pre : List Bool) :
    ∃ actual : ExecutionReceipt 3 (2+Fintype.card (RecoveryCalls.Control MatrixPayloadCount.sizes)),
      runFrom machine (rectangularInnerDimension r.dimension*(6*r.dimension+15)+9)
        (Composition.leftConfig _ (input r.dimension (pre++frame (payload r)) pre.length))=some actual ∧
      actual.final.tapes 0=UnaryTemplate.tape r.dimension ∧ actual.final.heads 0=1 ∧
      actual.final.tapes 1=pre++frame (payload r) ∧ actual.final.heads 1=pre.length+2*(payload r).length ∧
      actual.final.tapes 2=UnaryTemplate.tape (rectangularInnerDimension r.dimension) ∧ actual.final.heads 2=1 ∧
      actual.steps≤rectangularInnerDimension r.dimension*(6*r.dimension+15)+9 := by
  obtain ⟨actual,ha,hf,hs⟩ := count_run pre (payload r) r.dimension (rectangularInnerDimension r.dimension)
    (by omega) (payload_length r)
  refine ⟨actual,ha,?_,?_,?_,?_,?_,?_,hs⟩
  all_goals rw [hf]; rfl

end NearCubicWires.RepairOrdinary.WilliamsPayloadCount
