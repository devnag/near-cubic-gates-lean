import Proof.MachineModel.OrdinaryWilliamsPowerLoop

/-! Cold unary powering: the initial one is physically written, followed
by the fixed D calls. For D=10 this produces the supported source dimension
V from the payload-derived factor c. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPower
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (D c : ℕ) : Fin (tapes D) → List Bool :=
  fun i => if i.val=0 then UnaryTemplate.tape c else []
def initialOne (D c : ℕ) : Fin (tapes D) → List Bool :=
  fun i => if i.val=0 then UnaryTemplate.tape c else if i.val=1 then [true] else []
def bootstrap (D : ℕ) : Machine (tapes D) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i.val=1 then some true else none,fun _ => .stay⟩ else none

theorem bootstrap_ready (D c : ℕ) : ReadyRun (bootstrap D) 1 (input D c) (initialOne D c) := by
  let final : Configuration (tapes D) 2 := ⟨1,fun _ => 0,initialOne D c⟩
  have hs : step (bootstrap D) (initialConfiguration (bootstrap D) (input D c))=some final := by
    simp [step,bootstrap,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,final]
    · funext i
      by_cases h0 : i.val=0
      · simp [applyAction,input,initialOne,final,h0]
      · by_cases h1 : i.val=1
        · simp [applyAction,input,initialOne,final,h1,writeTapeBit]
        · simp [applyAction,input,initialOne,final,h0,h1]
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

theorem initial_input (D c : ℕ) (hD : 0<D) : Input D c ⟨0,hD⟩ (initialOne D c) := by
  refine ⟨?_,?_,?_⟩
  · simp [initialOne,factor]
  · simp [initialOne,operand,previous]
  · intro i hi
    have h0 : ¬i.val=0 := by omega
    have h1 : ¬i.val=1 := by omega
    simp [initialOne,h0,h1]

noncomputable def fullMachine (D : ℕ) (hD : 0<D) := Composition.machine (bootstrap D) (machine D hD)

theorem full_run (D c : ℕ) (hD : 0<D) (hc : 1≤c) :
    ∃ r : ExecutionReceipt (tapes D) (2+Fintype.card (RecoveryCalls.Control (sizes D))),
      run (fullMachine D hD) (budget D c+2) (input D c)=some r ∧
      r.final.tapes (factor D)=UnaryTemplate.tape c ∧
      r.final.tapes (outputTape D hD)=List.replicate (c^D) true ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤budget D c+2 := by
  obtain ⟨first,hr,ht,hh,hs⟩ := bootstrap_ready D c
  obtain ⟨last,hl,hlf,hlh,hls⟩ := power_run D c hD hc (initialOne D c) (initial_input D c hD)
  have hmid : Composition.restart first.final (machine D hD).start =
      initialConfiguration (machine D hD) (initialOne D c) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  have hl' : runFrom (machine D hD) (budget D c)
      (Composition.restart first.final (machine D hD).start)=some last := by rw [hmid]; exact hl
  have hj := Composition.run_join (bootstrap D) (machine D hD) 1 (budget D c) _ first last hr hl'
  have htime : 1+1+budget D c=budget D c+2 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,hlf.1,hlf.2,hlh,?_⟩
  change first.steps+1+last.steps≤_
  omega

end NearCubicWires.RepairOrdinary.WilliamsPower
