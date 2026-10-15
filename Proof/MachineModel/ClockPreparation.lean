import Proof.MachineModel.ClockNumericPrep

/-! Full counted-input to dyadic event-field preparation. The source input
is preserved throughout; every auxiliary tape starts blank and every head
is restored. The finite tape layout is explicit for the enclosing U. -/
namespace NearCubicWires.RepairOrdinary.ClockPreparation
open LocalBitMultitape ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countLayout : Fin 14 ≃ Fin 14 where
  toFun := ![0,11,12,13,1,2,3,4,5,6,7,8,9,10]
  invFun := ![0,4,5,6,7,8,9,10,11,12,13,1,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def countPhase : Machine 14 14 := ClockJoin.lifted (e:=10) countLayout ClockLengthReady.machine
def numericPhase : Machine 14 36 := ClockJoin.lifted (e:=3) (Equiv.refl (Fin 14)) ClockNumericPrep.machine
def machine : Machine 14 50 := Composition.machine countPhase numericPhase

def input (bits : List Bool) : Fin 14 → List Bool :=
  ![[],[],[],[],[],[],[],[],[],[],[],[],frame bits,[]]
def extra (bits : List Bool) (carry reset : ℕ) : Fin 3 → List Bool :=
  ![List.replicate carry false,frame bits,List.replicate reset false]
def middle (bits : List Bool) (carry reset : ℕ) : Fin 14 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (11+3) => List Bool) (ClockNumericPrep.input bits.length) (extra bits carry reset)
def output (bits : List Bool) (carry reset degree : ℕ) : Fin 14 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (11+3) => List Bool) (ClockNumericPrep.output bits.length degree) (extra bits carry reset)

def budget (bits : List Bool) : ℕ := ClockLengthReady.budget bits+1+ClockNumericPrep.budget bits.length

theorem count_phase (bits : List Bool) (hn : 0<bits.length) :
    ∃ carry reset,
      carry≤2*PCPResourceLedger.ell bits.length+3 ∧
      reset≤ClockInputLength.cost bits.length bits ∧
      ReadyRun countPhase (ClockLengthReady.budget bits) (input bits) (middle bits carry reset) := by
  obtain ⟨carry,reset,hcarry,hreset,r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockLengthReady.count_run bits hn
  have hinput : ClockLengthReady.source bits = ![[],[],frame bits,[]] := by funext i; fin_cases i <;> rfl
  rw [hinput] at hr
  have h : ReadyRun ClockLengthReady.machine (ClockLengthReady.budget bits)
      ![[],[],frame bits,[]]
      ![frame (ClockBinary.word bits.length),List.replicate carry false,frame bits,List.replicate reset false] := by
    refine ⟨r,hr,?_,hh,hs⟩
    funext i; fin_cases i <;> simp [h0,h1,h2,h3]
  have hl := ClockJoin.lift (e:=10) countLayout ClockLengthReady.machine (ClockLengthReady.budget bits)
    _ _ (fun _ => []) h
  have hi : data (e:=10) countLayout ![[],[],frame bits,[]] (fun _ => [])=input bits := by
    funext i; fin_cases i <;> rfl
  have ho : data (e:=10) countLayout
      ![frame (ClockBinary.word bits.length),List.replicate carry false,frame bits,List.replicate reset false]
      (fun _ => [])=middle bits carry reset := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact ⟨carry,reset,hcarry,hreset,hl⟩

theorem prepare_run (bits : List Bool) (hn : 0<bits.length) :
    ∃ carry reset degree,
      carry≤2*PCPResourceLedger.ell bits.length+3 ∧
      reset≤ClockInputLength.cost bits.length bits ∧
      degree≤2*PCPResourceLedger.ell bits.length+4 ∧
      ReadyRun machine (budget bits) (input bits) (output bits carry reset degree) := by
  obtain ⟨carry,reset,hcarry,hreset,hcount⟩ := count_phase bits hn
  obtain ⟨degree,hdegree,hnumeric⟩ := ClockNumericPrep.prepare_run bits.length hn
  have hl := ClockJoin.lift (e:=3) (Equiv.refl (Fin 14)) ClockNumericPrep.machine
    (ClockNumericPrep.budget bits.length) _ _ (extra bits carry reset) hnumeric
  have hi : data (e:=3) (Equiv.refl (Fin 14)) (ClockNumericPrep.input bits.length) (extra bits carry reset)=middle bits carry reset := rfl
  have ho : data (e:=3) (Equiv.refl (Fin 14)) (ClockNumericPrep.output bits.length degree) (extra bits carry reset)=output bits carry reset degree := rfl
  rw [hi,ho] at hl
  have hwhole := ClockJoin.join countPhase numericPhase _ _ _ _ _ hcount hl
  exact ⟨carry,reset,degree,hcarry,hreset,hdegree,hwhole⟩

theorem budget_bound (bits : List Bool) :
    budget bits≤100*(bits.length+1)*PCPResourceLedger.q bits.length^2 := by
  have hprep := ClockNumericPrep.budget_bound bits.length
  have hq : 1≤PCPResourceLedger.q bits.length^2 := by
    apply Nat.one_le_pow
    simp [PCPResourceLedger.q]
  have he : PCPResourceLedger.ell bits.length≤PCPResourceLedger.q bits.length^2 := by
    dsimp [PCPResourceLedger.q]
    nlinarith
  have hn : bits.length≤bits.length*PCPResourceLedger.q bits.length^2 := by nlinarith
  have hnell := Nat.mul_le_mul_left bits.length he
  dsimp only [budget,ClockLengthReady.budget,ClockInputLength.cost]
  nlinarith

/-- Literal fields consumed by the memory emitter, from a real N-bit input.
The source is on tape 12; a fixed tape renaming places this phase inside U. -/
theorem event_fields (bits : List Bool) (hn : 0<bits.length) :
    ∃ r : ExecutionReceipt 14 50,
      run machine (100*(bits.length+1)*PCPResourceLedger.q bits.length^2) (input bits)=some r ∧
      r.final.tapes 0=frame (ClockBinary.word bits.length) ∧
      r.final.tapes 6=frame (List.replicate (ClockDyadicLedger.exponent bits.length) false++[true]) ∧
      r.final.tapes 7=List.replicate (ClockDyadicLedger.width bits.length) true ∧
      r.final.tapes 8=List.replicate (2*ClockDyadicLedger.width bits.length) true ∧
      r.final.tapes 9=List.replicate (2*ClockDyadicLedger.width bits.length+2) true ∧
      r.final.tapes 12=frame bits ∧ (∀ i,r.final.heads i=0) ∧
      r.steps≤100*(bits.length+1)*PCPResourceLedger.q bits.length^2 := by
  obtain ⟨carry,reset,degree,_,_,_,h⟩ := prepare_run bits hn
  obtain ⟨r,hr,ht,hh,hs⟩ := ClockJoin.enlarge machine _ _ _ _ h (budget_bound bits)
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,hh,hs⟩
  all_goals simp [ht,output,ClockNumericPrep.output,extra,Fin.addCases]

end NearCubicWires.RepairOrdinary.ClockPreparation
