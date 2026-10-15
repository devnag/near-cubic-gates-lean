import Proof.MachineModel.ClockFromInput

/-! The empty-input dyadic clock branch prints the fixed exponent and then
executes the same clock-field emitter as the nonempty constructor. -/
namespace NearCubicWires.RepairOrdinary.ClockEmptyInput
open LocalBitMultitape ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def constantLayout : Fin 7 ≃ Fin 7 := Equiv.swap 1 6
def constantPhase (k : ℕ) : Machine 7 (k+1+2) :=
  lifted (e:=5) constantLayout (RecoveryEraseConstant.resetMachine k)
def fieldsPhase : Machine 7 14 := lifted (e:=1) (Equiv.refl _) ClockFields.machine
def localMachine (k : ℕ) : Machine 7 (k+1+2+14) :=
  Composition.machine (constantPhase k) fieldsPhase
def prepared (k : ℕ) : Fin 7 → List Bool :=
  ![List.replicate k true,[],[],[],[],[],List.replicate k false]
def localOutput (k : ℕ) : Fin 7 → List Bool :=
  ![List.replicate k true,frame (List.replicate k false++[true]),
    List.replicate (k+3) true,List.replicate (2*(k+3)) true,
    List.replicate (2*(k+3)+2) true,List.replicate (2*k+10) false,
    List.replicate k false]

theorem local_ready (k : ℕ) :
    ReadyRun (localMachine k) (6*k+25) (fun _ => []) (localOutput k) := by
  obtain ⟨rc,hrc,htc,hhc,hsc⟩ := RecoveryEraseConstant.constant_ready k
  have hc0 : ReadyRun (RecoveryEraseConstant.resetMachine k) (2*k+2)
      (fun _ => []) ![List.replicate k true,List.replicate k false] :=
    ⟨rc,hrc,htc,hhc,hsc.le⟩
  have hc := ClockJoin.lift (e:=5) constantLayout (RecoveryEraseConstant.resetMachine k)
    (2*k+2) _ _ (fun _ => []) hc0
  have hci : data constantLayout (fun _ : Fin 2 => []) (fun _ : Fin 5 => [])=
      (fun _ : Fin 7 => []) := by funext i; fin_cases i <;> rfl
  have hco : data constantLayout ![List.replicate k true,List.replicate k false]
      (fun _ : Fin 5 => [])=prepared k := by funext i; fin_cases i <;> rfl
  rw [hci,hco] at hc
  obtain ⟨r,hr,h0,h1,h2,h3,h4,h5,hh,hs⟩ := ClockFields.fields_run k
  have hf : ReadyRun ClockFields.machine (4*k+22)
      (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
        ![List.replicate k true,[],[],[],[]] (fun _ : Fin 1 => []))
      ![List.replicate k true,frame (List.replicate k false++[true]),
        List.replicate (k+3) true,List.replicate (2*(k+3)) true,
        List.replicate (2*(k+3)+2) true,List.replicate (2*k+10) false] := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i; fin_cases i <;> assumption
  have hfields := ClockJoin.lift (e:=1) (Equiv.refl (Fin 7)) ClockFields.machine
    (4*k+22) _ _ (fun _ => List.replicate k false) hf
  have hfi : data (Equiv.refl (Fin 7))
      (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
        ![List.replicate k true,[],[],[],[]] (fun _ : Fin 1 => []))
      (fun _ : Fin 1 => List.replicate k false)=prepared k := by
    funext i; fin_cases i <;> rfl
  have hfo : data (Equiv.refl (Fin 7))
      ![List.replicate k true,frame (List.replicate k false++[true]),
        List.replicate (k+3) true,List.replicate (2*(k+3)) true,
        List.replicate (2*(k+3)+2) true,List.replicate (2*k+10) false]
      (fun _ : Fin 1 => List.replicate k false)=localOutput k := by
    funext i; fin_cases i <;> rfl
  rw [hfi,hfo] at hfields
  have h := ClockJoin.join (constantPhase k) fieldsPhase _ _ _ _ _ hc hfields
  have htime : (2*k+2)+1+(4*k+22)=6*k+25 := by omega
  simpa only [htime,localMachine] using h

def layout : Fin 34 ≃ Fin 34 where
  toFun := ![27,29,30,31,32,28,33,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
  invFun := ![7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,0,5,1,2,3,4,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def retained : Fin 27 → List Bool :=
  fun i => ClockFromInput.input [] (layout (Fin.natAdd 7 i))
def machine (k : ℕ) : Machine 34 (k+1+2+14) := lifted (e:=27) layout (localMachine k)
def output (k : ℕ) : Fin 34 → List Bool := data layout (localOutput k) retained

theorem empty_ready (k : ℕ) :
    ReadyRun (machine k) (6*k+25) (ClockFromInput.input []) (output k) := by
  have h := ClockJoin.lift layout (localMachine k) (6*k+25) _ _ retained (local_ready k)
  have hi : data layout (fun _ : Fin 7 => []) retained=ClockFromInput.input [] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at h
  exact h

@[simp] theorem exponent_zero (k c : ℕ) : ClockEnvelope.exponent k c 0=k := by
  simp [ClockEnvelope.exponent,ClockEnvelope.logWidth,ClockDyadicLedger.exponent,
    PCPResourceLedger.ell]

theorem empty_fields (k c : ℕ) :
    output k 29=frame (SignedSortKey.binary (ClockEnvelope.exponent k c 0+1)
      (ClockEnvelope.clock k c 0)) ∧
    output k 27=List.replicate (ClockEnvelope.exponent k c 0) true ∧
    output k 12=frame [] := by
  have hb := ClockFromInput.clock_word_binary k c 0
  rw [exponent_zero] at hb
  refine ⟨?_,?_,rfl⟩
  · change frame (List.replicate k false++[true])=_
    rw [hb,exponent_zero]
  · rw [exponent_zero]
    rfl

end NearCubicWires.RepairOrdinary.ClockEmptyInput
