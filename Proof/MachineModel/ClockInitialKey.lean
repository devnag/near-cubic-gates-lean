import Proof.MachineModel.ClockScalarFields

namespace NearCubicWires.RepairOrdinary.ClockInitialKey
open LocalBitMultitape ClockJoin SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def K (w : ℕ) : ℕ := 2*w+2
def power (w : ℕ) : List Bool := List.replicate w false++[true]
def key (w : ℕ) : List Bool := power w++List.replicate (w+1) false
@[simp] theorem key_length (w : ℕ) : (key w).length=K w := by simp [key,power,K]; omega
theorem key_binary (w : ℕ) : key w=binary (K w) (2^w) := by
  have hv : value (key w)=2^w := by simp [key,power,value_append,value]
  simpa [hv] using (BoundedCounter.binary_of_value (key w)).symm
theorem normalized_power (w : ℕ) : ClockNormalize.resize (K w) (power w)=key w := by
  have hlen : (power w).length≤K w := by simp [power,K]; omega
  rw [ClockNormalize.resize_eq _ _ hlen]
  have hsub : K w-(power w).length=w+1 := by simp [K,power]; omega
  rw [hsub]
  rfl

def fieldInput (w : ℕ) : Fin 6 → List Bool := ![List.replicate w true,[],[],[],[],[]]
def fieldOutput (w : ℕ) : Fin 6 → List Bool :=
  ![List.replicate w true,frame (power w),List.replicate (w+3) true,
    List.replicate (2*(w+3)) true,List.replicate (2*(w+3)+2) true,List.replicate (2*w+10) false]
def input (w : ℕ) : Fin 12 → List Bool :=
  ![List.replicate w true,[],[],[],[],[],List.replicate (K w) true,[],[],[],[],[]]
def afterPower (w : ℕ) : Fin 12 → List Bool :=
  ![List.replicate w true,frame (power w),List.replicate (w+3) true,List.replicate (2*(w+3)) true,
    List.replicate (2*(w+3)+2) true,List.replicate (2*w+10) false,List.replicate (K w) true,[],[],[],[],[]]
def afterNormalize (w : ℕ) : Fin 12 → List Bool :=
  ![List.replicate w true,frame (power w),List.replicate (w+3) true,List.replicate (2*(w+3)) true,
    List.replicate (2*(w+3)+2) true,List.replicate (2*w+10) false,List.replicate (K w) true,
    frame (key w),[true],List.replicate (2*K w+1) false,[],[]]
def output (w : ℕ) : Fin 12 → List Bool :=
  ![List.replicate w true,frame (power w),List.replicate (w+3) true,List.replicate (2*(w+3)) true,
    List.replicate (2*(w+3)+2) true,List.replicate (2*w+10) false,List.replicate (K w) true,
    frame (key w),[true],List.replicate (2*K w+1) false,key w,List.replicate (K w) false]
def normLayout : Fin 12 ≃ Fin 12 where
  toFun := ![6,1,7,8,9,0,2,3,4,5,10,11]
  invFun := ![5,1,6,7,8,9,0,2,3,4,10,11]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def extractLayout : Fin 12 ≃ Fin 12 where
  toFun := ![7,10,11,0,1,2,3,4,5,6,8,9]
  invFun := ![3,4,5,6,7,8,9,0,10,11,1,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def fieldPhase : Machine 12 14 := ClockJoin.lifted (e:=6) (Equiv.refl _) ClockFields.machine
def normPhase : Machine 12 6 := ClockJoin.lifted (e:=7) normLayout ClockNormalize.machine
def extractPhase : Machine 12 5 := ClockJoin.lifted (e:=9) extractLayout Streaming.machine
def machine : Machine 12 25 := Composition.machine (Composition.machine fieldPhase normPhase) extractPhase

theorem field_ready (w : ℕ) : ReadyRun ClockFields.machine (4*w+22) (fieldInput w) (fieldOutput w) := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,h5,hh,hs⟩ := ClockFields.fields_run w
  have hi : (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
      ![List.replicate w true,[],[],[],[]] (fun _ : Fin 1 => []))=fieldInput w := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i; fin_cases i <;> simp [fieldOutput,power,h0,h1,h2,h3,h4,h5]

theorem field_phase (w : ℕ) : ReadyRun fieldPhase (4*w+22) (input w) (afterPower w) := by
  let extra : Fin 6 → List Bool := ![List.replicate (K w) true,[],[],[],[],[]]
  have hl := ClockJoin.lift (Equiv.refl (Fin 12)) ClockFields.machine (4*w+22) _ _ extra (field_ready w)
  have hi : data (Equiv.refl (Fin 12)) (fieldInput w) extra=input w := by funext i; fin_cases i <;> rfl
  have ho : data (Equiv.refl (Fin 12)) (fieldOutput w) extra=afterPower w := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem norm_phase (w : ℕ) : ReadyRun normPhase (4*K w+4) (afterPower w) (afterNormalize w) := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockNormalize.normalize_run (K w) (power w)
  have hlen : (power w).length≤K w := by simp [power,K]; omega
  have h : ReadyRun ClockNormalize.machine (4*K w+4) (ClockNormalize.input (K w) (power w))
      ![List.replicate (K w) true,frame (power w),frame (key w),[true],List.replicate (2*K w+1) false] := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i; fin_cases i <;> simp [h0,h1,h2,h3,h4,normalized_power,hlen]
  let extra : Fin 7 → List Bool := ![List.replicate w true,List.replicate (w+3) true,
    List.replicate (2*(w+3)) true,List.replicate (2*(w+3)+2) true,List.replicate (2*w+10) false,[],[]]
  have hl := ClockJoin.lift normLayout ClockNormalize.machine (4*K w+4) _ _ extra h
  have hi : data normLayout (ClockNormalize.input (K w) (power w)) extra=afterPower w := by
    funext i; fin_cases i <;> rfl
  have ho : data normLayout
      ![List.replicate (K w) true,frame (power w),frame (key w),[true],List.replicate (2*K w+1) false]
      extra=afterNormalize w := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem extract_phase (w : ℕ) : ReadyRun extractPhase (4*K w+2) (afterNormalize w) (output w) := by
  obtain ⟨r,hr,hf,hs,_⟩ := Streaming.copy_run (key w)
  have hi0 : (fun t : Fin 3 => if t.val=0 then frame (key w) else [])=![frame (key w),[],[]] := by
    funext i; fin_cases i <;> rfl
  rw [hi0,key_length] at hr
  have h : ReadyRun Streaming.machine (4*K w+2) ![frame (key w),[],[]]
      ![frame (key w),key w,List.replicate (K w) false] := by
    refine ⟨r,hr,?_,?_,by simpa using hs.le⟩
    · rw [hf]; funext i; fin_cases i <;> simp [Streaming.finished,Streaming.config]
    · rw [hf]; intro i; fin_cases i <;> rfl
  let extra : Fin 9 → List Bool := ![List.replicate w true,frame (power w),List.replicate (w+3) true,
    List.replicate (2*(w+3)) true,List.replicate (2*(w+3)+2) true,List.replicate (2*w+10) false,
    List.replicate (K w) true,[true],List.replicate (2*K w+1) false]
  have hl := ClockJoin.lift extractLayout Streaming.machine (4*K w+2) _ _ extra h
  have hi : data extractLayout ![frame (key w),[],[]] extra=afterNormalize w := by
    funext i; fin_cases i <;> rfl
  have ho : data extractLayout ![frame (key w),key w,List.replicate (K w) false] extra=output w := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem key_ready (w : ℕ) : ReadyRun machine (50*(w+1)) (input w) (output w) := by
  have hfirst := ClockJoin.join fieldPhase normPhase _ _ _ _ _ (field_phase w) (norm_phase w)
  have h := ClockJoin.join (Composition.machine fieldPhase normPhase) extractPhase _ _ _ _ _ hfirst (extract_phase w)
  exact ClockJoin.enlarge machine _ _ _ _ h (by dsimp [K]; omega)

theorem key_run (w : ℕ) :
    ∃ r : ExecutionReceipt 12 25,
      run machine (50*(w+1)) (input w)=some r ∧
      r.final.tapes 0=List.replicate w true ∧ r.final.tapes 6=List.replicate (2*w+2) true ∧
      r.final.tapes 10=binary (2*w+2) (2^w) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤50*(w+1) := by
  obtain ⟨r,hr,hf,hh,hs⟩ := key_ready w
  exact ⟨r,hr,by simp [hf,output],by simp [hf,output,K],by simp [hf,output,key_binary,K],hh,hs⟩

end NearCubicWires.RepairOrdinary.ClockInitialKey
