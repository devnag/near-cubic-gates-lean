import Proof.Amplification.RecoveryEraseConstant
import Proof.MachineModel.ClockUnaryProduct

/-! The coarse scratch erase driver is physically produced from the original
framed word, including empty input. Two ordinary unary products supply the
quadratic length; the fixed coefficient is written by finite control. -/
namespace NearCubicWires.RepairOrdinary.RecoveryEraseDriver
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient : Nat := 8192
def length (bits : List Bool) := coefficient * (bits.length+1)^2

def productTime (d e : Nat) := 2*(d*(2*e+3)+2)+2

theorem product_ready (d e : Nat) : ReadyRun ClockUnaryProduct.machine (productTime d e)
    ![List.replicate d true,CompareMachine.word e,[],[]]
    ![List.replicate d true,CompareMachine.word e,List.replicate (d*e) true,
      List.replicate (d*(2*e+3)+2) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run d e
  refine ⟨r,?_,?_,hh,hs⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

def constantSlots : Fin 2 → Fin 9 := ![1,5]
def widthSlots : Fin 3 → Fin 9 := ![0,2,6]
def firstSlots : Fin 4 → Fin 9 := ![1,2,3,7]
def secondSlots : Fin 4 → Fin 9 := ![3,2,4,8]
theorem constantSlots_injective : Function.Injective constantSlots := by decide
theorem widthSlots_injective : Function.Injective widthSlots := by decide
theorem firstSlots_injective : Function.Injective firstSlots := by decide
theorem secondSlots_injective : Function.Injective secondSlots := by decide

def input (bits : List Bool) (i : Fin 9) : List Bool := if i.val=0 then frame bits else []
def output0 (bits : List Bool) (i : Fin 9) : List Bool :=
  match i.val with
  | 0 => frame bits
  | 1 => List.replicate coefficient true
  | 5 => List.replicate coefficient false
  | _ => []
def output1 (bits : List Bool) (i : Fin 9) : List Bool :=
  if i.val=2 then CompareMachine.word (bits.length+1)
  else if i.val=6 then List.replicate (6*bits.length+6) false else output0 bits i

def output2 (bits : List Bool) (i : Fin 9) : List Bool :=
  if i.val=3 then List.replicate (coefficient*(bits.length+1)) true
  else if i.val=7 then List.replicate (coefficient*(2*(bits.length+1)+3)+2) false else output1 bits i

def output3 (bits : List Bool) (i : Fin 9) : List Bool :=
  if i.val=4 then List.replicate (coefficient*(bits.length+1)*(bits.length+1)) true
  else if i.val=8 then List.replicate ((coefficient*(bits.length+1))*(2*(bits.length+1)+3)+2) false
  else output2 bits i

def sizes : Fin 4 → Nat := ![coefficient+1+2,11,7,7]
noncomputable def programs : (j : Fin 4) → Machine 9 (sizes j)
  | ⟨0,_⟩ => RecoveryFocus.machine constantSlots (RecoveryEraseConstant.resetMachine coefficient)
  | ⟨1,_⟩ => RecoveryFocus.machine widthSlots RecoveryEraseWidth.machine
  | ⟨2,_⟩ => RecoveryFocus.machine firstSlots ClockUnaryProduct.machine
  | ⟨3,_⟩ => RecoveryFocus.machine secondSlots ClockUnaryProduct.machine
  | ⟨n+4,h⟩ => False.elim (by omega)

def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 9 → Bool) : Option (Fin 4) :=
  if j.val=0 then some 1 else if j.val=1 then some 2 else if j.val=2 then some 3 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem constant_ready (bits : List Bool) : ReadyRun (programs 0) (2*coefficient+2) (input bits) (output0 bits) := by
  have h := (RecoveryEraseConstant.constant_ready coefficient).focus constantSlots constantSlots_injective (input bits)
    (by intro j; fin_cases j <;> rfl)
  have he : install constantSlots (input bits) ![List.replicate coefficient true,List.replicate coefficient false] = output0 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot constantSlots constantSlots_injective _ _ 0
      | exact install_slot constantSlots constantSlots_injective _ _ 1
      | exact install_other constantSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem width_ready (bits : List Bool) : ReadyRun (programs 1) (12*bits.length+14) (output0 bits) (output1 bits) := by
  have h := (RecoveryEraseWidth.width_ready bits 0).focus widthSlots widthSlots_injective (output0 bits)
    (by intro j; fin_cases j <;> rfl)
  simp only [Nat.zero_max] at h
  have he : install widthSlots (output0 bits) ![frame bits,CompareMachine.word (bits.length+1),List.replicate (6*bits.length+6) false] = output1 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot widthSlots widthSlots_injective _ _ 0
      | exact install_slot widthSlots widthSlots_injective _ _ 1
      | exact install_slot widthSlots widthSlots_injective _ _ 2
      | exact install_other widthSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem first_ready (bits : List Bool) : ReadyRun (programs 2) (productTime coefficient (bits.length+1)) (output1 bits) (output2 bits) := by
  have h := (product_ready coefficient (bits.length+1)).focus firstSlots firstSlots_injective (output1 bits)
    (by intro j; fin_cases j <;> rfl)
  have he : install firstSlots (output1 bits) ![List.replicate coefficient true,CompareMachine.word (bits.length+1),List.replicate (coefficient*(bits.length+1)) true,List.replicate (coefficient*(2*(bits.length+1)+3)+2) false] = output2 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot firstSlots firstSlots_injective _ _ 0
      | exact install_slot firstSlots firstSlots_injective _ _ 1
      | exact install_slot firstSlots firstSlots_injective _ _ 2
      | exact install_slot firstSlots firstSlots_injective _ _ 3
      | exact install_other firstSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem second_ready (bits : List Bool) : ReadyRun (programs 3) (productTime (coefficient*(bits.length+1)) (bits.length+1)) (output2 bits) (output3 bits) := by
  have h := (product_ready (coefficient*(bits.length+1)) (bits.length+1)).focus secondSlots secondSlots_injective (output2 bits)
    (by intro j; fin_cases j <;> rfl)
  have he : install secondSlots (output2 bits) ![List.replicate (coefficient*(bits.length+1)) true,CompareMachine.word (bits.length+1),List.replicate ((coefficient*(bits.length+1))*(bits.length+1)) true,List.replicate ((coefficient*(bits.length+1))*(2*(bits.length+1)+3)+2) false] = output3 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot secondSlots secondSlots_injective _ _ 0
      | exact install_slot secondSlots secondSlots_injective _ _ 1
      | exact install_slot secondSlots secondSlots_injective _ _ 2
      | exact install_slot secondSlots secondSlots_injective _ _ 3
      | exact install_other secondSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

def time (bits : List Bool) :=
  ((2*coefficient+2+1+(12*bits.length+14+1))+(productTime coefficient (bits.length+1)+1))+
    (productTime (coefficient*(bits.length+1)) (bits.length+1)+1)
def budget (bits : List Bool) := 64*(coefficient+1)*(bits.length+1)^2

theorem driver_ready (bits : List Bool) : ReadyRun machine (time bits) (input bits) (output3 bits) := by
  have hc := (constant_ready bits).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hw := (width_ready bits).call sizes programs 0 next 1 2 (by intro q; rfl)
  have hf := (first_ready bits).call sizes programs 0 next 2 3 (by intro q; rfl)
  have hs := (second_ready bits).stop sizes programs 0 next 3 (by intro q; rfl)
  have h := ((hc.trans hw).trans hf).trans hs
  have hin : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) (input bits)) =
      initialConfiguration machine (input bits) := by rfl
  rw [hin] at h
  obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hfinal,RecoveryCalls.stopped],by intro i; simp [hfinal,RecoveryCalls.stopped],hsteps⟩

theorem time_bound (bits : List Bool) : time bits ≤ budget bits := by
  unfold time budget productTime coefficient
  nlinarith

theorem driver_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 9 (Fintype.card (RecoveryCalls.Control sizes)),
      run machine (budget bits) (fun i => if i.val=0 then frame bits else []) = some r ∧
      r.final.tapes 4 = List.replicate (length bits) true ∧
      r.final.tapes 0 = frame bits ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤budget bits := by
  obtain ⟨r,hr,ht,hh,hs⟩ := driver_ready bits
  have hmore := run_moreFuel machine (time bits) (budget bits-time bits) _ r hr
  rw [Nat.add_sub_of_le (time_bound bits)] at hmore
  refine ⟨r,hmore,?_,?_,hh,hs.le.trans (time_bound bits)⟩
  · rw [ht]
    change List.replicate (coefficient*(bits.length+1)*(bits.length+1)) true =
      List.replicate (coefficient*(bits.length+1)^2) true
    rw [pow_two,Nat.mul_assoc]
  · rw [ht]; rfl

end NearCubicWires.RepairOrdinary.RecoveryEraseDriver
