import Proof.Amplification.RecoveryListPredecessor

/-! The literal raw-list consumer of predecessor and reusable unpair.
The ordinary finite controller tests the physically written flag before
decoding a nonempty list cell. Empty lists take the actual stop branch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawListStep
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (base : Fin 23 → List Bool) (flag : Bool) : Fin 24 → List Bool :=
  Fin.addCases (m := 23) (n := 1) (motive := fun _ => List Bool) base (fun _ => [flag])
def input (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool) (flag : Bool) :=
  tapes (RecoveryReusableUnpair.input bits resetCapacity backing) flag
def reduced (bits : List Bool) := RecoveryListPredecessor.result bits true
def reset1 (bits : List Bool) (resetCapacity : Nat) := max resetCapacity (2*bits.length+1)
def predOutput (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool) :=
  input (reduced bits) (reset1 bits resetCapacity) backing (decide (value bits≠0))
def predSlots : Fin 3 → Fin 24 := ![0,23,22]
def decodeSlots (i : Fin 23) : Fin 24 := i.castAdd 1
theorem predSlots_injective : Function.Injective predSlots := by decide
theorem decodeSlots_injective : Function.Injective decodeSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)

@[simp] theorem reduced_length (bits : List Bool) : (reduced bits).length=bits.length :=
  RecoveryListPredecessor.result_length bits true
theorem reduced_capacity (bits : List Bool) :
    RecoveryReusableUnpair.capacity (reduced bits)=RecoveryReusableUnpair.capacity bits := by
  simp [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity]

noncomputable def predMachine := RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def decodeMachine (left : Bool) := RecoveryFocus.machine decodeSlots (RecoveryDecodeStep.machine left)

theorem predecessor_ready (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool) (flag : Bool) :
    ReadyRun predMachine (4*bits.length+4) (input bits resetCapacity backing flag)
      (predOutput bits resetCapacity backing) := by
  have h := (RecoveryListPredecessor.predecessor_ready bits flag resetCapacity).focus predSlots
    predSlots_injective (input bits resetCapacity backing flag) (by intro j; fin_cases j <;> rfl)
  have he : install predSlots (input bits resetCapacity backing flag)
      ![frame (reduced bits),[decide (value bits≠0)],List.replicate (reset1 bits resetCapacity) false] =
      predOutput bits resetCapacity backing := by
    funext i
    fin_cases i
    case «0» => exact install_slot predSlots predSlots_injective _ _ 0
    case «22» => exact install_slot predSlots predSlots_injective _ _ 2
    case «23» => exact install_slot predSlots predSlots_injective _ _ 1
    case «21» =>
      rw [install_other predSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      exact congrArg (fun n => List.replicate n true) (reduced_capacity bits).symm
    all_goals first
      | (rw [install_other predSlots _ _ _ (by intro j; fin_cases j <;> decide)]
         change backing _=backing _
         rfl)
  unfold reduced reset1 at he
  rw [he] at h
  exact h

def decodeOutput (left : Bool) (bits : List Bool) (resetCapacity : Nat) :=
  tapes (RecoveryReusableUnpair.input (RecoveryChildSelection.word left (reduced bits))
    (max (reset1 bits resetCapacity) (RecoveryReusableUnpair.capacity (reduced bits)+1))
    (RecoveryChildSelection.backing (reduced bits) (reset1 bits resetCapacity))) (decide (value bits≠0))

theorem decode_ready (left : Bool) (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool)
    (hb : ∀ i,(backing i).length≤RecoveryReusableUnpair.capacity bits) :
    ReadyRun (decodeMachine left) (RecoveryDecodeStep.time (reduced bits))
      (predOutput bits resetCapacity backing) (decodeOutput left bits resetCapacity) := by
  have hb' : ∀ i,(backing i).length≤RecoveryReusableUnpair.capacity (reduced bits) := by
    intro i; rw [reduced_capacity]; exact hb i
  have h := (RecoveryDecodeStep.decode_ready left (reduced bits) (reset1 bits resetCapacity) backing hb').focus
    decodeSlots decodeSlots_injective (predOutput bits resetCapacity backing)
    (by intro j; simp [predOutput,input,tapes,decodeSlots])
  have he : install decodeSlots (predOutput bits resetCapacity backing)
      (RecoveryReusableUnpair.input (RecoveryChildSelection.word left (reduced bits))
        (max (reset1 bits resetCapacity) (RecoveryReusableUnpair.capacity (reduced bits)+1))
        (RecoveryChildSelection.backing (reduced bits) (reset1 bits resetCapacity))) =
      decodeOutput left bits resetCapacity := by
    funext i
    refine Fin.addCases (m := 23) (n := 1) (motive := fun j : Fin 24 =>
      install decodeSlots (predOutput bits resetCapacity backing) _ j=decodeOutput left bits resetCapacity j) ?_ ?_ i
    · intro j
      rw [decodeOutput,tapes,Fin.addCases_left]
      exact install_slot decodeSlots decodeSlots_injective _ _ j
    · intro j
      fin_cases j
      rw [install_other decodeSlots _ _ _ (by
        intro k hk
        have hv := congrArg (fun q : Fin 24 => q.val) hk
        simp only [decodeSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      change [decide (value bits≠0)]=[decide (value bits≠0)]
      rfl
  rw [he] at h
  exact h

abbrev decodeStates := Fintype.card (RecoveryCalls.Control RecoveryDecodeStep.sizes)
def sizes : Fin 2 → Nat := ![7,decodeStates]
noncomputable def programs (left : Bool) : (j : Fin 2) → Machine 24 (sizes j)
  | ⟨0,_⟩ => predMachine
  | ⟨1,_⟩ => decodeMachine left
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scanned : Fin 24 → Bool) : Option (Fin 2) :=
  if j.val=0 && scanned 23 then some 1 else none
noncomputable def machine (left : Bool) := RecoveryCalls.machine sizes (programs left) 0 next
def output (left : Bool) (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool) :=
  if value bits=0 then predOutput bits resetCapacity backing else decodeOutput left bits resetCapacity
def time (bits : List Bool) :=
  if value bits=0 then 4*bits.length+5 else (4*bits.length+5)+(RecoveryDecodeStep.time (reduced bits)+1)
def budget (bits : List Bool) := 131072*(bits.length+1)^2

theorem list_step_ready (left : Bool) (bits : List Bool) (resetCapacity : Nat)
    (backing : Fin 20 → List Bool) (flag : Bool)
    (hb : ∀ i,(backing i).length≤RecoveryReusableUnpair.capacity bits) :
    ReadyRun (machine left) (time bits) (input bits resetCapacity backing flag)
      (output left bits resetCapacity backing) := by
  have hin : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs left 0) (input bits resetCapacity backing flag)) =
      initialConfiguration (machine left) (input bits resetCapacity backing flag) := rfl
  by_cases hz : value bits=0
  · have h := (predecessor_ready bits resetCapacity backing flag).stop sizes (programs left) 0 next 0
      (by intro q; simp [next,predOutput,input,tapes,hz,readTapeBit,List.getD,Fin.addCases])
    rw [hin] at h
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa [time,hz,run,machine,Nat.add_assoc] using hr
    · simp [hf,RecoveryCalls.stopped,output,hz]
    · intro i; simp [hf,RecoveryCalls.stopped]
    · simpa [time,hz] using hs
  · have hp := (predecessor_ready bits resetCapacity backing flag).call sizes (programs left) 0 next 0 1
      (by intro q; simp [next,predOutput,input,tapes,hz,readTapeBit,List.getD,Fin.addCases])
    have hd := (decode_ready left bits resetCapacity backing hb).stop sizes (programs left) 0 next 1
      (by intro q; rfl)
    have h := hp.trans hd
    rw [hin] at h
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa [time,hz,run,machine,Nat.add_assoc] using hr
    · simp [hf,RecoveryCalls.stopped,output,hz]
    · intro i; simp [hf,RecoveryCalls.stopped]
    · simpa [time,hz] using hs

theorem time_bound (bits : List Bool) : time bits≤budget bits := by
  have h := RecoveryDecodeStep.time_bound (reduced bits)
  simp only [RecoveryDecodeStep.budget,reduced_length] at h
  unfold time budget
  split <;> nlinarith

theorem list_component (left : Bool) (bits : List Bool) (hz : value bits≠0) :
    value (RecoveryChildSelection.word left (reduced bits))=
      if left then (Nat.unpair (value bits-1)).1 else (Nat.unpair (value bits-1)).2 := by
  rw [RecoveryDecodeStep.child_value,reduced,RecoveryListPredecessor.predecessor_value bits hz]

end NearCubicWires.RepairOrdinary.RecoveryRawListStep
