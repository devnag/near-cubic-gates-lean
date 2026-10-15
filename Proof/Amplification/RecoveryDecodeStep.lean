import Proof.Amplification.RecoveryChildSelection

/-! One reusable scalar decoding step: physically erase, unpair, select and
overwrite the current code. Its output is exactly the next call's input ABI. -/
namespace NearCubicWires.RepairOrdinary.RecoveryDecodeStep
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev unpairStates := Fintype.card (RecoveryCalls.Control RecoveryReusableUnpair.sizes)
def sizes : Fin 2 → Nat := ![unpairStates,10]
noncomputable def programs (left : Bool) : (j : Fin 2) → Machine 23 (sizes j)
  | ⟨0,_⟩ => RecoveryReusableUnpair.machine
  | ⟨1,_⟩ => RecoveryChildSelection.machine left
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (_ : Fin 23 → Bool) : Option (Fin 2) :=
  if j.val=0 then some 1 else none
noncomputable def machine (left : Bool) := RecoveryCalls.machine sizes (programs left) 0 next
def time (bits : List Bool) := (RecoveryReusableUnpair.time bits+1)+(8*bits.length+10+1)
def budget (bits : List Bool) := 65536*(bits.length+1)^2

theorem decode_ready (left : Bool) (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool)
    (hb : ∀ i,(backing i).length≤RecoveryReusableUnpair.capacity bits) :
    ReadyRun (machine left) (time bits)
      (RecoveryReusableUnpair.input bits resetCapacity backing)
      (RecoveryReusableUnpair.input (RecoveryChildSelection.word left bits)
        (max resetCapacity (RecoveryReusableUnpair.capacity bits+1))
        (RecoveryChildSelection.backing bits resetCapacity)) := by
  have hu := (RecoveryReusableUnpair.reusable_ready bits resetCapacity backing hb).call
    sizes (programs left) 0 next 0 1 (by intro q; rfl)
  have hc := (RecoveryChildSelection.copy_ready left bits resetCapacity).stop
    sizes (programs left) 0 next 1 (by intro q; rfl)
  have h := hu.trans hc
  have hin : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs left 0) (RecoveryReusableUnpair.input bits resetCapacity backing)) =
      initialConfiguration (machine left) (RecoveryReusableUnpair.input bits resetCapacity backing) := rfl
  rw [hin] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨r,hr,?_,?_,hs⟩
  · simp only [hf,RecoveryCalls.stopped]
    exact RecoveryChildSelection.next_input left bits resetCapacity
  · intro i
    simp [hf,RecoveryCalls.stopped]

theorem time_bound (bits : List Bool) : time bits≤budget bits := by
  have h := RecoveryReusableUnpair.time_bound bits
  unfold time budget RecoveryReusableUnpair.budget at *
  nlinarith

theorem child_value (left : Bool) (bits : List Bool) :
    RadixSemantics.value (RecoveryChildSelection.word left bits)=
      if left then (Nat.unpair (RadixSemantics.value bits)).1 else (Nat.unpair (RadixSemantics.value bits)).2 := by
  cases left
  · exact (RecoveryFixedUnpair.word_values bits).2
  · exact (RecoveryFixedUnpair.word_values bits).1

theorem next_backing_bound (left : Bool) (bits : List Bool) (resetCapacity : Nat) (i : Fin 20) :
    (RecoveryChildSelection.backing bits resetCapacity i).length≤
      RecoveryReusableUnpair.capacity (RecoveryChildSelection.word left bits) := by
  simpa [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,RecoveryChildSelection.word_length]
    using RecoveryChildSelection.backing_bound bits resetCapacity i

end NearCubicWires.RepairOrdinary.RecoveryDecodeStep
