import Proof.Amplification.RecoveryCellStore

/-! Actual raw-cell consumer: reject/stop on empty input, otherwise decode the
tail back to input0 and preserve the head in external storage before scratch
can be erased. This is the reusable cell loop needed by the clause checker. -/
namespace NearCubicWires.RepairOrdinary.RecoveryStoredListCell
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 24) : Fin 25 := i.castAdd 1
theorem slots_injective : Function.Injective slots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 25 => k.val) h)
noncomputable def cellMachine := RecoveryFocus.machine slots (RecoveryRawListStep.machine false)
def input (bits saved : List Bool) (capacity : Nat) (backing : Fin 20 → List Bool) (flag : Bool) :=
  RecoveryCellStore.tapes (RecoveryRawListStep.input bits capacity backing flag) saved
def middle (bits saved : List Bool) (capacity : Nat) (backing : Fin 20 → List Bool) :=
  RecoveryCellStore.tapes (RecoveryRawListStep.output false bits capacity backing) saved

theorem cell_ready (bits saved : List Bool) (capacity : Nat) (backing : Fin 20 → List Bool) (flag : Bool)
    (hb : ∀ i,(backing i).length≤RecoveryReusableUnpair.capacity bits) :
    ReadyRun cellMachine (RecoveryRawListStep.time bits) (input bits saved capacity backing flag)
      (middle bits saved capacity backing) := by
  have h := (RecoveryRawListStep.list_step_ready false bits capacity backing flag hb).focus
    slots slots_injective (input bits saved capacity backing flag) (by
      intro j; simp [input,RecoveryCellStore.tapes,slots])
  have he : install slots (input bits saved capacity backing flag)
      (RecoveryRawListStep.output false bits capacity backing)=middle bits saved capacity backing := by
    funext i
    refine Fin.addCases (m := 24) (n := 1) (motive := fun j : Fin 25 =>
      install slots (input bits saved capacity backing flag) _ j=middle bits saved capacity backing j) ?_ ?_ i
    · intro j
      rw [middle,RecoveryCellStore.tapes,Fin.addCases_left]
      exact install_slot slots slots_injective _ _ j
    · intro j
      fin_cases j
      rw [install_other slots _ _ _ (by
        intro k hk
        have hv := congrArg (fun q : Fin 25 => q.val) hk
        simp only [slots,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      rfl
  rw [he] at h
  exact h

abbrev cellStates := Fintype.card (RecoveryCalls.Control RecoveryRawListStep.sizes)
def sizes : Fin 2 → Nat := ![cellStates,10]
noncomputable def programs : (j : Fin 2) → Machine 25 (sizes j)
  | ⟨0,_⟩ => cellMachine
  | ⟨1,_⟩ => RecoveryCellStore.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scanned : Fin 25 → Bool) : Option (Fin 2) :=
  if j.val=0 && scanned 23 then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def output (bits saved : List Bool) (capacity : Nat) (backing : Fin 20 → List Bool) :=
  if value bits=0 then middle bits saved capacity backing
  else RecoveryCellStore.tapes (RecoveryCellStore.base bits capacity) (frame (RecoveryCellStore.headWord bits))
def time (bits : List Bool) := RecoveryRawListStep.time bits+1+
  if value bits=0 then 0 else 8*bits.length+11
def budget (bits : List Bool) := 262144*(bits.length+1)^2

theorem stored_cell_ready (bits saved : List Bool) (capacity : Nat)
    (backing : Fin 20 → List Bool) (flag : Bool)
    (hb : ∀ i,(backing i).length≤RecoveryReusableUnpair.capacity bits)
    (hsaved : saved.length≤2*bits.length+1) :
    ReadyRun machine (time bits) (input bits saved capacity backing flag)
      (output bits saved capacity backing) := by
  have hin : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs 0) (input bits saved capacity backing flag))=
      initialConfiguration machine (input bits saved capacity backing flag) := rfl
  by_cases hz : value bits=0
  · have h := (cell_ready bits saved capacity backing flag hb).stop sizes programs 0 next 0
      (by intro q; simp [next,middle,RecoveryCellStore.tapes,RecoveryRawListStep.output,hz,
        RecoveryRawListStep.predOutput,RecoveryRawListStep.input,RecoveryRawListStep.tapes,
        Fin.addCases,readTapeBit,List.getD])
    rw [hin] at h
    obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,by simpa [time,hz,run,machine] using hr,?_,?_,by simpa [time,hz] using ht⟩
    · simp [hf,RecoveryCalls.stopped,output,hz]
    · intro i; simp [hf,RecoveryCalls.stopped]
  · have hc := (cell_ready bits saved capacity backing flag hb).call sizes programs 0 next 0 1
      (by intro q; simp [next,middle,RecoveryCellStore.tapes,RecoveryRawListStep.output,hz,
        RecoveryRawListStep.decodeOutput,RecoveryRawListStep.tapes,Fin.addCases,readTapeBit,List.getD])
    have hs := (RecoveryCellStore.copy_ready bits saved capacity hsaved).stop sizes programs 0 next 1
      (by intro q; rfl)
    have hm : middle bits saved capacity backing=
        RecoveryCellStore.tapes (RecoveryCellStore.base bits capacity) saved := by
      simp [middle,RecoveryRawListStep.output,hz,RecoveryCellStore.base]
    rw [hm] at hc
    have h := hc.trans hs
    rw [hin] at h
    obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,by simpa [time,hz,run,machine,Nat.add_assoc] using hr,?_,?_,by simpa [time,hz,Nat.add_assoc] using ht⟩
    · simp [hf,RecoveryCalls.stopped,output,hz]
    · intro i; simp [hf,RecoveryCalls.stopped]

theorem time_bound (bits : List Bool) : time bits≤budget bits := by
  have h := RecoveryRawListStep.time_bound bits
  have hp : 0<(bits.length+1)^2 := by positivity
  unfold time budget RecoveryRawListStep.budget at *
  split <;> nlinarith

end NearCubicWires.RepairOrdinary.RecoveryStoredListCell
