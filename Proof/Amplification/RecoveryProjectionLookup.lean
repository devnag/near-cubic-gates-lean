import Proof.Amplification.RecoveryProjectionMeaning

/-! The actual normalized-projection evaluator unpairs its code and looks
up the decoded random-bit index. The literal tag/code fields survive for
the checked selector. Its enclosing repeated emitter owns the backing. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionEval
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 21) : Fin 28 := i.castAdd 7
def lookupSlots : Fin 6→Fin 28 := ![18,22,23,21,24,25]
def selectSlots : Fin 5→Fin 28 := ![17,0,24,26,27]
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 28=>i.val) h)
theorem lookup_injective : Function.Injective lookupSlots := by decide
theorem select_injective : Function.Injective selectSlots := by decide

def input (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat) : Fin 28→List Bool :=
  fun i=>Fin.addCases (m:=21) (n:=7) (motive:=fun _=>List Bool) (RecoveryFixedUnpair.input bits)
    ![frame randomness,[flag],List.replicate cap false,[picked],List.replicate cap false,[old],[]] i
noncomputable def decoded (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat) :=
  install nativeSlots (input bits randomness flag picked old cap) (RecoveryFixedUnpair.output3 bits)
def pickedBit (bits randomness : List Bool) := (value randomness).testBit (Nat.unpair (value bits)).2
noncomputable def unpairMachine := RecoveryFocus.machine nativeSlots RecoveryFixedUnpair.machine
noncomputable def lookupMachine := RecoveryFocus.machine lookupSlots RecoveryCommittedBit.machine
noncomputable def selectMachine := RecoveryFocus.machine selectSlots RecoveryProjectionSelect.machine

theorem decoded_native (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat) (j : Fin 21) :
    decoded bits randomness flag picked old cap (nativeSlots j)=RecoveryFixedUnpair.output3 bits j :=
  install_slot _ native_injective _ _ _

theorem decoded_extra (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat) (j : Fin 7) :
    decoded bits randomness flag picked old cap (j.natAdd 21)=
      ![frame randomness,[flag],List.replicate cap false,[picked],List.replicate cap false,[old],[]] j := by
  rw [decoded,install_other _ _ _ _ (by
    intro i he
    have hv:=congrArg Fin.val he
    have hi:=i.isLt
    simp only [nativeSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega)]
  simp only [input,Fin.addCases_right]

theorem unpair_ready (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat) :
    ClockJoin.ReadyRun unpairMachine (RecoveryFixedUnpair.time bits)
      (input bits randomness flag picked old cap) (decoded bits randomness flag picked old cap) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryFixedUnpair.fixed_unpair_ready bits
  have h : ClockJoin.ReadyRun RecoveryFixedUnpair.machine (RecoveryFixedUnpair.time bits)
      (RecoveryFixedUnpair.input bits) (RecoveryFixedUnpair.output3 bits) := ⟨r,hr,ht,hh,hs.le⟩
  exact h.focus nativeSlots native_injective _ (by intro i; simp only [input,nativeSlots,Fin.addCases_left])

theorem decoded_lookup (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat) (j : Fin 6) :
    decoded bits randomness flag picked old cap (lookupSlots j)=
      ![frame (RecoveryFixedUnpair.rightWord bits),[flag],List.replicate cap false,
        frame randomness,[picked],List.replicate cap false] j := by
  fin_cases j
  · exact decoded_native bits randomness flag picked old cap 18
  · exact decoded_extra bits randomness flag picked old cap 1
  · exact decoded_extra bits randomness flag picked old cap 2
  · exact decoded_extra bits randomness flag picked old cap 0
  · exact decoded_extra bits randomness flag picked old cap 3
  · exact decoded_extra bits randomness flag picked old cap 4

theorem lookup_ready (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat)
    (hw : 2*bits.length+1 ≤ cap)
    (hc : RecoveryCommittedBit.rawCost (RecoveryFixedUnpair.rightWord bits) randomness ≤ cap) : ∃ out,
    ClockJoin.ReadyRun lookupMachine (2*RecoveryCommittedBit.rawCost (RecoveryFixedUnpair.rightWord bits) randomness+2)
      (decoded bits randomness flag picked old cap) out ∧
      ∀ j,out (selectSlots j)=
        ![frame (RecoveryFixedUnpair.leftWord bits),frame bits,[pickedBit bits randomness],[old],[]] j := by
  obtain ⟨r,hr,hs,hh,remainder,newflag,_hlen,ht⟩ := RecoveryCommittedBit.lookup_run
    (RecoveryFixedUnpair.rightWord bits) randomness flag picked cap
    (by rw [(RecoveryFixedUnpair.word_lengths bits).2]; exact hw) hc
  have h : ClockJoin.ReadyRun RecoveryCommittedBit.machine
      (2*RecoveryCommittedBit.rawCost (RecoveryFixedUnpair.rightWord bits) randomness+2)
      ![frame (RecoveryFixedUnpair.rightWord bits),[flag],List.replicate cap false,
        frame randomness,[picked],List.replicate cap false] r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hf := h.focus lookupSlots lookup_injective _ (decoded_lookup bits randomness flag picked old cap)
  refine ⟨_,hf,?_⟩
  intro j
  fin_cases j
  · rw [install_other _ _ _ _ (by decide)]
    exact decoded_native bits randomness flag picked old cap 17
  · rw [install_other _ _ _ _ (by decide)]
    exact decoded_native bits randomness flag picked old cap 0
  · change install lookupSlots _ _ (lookupSlots 4)=_
    rw [install_slot _ lookup_injective,ht]
    change [(value randomness).testBit (value (RecoveryFixedUnpair.rightWord bits))]=[pickedBit bits randomness]
    rw [(RecoveryFixedUnpair.word_values bits).2]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    exact decoded_extra bits randomness flag picked old cap 5
  · rw [install_other _ _ _ _ (by decide)]
    exact decoded_extra bits randomness flag picked old cap 6

end NearCubicWires.RepairSource.RecoveryProjectionEval
