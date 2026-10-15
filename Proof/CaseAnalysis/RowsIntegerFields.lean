import Proof.CaseAnalysis.WitnessNativePayload

/-! Direct canonical signed-integer fields for the normalized row source.
The existing binary unpair feeds the existing natural decoder on the same
physical tapes. No integer magnitude is expanded to a unary numeric value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerFields
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def splitSlots (i : Fin 21) : Fin 203:=i.castAdd 182
def nativeSlots (i : Fin 183) : Fin 203:=
  if i.val=0 then 18 else ⟨i.val+20,by omega⟩
theorem native_val (i : Fin 183) :
    (nativeSlots i).val=if i.val=0 then 18 else i.val+20:=by
  unfold nativeSlots
  split <;> rfl
theorem split_injective : Function.Injective splitSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 203=>k.val) h)
theorem native_injective : Function.Injective nativeSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [native_val,native_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

def input (bits : List Bool) : Fin 203→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (21+182)=>List Bool)
    (RecoveryFixedUnpair.input bits) (fun _=>[])
noncomputable def split:=RecoveryFocus.machine splitSlots RecoveryFixedUnpair.machine
noncomputable def native:=RecoveryFocus.machine nativeSlots NatNative.machine
noncomputable def machine:=Composition.machine split native
noncomputable def middle (bits : List Bool):=
  install splitSlots (input bits) (RecoveryFixedUnpair.output3 bits)

theorem middle_old (bits : List Bool) (i : Fin 21) :
    middle bits (splitSlots i)=RecoveryFixedUnpair.output3 bits i:=
  install_slot _ split_injective _ _ _
theorem middle_new (bits : List Bool) (i : Fin 203) (hi : 21 ≤ i.val) :
    middle bits i=[]:=by
  rw [middle,install_other _ _ _ _ (by
    intro j he
    have hv:=congrArg Fin.val he
    simp only [splitSlots,Fin.val_castAdd] at hv
    omega)]
  simp [input,Fin.addCases,show ¬i.val<21 by omega]

theorem cold_input (bits : List Bool) (i : Fin 183) :
    NatNative.input bits i=if i.val=0 then frame bits else []:=by
  fin_cases i <;> rfl

theorem native_input (bits : List Bool) :
    ∀ i,middle bits (nativeSlots i)=NatNative.input (RecoveryFixedUnpair.rightWord bits) i:=by
  intro i
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    exact middle_old bits 18
  · rw [nativeSlots,if_neg hi,middle_new _ _ (by dsimp;omega)]
    rw [cold_input,if_neg hi]

def time (bits : List Bool):=RecoveryFixedUnpair.time bits+1+
  NatNative.budget (RecoveryFixedUnpair.rightWord bits)
def budget (bits : List Bool):=18000000000000010000*(bits.length+1)^24
theorem time_bound (bits : List Bool) : time bits ≤ budget bits:=by
  have hs:=RecoveryFixedUnpair.time_bound bits
  have hp:(bits.length+1)^2 ≤ (bits.length+1)^24:=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hpos:1 ≤ (bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold time budget NatNative.budget RecoveryFixedUnpair.budget at *
  rw [(RecoveryFixedUnpair.word_lengths bits).2]
  omega

theorem fields_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 17=frame (RecoveryFixedUnpair.leftWord bits) ∧
      output (nativeSlots 180)=NativeWord.word (BitFields.payload (RecoveryFixedUnpair.rightWord bits)) ∧
      output (nativeSlots 174)=frame (BitFields.payload (RecoveryFixedUnpair.rightWord bits)) ∧
      (readTapeBit (output (nativeSlots 175)) 0=true ↔
        (CanonicalBinary.decodeNat (value (RecoveryFixedUnpair.rightWord bits))).isSome) ∧
      (∀ z,CanonicalBinary.decodeInt (value bits)=some z →
        output (nativeSlots 180)=RepairRepresentation.natWord z.natAbs) := by
  obtain ⟨first,hfirst,ft,fh,fs⟩:=RecoveryFixedUnpair.fixed_unpair_ready bits
  have hs:=bounded_focus splitSlots split_injective _ _ _
    ⟨first,hfirst,ft,fh,fs.le⟩ (input bits)
    (by intro i;simp only [input,splitSlots,Fin.addCases_left])
  obtain ⟨out,ho,hw,hflag,hnat⟩:=NatNative.nat_run (RecoveryFixedUnpair.rightWord bits)
  have hn:=bounded_focus nativeSlots native_injective _ _ _ ho (middle bits) (native_input bits)
  have h:=ClockJoin.join split native _ _ _ _ _ hs hn
  have more:=ClockJoin.enlarge machine (time bits) (budget bits) _ _ h (time_bound bits)
  let output:=install nativeSlots (middle bits) out
  have h17:output 17=frame (RecoveryFixedUnpair.leftWord bits):=by
    change install nativeSlots (middle bits) out 17=frame (RecoveryFixedUnpair.leftWord bits)
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      rw [native_val] at hv
      split_ifs at hv <;> omega)]
    exact middle_old bits 17
  refine ⟨output,more,h17,?_,?_,?_,?_⟩
  · exact (install_slot _ native_injective _ _ 180).trans hw
  · exact (install_slot _ native_injective _ _ 174).trans (NativePayload.nat_payload _ _ ho)
  · change readTapeBit (install nativeSlots (middle bits) out (nativeSlots 175)) 0=true ↔ _
    rw [install_slot _ native_injective]
    exact hflag
  · intro z hz
    change install nativeSlots (middle bits) out (nativeSlots 180)=_
    rw [install_slot _ native_injective]
    apply hnat
    have hc:=CanonicalBinary.encodeInt_of_decode hz
    rw [(RecoveryFixedUnpair.word_values bits).2,←hc,CanonicalBinary.encodeInt,Nat.unpair_pair]
    exact CanonicalBinary.decodeNat_encode z.natAbs

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerFields
