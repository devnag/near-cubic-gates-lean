import Proof.CaseAnalysis.WitnessNat
import Proof.CaseAnalysis.WitnessNativeWord

/-! The typed-node field consumer gets the exact source natWord from the
original canonical code. Both the decoder test and all-raw cost are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NatNative
open LocalBitMultitape RadixSemantics CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldSlots (i : Fin 178) : Fin 183:=i.castAdd 5
def nativeSlots : Fin 7→Fin 183:=![174,41,178,179,180,181,182]
theorem cold_injective : Function.Injective coldSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 183=>a.val) h)
theorem native_injective : Function.Injective nativeSlots:=by decide
def input (bits : List Bool) : Fin 183→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (178+5)=>List Bool) (NatCold.input bits) (fun _=>[])
noncomputable def cold:=RecoveryFocus.machine coldSlots NatCold.machine
noncomputable def native:=RecoveryFocus.machine nativeSlots NativeWord.machine
noncomputable def machine:=Composition.machine cold native
noncomputable def copied (bits : List Bool) (base : Fin 178→List Bool):=
  RecoveryRootRound.install coldSlots (input bits) base

theorem copied_fresh (bits : List Bool) (base : Fin 178→List Bool) (i : Fin 183) (hi : 178 ≤ i.val) :
    copied bits base i=[]:=by
  rw [copied,RecoveryRootRound.install_other _ _ _ _ (by
    intro j he
    have hv:=congrArg Fin.val he
    dsimp [coldSlots] at hv
    omega)]
  simp [input,Fin.addCases,show ¬i.val<178 by omega]

theorem native_input (bits : List Bool) (base : Fin 178→List Bool)
    (hb : base 174=frame (BitFields.payload bits))
    (hc : base 41=RepairSource.VerifierDecoding.CompareMachine.word (BitFields.payload bits).length) :
    ∀ i,copied bits base (nativeSlots i)=NativeWord.input (BitFields.payload bits) i:=by
  intro i
  fin_cases i
  · change RecoveryRootRound.install coldSlots (input bits) base (coldSlots 174)=_
    rw [RecoveryRootRound.install_slot _ cold_injective]
    exact hb
  · change RecoveryRootRound.install coldSlots (input bits) base (coldSlots 41)=_
    rw [RecoveryRootRound.install_slot _ cold_injective]
    exact hc
  all_goals exact copied_fresh bits base _ (by decide)

def budget (bits : List Bool):=18000000000000000000*(bits.length+1)^24
theorem time_bound (bits : List Bool) :
    NatCold.budget bits+1+NativeWord.budget (BitFields.payload bits) ≤ budget bits:=by
  have hc:=Reencode.count_bound bits
  have hl:(BitFields.payload bits).length ≤ bits.length+1:=by
    simpa only [BitFields.payload,Reencode.fields,List.length_map,TraversalCounted.count] using hc
  have hp:bits.length+1 ≤ (bits.length+1)^24:=by
    simpa using Nat.pow_le_pow_right (by omega : 0<bits.length+1) (by decide : 1 ≤ 24)
  have hpos:1 ≤ (bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold NatCold.budget NativeWord.budget budget
  omega

theorem nat_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 180=NativeWord.word (BitFields.payload bits) ∧
      (readTapeBit (output 175) 0=true ↔ (CanonicalBinary.decodeNat (value bits)).isSome) ∧
      (∀ n,CanonicalBinary.decodeNat (value bits)=some n → output 180=RepairRepresentation.natWord n) := by
  obtain ⟨base,hb,hbinary,hcount,hflag,hdecode⟩:=NatCold.nat_run bits
  have hc:=bounded_focus coldSlots cold_injective _ _ _ hb (input bits)
    (by intro i;simp only [input,coldSlots,Fin.addCases_left])
  obtain ⟨out,ho,hword⟩:=NativeWord.word_run (BitFields.payload bits)
  have hn:=bounded_focus nativeSlots native_injective _ _ _ ho (copied bits base)
    (native_input bits base hbinary hcount)
  have hall:=ClockJoin.join cold native _ _ _ _ _ hc hn
  have more:=ClockJoin.enlarge machine _ (budget bits) _ _ hall (time_bound bits)
  let output:=RecoveryRootRound.install nativeSlots (copied bits base) out
  have h175:output 175=base 175:=by
    change RecoveryRootRound.install nativeSlots (copied bits base) out 175=base 175
    rw [RecoveryRootRound.install_other _ _ _ _ (by decide)]
    change RecoveryRootRound.install coldSlots (input bits) base (coldSlots 175)=_
    exact RecoveryRootRound.install_slot _ cold_injective _ _ _
  have h180:output 180=NativeWord.word (BitFields.payload bits):=by
    change RecoveryRootRound.install nativeSlots (copied bits base) out (nativeSlots 4)=_
    rw [RecoveryRootRound.install_slot _ native_injective,hword]
  refine ⟨output,more,h180,by rw [h175];exact hflag,?_⟩
  intro n hd
  have hp:BitFields.payload bits=n.bits:=
    (BitFields.encoded_passes bits n (CanonicalBinary.encodeNat_of_decode hd).symm).2
  rw [h180,hp,NativeWord.word_eq _ (CanonicalBinary.Nat.bits_canonical n)]
  have hv:RadixSemantics.value n.bits=n:=by
    have h:=hdecode (hflag.mpr (Option.isSome_iff_exists.mpr ⟨n,hd⟩))
    rw [hp,hd] at h
    exact (Option.some.inj h).symm
  rw [hv]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NatNative
