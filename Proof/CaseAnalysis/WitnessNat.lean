import Proof.CaseAnalysis.WitnessCanonicalFields
import Proof.CaseAnalysis.WitnessBitFieldsReady

/-! One cold ordinary program decodes a canonical natural.  Its flag agrees
exactly with the public decoder on every raw input, and its output is a framed
binary value.  The source natWord serializer is a subsequent ABI conversion. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NatCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open CompetitorRationalProducts RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def canonSlots (i : Fin 174) : Fin 178:=i.castAdd 4
def readerSlots : Fin 6→Fin 178:=![30,41,174,175,176,177]
theorem canon_injective : Function.Injective canonSlots:=by
  intro i j h
  have hv:=congrArg (fun a : Fin 178=>a.val) h
  exact Fin.ext hv
theorem reader_injective : Function.Injective readerSlots:=by decide

def input (bits : List Bool) : Fin 178→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (174+4)=>List Bool) (CanonicalTest.input bits) (fun _=>[])
noncomputable def canonical:=RecoveryFocus.machine canonSlots CanonicalTest.machine
noncomputable def reader:=RecoveryFocus.machine readerSlots BitFields.readyMachine
noncomputable def copied (bits : List Bool) (base : Fin 174→List Bool):=install canonSlots (input bits) base
noncomputable def primed (bits : List Bool) (base : Fin 174→List Bool):=Function.update (copied bits base) 175 [true]

theorem copied_old (bits : List Bool) (base : Fin 174→List Bool) (i : Fin 174) :
    copied bits base (canonSlots i)=base i:=install_slot _ canon_injective _ _ _
theorem copied_fresh (bits : List Bool) (base : Fin 174→List Bool) (i : Fin 178) (hi : 174 ≤ i.val) :
    copied bits base i=[]:=by
  rw [copied,install_other _ _ _ _ (by intro j he;have hv:=congrArg Fin.val he;dsimp [canonSlots] at hv;omega)]
  simp [input,Fin.addCases,show ¬i.val<174 by omega]

def prime : Machine 178 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=175 then some true else none,fun _=>.stay⟩ else none

theorem prime_ready (bits : List Bool) (base : Fin 174→List Bool) :
    ClockJoin.ReadyRun prime 1 (copied bits base) (primed bits base):=by
  let final:Configuration 178 2:=⟨1,fun _=>0,primed bits base⟩
  have hs:step prime (initialConfiguration prime (copied bits base))=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=175
      · subst i
        simp [applyAction,initialConfiguration,prime,final,primed,copied_fresh bits base 175 (by decide),writeTapeBit]
      · simp [applyAction,initialConfiguration,prime,final,primed,hi]
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht.le⟩

theorem reader_input (bits : List Bool) (base : Fin 174→List Bool)
    (hs : base 30=PCPPNativeCanonicalWalk.atomStream bits.length (PCPPNativeCanonicalTree.tree (value bits)).atoms)
    (hc : base 41=RepairSource.VerifierDecoding.CompareMachine.word (PCPPNativeCanonicalTree.tree (value bits)).atoms.length) :
    ∀ i,primed bits base (readerSlots i)=BitFields.readyInput (Reencode.fields bits) true i:=by
  intro i
  fin_cases i
  · change copied bits base (canonSlots 30)=FieldList.stream (Reencode.fields bits)
    rw [copied_old,Reencode.fields_stream,hs]
  · change copied bits base (canonSlots 41)=RepairSource.VerifierDecoding.CompareMachine.word (Reencode.fields bits).length
    rw [copied_old,hc]
    simp only [Reencode.fields,List.length_map]
  · change copied bits base 174=[]
    exact copied_fresh bits base _ (by decide)
  · change Function.update (copied bits base) 175 [true] 175=[true]
    simp
  · change copied bits base 176=[]
    exact copied_fresh bits base _ (by decide)
  · change copied bits base 177=[]
    exact copied_fresh bits base _ (by decide)

def finish : Machine 178 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some ⟨1,fun i=>if i=175 then some (bits 172 && bits 175) else none,fun _=>.stay⟩ else none
def finished (bank : Fin 178→List Bool) (flag : Bool):=
  Function.update bank 175 [readTapeBit (bank 172) 0 && flag]

theorem finish_ready (bank : Fin 178→List Bool) (flag : Bool) (hflag : bank 175=[flag]) :
    ClockJoin.ReadyRun finish 1 bank (finished bank flag):=by
  let final:Configuration 178 2:=⟨1,fun _=>0,finished bank flag⟩
  have hs:step finish (initialConfiguration finish bank)=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=175
      · subst i
        simp [applyAction,initialConfiguration,finish,final,finished,Configuration.scanned,hflag,readTapeBit,writeTapeBit]
      · simp [applyAction,initialConfiguration,finish,final,finished,hi]
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht.le⟩

noncomputable def prefixMachine:=Composition.machine canonical prime
noncomputable def body:=Composition.machine prefixMachine reader
noncomputable def machine:=Composition.machine body finish
def time (bits : List Bool):=CanonicalTest.budget bits+BitFields.readyTime (Reencode.fields bits)+5
def budget (bits : List Bool):=17000000000000000000*(bits.length+1)^24

theorem time_bound (bits : List Bool) : time bits ≤ budget bits:=by
  have h:=BitFields.raw_time_bound bits
  have hp:(bits.length+1)^2 ≤ (bits.length+1)^24:=Nat.pow_le_pow_right (by omega) (by decide)
  have hpos:1 ≤ (bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold time budget CanonicalTest.budget Reencode.polynomialBudget
  omega

theorem nat_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 174=frame (BitFields.payload bits) ∧
      output 41=RepairSource.VerifierDecoding.CompareMachine.word (BitFields.payload bits).length ∧
      (readTapeBit (output 175) 0=true ↔ (CanonicalBinary.decodeNat (value bits)).isSome) ∧
      (readTapeBit (output 175) 0=true→
        CanonicalBinary.decodeNat (value bits)=some (value (BitFields.payload bits))) := by
  obtain ⟨base,hbase,hstream,hcount,hcanonical⟩:=CanonicalTest.fields_run bits
  have hcan:=bounded_focus canonSlots canon_injective _ _ _ hbase (input bits) (by intro i;simp only [input,canonSlots,Fin.addCases_left])
  have hp:=ClockJoin.join canonical prime _ _ _ _ _ hcan (prime_ready bits base)
  obtain ⟨out,hout,_,hreaderCount,hbinary,hbool⟩:=BitFields.ready (Reencode.fields bits) true
  have hr:=bounded_focus readerSlots reader_injective _ _ _ hout (primed bits base)
    (reader_input bits base hstream hcount)
  let bank:=install readerSlots (primed bits base) out
  let flag:=true && (Reencode.fields bits).all BitFields.good && BitFields.last true (Reencode.fields bits)
  have hflag:bank 175=[flag]:=by
    change install readerSlots (primed bits base) out (readerSlots 3)=_
    rw [install_slot _ reader_injective,hbool]
  have h172:bank 172=base 172:=by
    change install readerSlots (primed bits base) out 172=_
    rw [install_other _ _ _ _ (by decide)]
    change copied bits base (canonSlots 172)=_
    exact copied_old _ _ _
  have hb:=ClockJoin.join prefixMachine reader _ _ _ _ _ hp hr
  have hf:=ClockJoin.join body finish _ _ _ _ _ hb (finish_ready bank flag hflag)
  have htime:((CanonicalTest.budget bits+1+1)+1+BitFields.readyTime (Reencode.fields bits))+1+1=time bits:=by
    unfold time
    omega
  rw [htime] at hf
  have more:=ClockJoin.enlarge machine (time bits) (budget bits) _ _ hf (time_bound bits)
  have hpass:readTapeBit (finished bank flag 175) 0=true ↔ BitFields.passes bits:=by
    change (readTapeBit (bank 172) 0 && flag)=true ↔ BitFields.passes bits
    rw [h172]
    simp only [Bool.and_eq_true,hcanonical,flag,Bool.true_and,BitFields.passes]
  refine ⟨finished bank flag,more,?_,?_,hpass.trans (BitFields.passes_iff bits),?_⟩
  · change install readerSlots (primed bits base) out (readerSlots 2)=frame (BitFields.payload bits)
    rw [install_slot _ reader_injective]
    exact hbinary
  · change install readerSlots (primed bits base) out (readerSlots 1)=RepairSource.VerifierDecoding.CompareMachine.word (BitFields.payload bits).length
    rw [install_slot _ reader_injective]
    simpa only [BitFields.payload,List.length_map] using hreaderCount
  · intro h
    exact BitFields.decode_of_passes bits (hpass.mp h)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NatCold
