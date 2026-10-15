import Proof.CaseAnalysis.RowsIntegerMeaning
import Proof.CaseAnalysis.RowsIntegerTests

/-! The cold canonical integer guard combines the actual retained natural
flag with the three actual binary tests. Its verdict equals decodeInt on
every raw word, and it retains the exact native magnitude for the row source. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics CloseoutWitness
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldsSlots (i : Fin 203) : Fin 212:=i.castAdd 9
def testSlots (i : Fin 10) : Fin 212:=
  if i.val=0 then 17 else if i.val=1 then 194 else ⟨201+i.val,by omega⟩
theorem fields_injective : Function.Injective fieldsSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 212=>x.val) h)
theorem tests_injective : Function.Injective testSlots:=by decide
def input (bits : List Bool) : Fin 212→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (203+9)=>List Bool) (CloseoutRowsIntegerFields.input bits) (fun _=>[])
noncomputable def fields:=RecoveryFocus.machine fieldsSlots CloseoutRowsIntegerFields.machine
noncomputable def tests:=RecoveryFocus.machine testSlots CloseoutRowsIntegerTests.machine
noncomputable def prefixMachine:=Composition.machine fields tests
noncomputable def middle (bits : List Bool) (base : Fin 203→List Bool):=install fieldsSlots (input bits) base

theorem middle_old (bits : List Bool) (base : Fin 203→List Bool) (i : Fin 203) :
    middle bits base (fieldsSlots i)=base i:=install_slot _ fields_injective _ _ _
theorem middle_new (bits : List Bool) (base : Fin 203→List Bool) (i : Fin 212) (hi : 203 ≤ i.val) :
    middle bits base i=[]:=by
  rw [middle,install_other _ _ _ _ (by
    intro j he
    have hv:=congrArg Fin.val he
    change j.val=i.val at hv
    omega)]
  simp [input,Fin.addCases,show ¬i.val<203 by omega]

def finish : Machine 212 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some ⟨1,fun i=>if i=211 then some (bits 195 && (bits 205 || (bits 206 && !bits 207))) else none,
      fun _=>.stay⟩ else none
def finished (bank : Fin 212→List Bool):=Function.update bank 211
  [readTapeBit (bank 195) 0 && (readTapeBit (bank 205) 0 ||
    (readTapeBit (bank 206) 0 && !readTapeBit (bank 207) 0))]
theorem finish_run (bank : Fin 212→List Bool) (hb : bank 211=[]) :
    ClockJoin.ReadyRun finish 1 bank (finished bank):=by
  let final : Configuration 212 2:=⟨1,fun _=>0,finished bank⟩
  have hs:step finish (initialConfiguration finish bank)=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=211
      · subst i
        simp [applyAction,initialConfiguration,finish,final,finished,Configuration.scanned,hb,writeTapeBit]
      · simp [applyAction,initialConfiguration,finish,final,finished,hi]
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩
noncomputable def machine:=Composition.machine prefixMachine finish
def payload (bits : List Bool):=BitFields.payload (RecoveryFixedUnpair.rightWord bits)
def budget (bits : List Bool):=CloseoutRowsIntegerFields.budget bits+24*bits.length+51
theorem payload_bound (bits : List Bool) : (payload bits).length ≤ bits.length+1:=by
  have h:=Reencode.count_bound (RecoveryFixedUnpair.rightWord bits)
  simpa only [payload,BitFields.payload,Reencode.fields,List.length_map,
    TraversalCounted.count,(RecoveryFixedUnpair.word_lengths bits).2] using h

theorem guard_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      (readTapeBit (output 211) 0=true ↔ (CanonicalBinary.decodeInt (value bits)).isSome) ∧
      output 17=frame (RecoveryFixedUnpair.leftWord bits) ∧
      output 194=frame (payload bits) ∧
      output 200=NativeWord.word (payload bits) ∧
      (∀ z,CanonicalBinary.decodeInt (value bits)=some z → output 200=RepairRepresentation.natWord z.natAbs):=by
  obtain ⟨base,hbase,hs,hw,hmag,hflag,hn⟩:=CloseoutRowsIntegerFields.fields_run bits
  have hf:=bounded_focus fieldsSlots fields_injective _ _ _ hbase (input bits)
    (by intro i;simp only [input,fieldsSlots,Fin.addCases_left])
  obtain ⟨out,ho,os,om,hz,h1,hm⟩:=CloseoutRowsIntegerTests.tests_run (RecoveryFixedUnpair.leftWord bits) (payload bits)
  have hinput:∀ i,middle bits base (testSlots i)=
      CloseoutRowsIntegerTests.input (RecoveryFixedUnpair.leftWord bits) (payload bits) i:=by
    intro i;fin_cases i
    · exact (middle_old bits base 17).trans hs
    · exact (middle_old bits base 194).trans hmag
    all_goals exact middle_new _ _ _ (by decide)
  have ht:=bounded_focus testSlots tests_injective _ _ _ ho (middle bits base) hinput
  let bank:=install testSlots (middle bits base) out
  have keep (i : Fin 203) (hi : ∀ j,testSlots j≠fieldsSlots i) : bank (fieldsSlots i)=base i:=by
    change install testSlots (middle bits base) out (fieldsSlots i)=base i
    rw [install_other _ _ _ _ hi]
    exact middle_old _ _ _
  have hb:bank 211=[]:=by
    change install testSlots (middle bits base) out 211=[]
    rw [install_other _ _ _ _ (by decide)]
    exact middle_new _ _ _ (by decide)
  have prefixRun:=ClockJoin.join fields tests _ _ _ _ _ hf ht
  have full:=ClockJoin.join prefixMachine finish _ _ _ _ _ prefixRun (finish_run bank hb)
  have timeBound:(CloseoutRowsIntegerFields.budget bits+1+
      CloseoutRowsIntegerTests.budget (RecoveryFixedUnpair.leftWord bits) (payload bits))+1+1 ≤ budget bits:=by
    have hp:=payload_bound bits
    unfold CloseoutRowsIntegerTests.budget budget
    rw [(RecoveryFixedUnpair.word_lengths bits).1]
    omega
  have more:=ClockJoin.enlarge machine _ (budget bits) _ _ full timeBound
  refine ⟨finished bank,more,?_,?_,?_,?_,?_⟩
  · change (readTapeBit (bank 195) 0 && (readTapeBit (bank 205) 0 ||
      (readTapeBit (bank 206) 0 && !readTapeBit (bank 207) 0)))=true ↔ _
    have b195:bank 195=base 195:=keep 195 (by decide)
    have b205:bank 205=out 4:=install_slot _ tests_injective _ _ 4
    have b206:bank 206=out 5:=install_slot _ tests_injective _ _ 5
    have b207:bank 207=out 6:=install_slot _ tests_injective _ _ 6
    rw [b195,b205,b206,b207,hz,h1,hm]
    rw [←CloseoutRowsIntegerMeaning.valid_iff]
    simp only [readTapeBit,List.getD,List.getElem?_cons_zero,Option.getD_some,
      Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
    exact and_congr hflag Iff.rfl
  · change bank (testSlots 0)=_
    exact (install_slot _ tests_injective _ _ 0).trans os
  · change bank (testSlots 1)=_
    exact (install_slot _ tests_injective _ _ 1).trans om
  · change bank (fieldsSlots 200)=_
    exact (keep 200 (by decide)).trans hw
  · intro z hz
    change bank (fieldsSlots 200)=_
    exact (keep 200 (by decide)).trans (hn z hz)

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerGuard
