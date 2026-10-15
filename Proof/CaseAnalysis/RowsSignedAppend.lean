import Proof.CaseAnalysis.RowsIntegerFields
import Proof.CaseAnalysis.WitnessNativeAppend

/-! Append the actual sign bit and already decoded native magnitude. This
is the source intWord format, copied in its binary representation length. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSignedAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sign : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then
      some ⟨1,fun _=>none,![.right,.stay,.stay,.stay]⟩
    else if q.val=1 then
      some ⟨2,![none,none,none,some (bits 0)],![.left,.stay,.stay,.right]⟩
    else none
def signInput (source magnitude backing out : List Bool) : Configuration 4 3:=
  ⟨0,![0,0,0,out.length],![source,magnitude,backing,out]⟩
def signed (source out : List Bool):=out++[readTapeBit source 1]
def signResult (source magnitude backing out : List Bool) : Configuration 4 3:=
  ⟨2,![0,0,0,(signed source out).length],![source,magnitude,backing,signed source out]⟩

theorem sign_run (source magnitude backing out : List Bool) : ∃ r,
    runFrom sign 2 (signInput source magnitude backing out)=some r ∧
      r.final=signResult source magnitude backing out ∧ r.steps=2:=by
  let middle : Configuration 4 3:=⟨1,![1,0,0,out.length],![source,magnitude,backing,out]⟩
  have h0:step sign (signInput source magnitude backing out)=some middle:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  have h1:step sign middle=some (signResult source magnitude backing out):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,middle,signResult,signed,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,middle,signResult,signed,Streaming.write_append,Configuration.scanned]
  exact ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)

def copySlots : Fin 3→Fin 4:=![1,2,3]
theorem copy_injective : Function.Injective copySlots:=by decide
noncomputable def copy:=RecoveryFocus.machine copySlots NativeAppend.machine
noncomputable def machine:=Composition.machine sign copy
def entry (source bits backing out : List Bool):=
  Composition.leftConfig 4 (signInput source (NativeWord.word bits) backing out)
def appended (source bits out : List Bool):=signed source out++NativeWord.word bits

theorem append_run (source bits backing out : List Bool) : ∃ r,
    runFrom machine (2*bits.length+8) (entry source bits backing out)=some r ∧
      r.steps ≤ 2*bits.length+8 ∧
      r.final.tapes 3=appended source bits out ∧
      r.final.heads 3=(appended source bits out).length ∧
      r.final.tapes 0=source ∧ r.final.heads 0=0:=by
  obtain ⟨a,ha,af,as⟩:=sign_run source (NativeWord.word bits) backing out
  obtain ⟨raw,hr,rf,rs⟩:=NativeAppend.append_run bits backing (signed source out)
  obtain ⟨b,hb,_,bs,bh,bt,bkeep⟩:=RecoveryFocus.dock copySlots copy_injective NativeAppend.machine
    _ a.final.heads a.final.tapes (NativeAppend.entry bits backing (signed source out))
    (by intro i;rw [af];fin_cases i <;> rfl)
    (by intro i;rw [af];fin_cases i <;> rfl) raw hr
  have h:=Composition.run_join sign copy _ _ _ a b ha hb
  have he:2+1+(2*bits.length+5)=2*bits.length+8:=by omega
  rw [he] at h
  refine ⟨_,h,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    rw [as,bs]
    omega
  · change b.final.tapes (copySlots 2)=_
    rw [bt,rf]
    rfl
  · change b.final.heads (copySlots 2)=_
    rw [bh,rf]
    rfl
  · change b.final.tapes 0=source
    rw [(bkeep 0 (by decide)).2,af]
    rfl
  · change b.final.heads 0=0
    rw [(bkeep 0 (by decide)).1,af]
    rfl

theorem sign_value (bits : List Bool) (b : Bool) (h : value bits=b.toNat) :
    readTapeBit (frame bits) 1=b:=by
  cases bits with
  | nil=>cases b <;> simp_all [value,frame,RepairOrdinary.frame,readTapeBit]
  | cons a bits=>
    cases a <;> cases b <;> simp_all [value,frame,RepairOrdinary.frame,readTapeBit]

theorem sign_of_decode (bits : List Bool) (z : ℤ)
    (hz : CanonicalBinary.decodeInt (value bits)=some z) :
    readTapeBit (frame (RecoveryFixedUnpair.leftWord bits)) 1=decide (z<0):=by
  apply sign_value
  have hc:=CanonicalBinary.encodeInt_of_decode hz
  rw [(RecoveryFixedUnpair.word_values bits).1,←hc,CanonicalBinary.encodeInt,Nat.unpair_pair]
  by_cases h:z<0 <;> simp [h]

end NearCubicWires.RepairOrdinary.CloseoutRowsSignedAppend
