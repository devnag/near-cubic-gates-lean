import Proof.CaseAnalysis.WitnessPairHeader
import Proof.CaseAnalysis.RowsIntegerGuard

/-! The same raw rational code reaches its exact tagged pair, canonical
signed numerator, and canonical denominator. The magnitude payloads remain
binary; the next consumer guards their widths before running gcd. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 149) : Fin 539:=i.castAdd 390
def integerSlots (i : Fin 212) : Fin 539:=if i.val=0 then 38 else ⟨149+i.val,by omega⟩
def naturalSlots (i : Fin 178) : Fin 539:=if i.val=0 then 78 else ⟨361+i.val,by omega⟩
theorem integer_val (i : Fin 212) : (integerSlots i).val=if i.val=0 then 38 else 149+i.val:=by
  unfold integerSlots
  split_ifs <;> rfl
theorem natural_val (i : Fin 178) : (naturalSlots i).val=if i.val=0 then 78 else 361+i.val:=by
  unfold naturalSlots
  split_ifs <;> rfl
theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 539=>k.val) h)
theorem integer_injective : Function.Injective integerSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [integer_val,integer_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem natural_injective : Function.Injective naturalSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [natural_val,natural_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

def numeratorWord (bits : List Bool):=PairHeader.codeWord bits 0
def denominatorWord (bits : List Bool):=PairHeader.codeWord bits 1
def numerator (bits : List Bool):=CloseoutRowsIntegerGuard.payload (numeratorWord bits)
def denominator (bits : List Bool):=BitFields.payload (denominatorWord bits)
def input (bits : List Bool) (i : Fin 539):=if i.val=1 then frame bits else []
def booted (bits : List Bool):=Function.update (input bits) 0 [false]
noncomputable def headerDone (bits : List Bool):=install headerSlots (booted bits) (PairHeader.output bits)
noncomputable def integerDone (bits : List Bool) (out : Fin 212→List Bool):=install integerSlots (headerDone bits) out
noncomputable def result (bits : List Bool) (z : Fin 212→List Bool) (d : Fin 178→List Bool):=
  install naturalSlots (integerDone bits z) d

theorem header_input (bits : List Bool) (i : Fin 149) :
    booted bits (headerSlots i)=PairHeader.input bits i:=by
  refine Fin.addCases (m:=148) (n:=1) ?_ ?_ i
  · intro j
    rw [PairHeader.input,Fin.addCases_left,CompetitorWitnessHeader.input_eq]
    by_cases hj:j.val=0
    · have he:j=0:=Fin.ext hj
      subst j
      rfl
    · have hn:headerSlots (j.castAdd 1)≠0:=by intro h;exact hj (congrArg Fin.val h)
      rw [booted,Function.update_of_ne hn,if_neg hj]
      rfl
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl
theorem header_fresh (bits : List Bool) (i : Fin 539) (hi : 149 ≤ i.val) : headerDone bits i=[]:=by
  rw [headerDone,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;change j.val=i.val at hv;omega)]
  have hn:i≠0:=by intro h;have hv:=congrArg Fin.val h;omega
  simp only [booted,Function.update_of_ne hn,input,if_neg (show i.val≠1 by omega)]
theorem integer_input (bits : List Bool) (i : Fin 212) :
    headerDone bits (integerSlots i)=CloseoutRowsIntegerGuard.input (numeratorWord bits) i:=by
  have raw (word : List Bool) (j : Fin 212) :
      CloseoutRowsIntegerGuard.input word j=if j.val=0 then frame word else []:=by
    fin_cases j <;> rfl
  rw [raw]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change install headerSlots _ _ (headerSlots 38)=_
    rw [install_slot _ header_injective]
    exact (PairHeader.header_run bits).2.2.1
  · rw [if_neg hi]
    apply header_fresh
    rw [integer_val,if_neg hi]
    omega
theorem natural_input (bits : List Bool) (z : Fin 212→List Bool) (i : Fin 178) :
    integerDone bits z (naturalSlots i)=NatCold.input (denominatorWord bits) i:=by
  have raw (word : List Bool) (j : Fin 178) : NatCold.input word j=if j.val=0 then frame word else []:=by
    fin_cases j <;> rfl
  rw [raw]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change integerDone bits z 78=frame (denominatorWord bits)
    rw [integerDone,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h;rw [integer_val] at hv;split_ifs at hv <;> omega)]
    change install headerSlots _ _ (headerSlots 78)=_
    rw [install_slot _ header_injective]
    exact (PairHeader.header_run bits).2.2.2
  · rw [if_neg hi,integerDone,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      rw [integer_val,natural_val,if_neg hi] at hv;split_ifs at hv <;> omega)]
    apply header_fresh
    rw [natural_val,if_neg hi]
    omega

def boot : Machine 539 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=0 then some false else none,fun _=>.stay⟩ else none
noncomputable def header:=RecoveryFocus.machine headerSlots PairHeader.machine
noncomputable def integer:=RecoveryFocus.machine integerSlots CloseoutRowsIntegerGuard.machine
noncomputable def natural:=RecoveryFocus.machine naturalSlots NatCold.machine
noncomputable def first:=Composition.machine boot header
noncomputable def second:=Composition.machine first integer
noncomputable def machine:=Composition.machine second natural
def budget (bits : List Bool):=1+1+PairHeader.budget bits+1+
  CloseoutRowsIntegerGuard.budget (numeratorWord bits)+1+NatCold.budget (denominatorWord bits)

theorem boot_run (bits : List Bool) : ClockJoin.ReadyRun boot 1 (input bits) (booted bits):=by
  let final : Configuration 539 2:=⟨1,fun _=>0,booted bits⟩
  have hs:step boot (initialConfiguration boot (input bits))=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=0
      · subst i
        simp [applyAction,initialConfiguration,boot,final,booted,input,writeTapeBit]
      · simp [applyAction,initialConfiguration,boot,final,booted,hi]
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem result_integer (bits : List Bool) (z : Fin 212→List Bool) (d : Fin 178→List Bool) (i : Fin 212) :
    result bits z d (integerSlots i)=z i:=by
  rw [result,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h
    rw [natural_val,integer_val] at hv;split_ifs at hv <;> omega)]
  exact install_slot _ integer_injective _ _ _
theorem result_natural (bits : List Bool) (z : Fin 212→List Bool) (d : Fin 178→List Bool) (i : Fin 178) :
    result bits z d (naturalSlots i)=d i:=install_slot _ natural_injective _ _ _
theorem result_header (bits : List Bool) (z : Fin 212→List Bool) (d : Fin 178→List Bool) :
    result bits z d 148=PairHeader.output bits 148:=by
  rw [result,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;rw [natural_val] at hv;split_ifs at hv <;> omega)]
  rw [integerDone,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;rw [integer_val] at hv;split_ifs at hv <;> omega)]
  exact install_slot _ header_injective _ _ 148

theorem fields_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      (readTapeBit (output 148) 0=true ↔ PairHeader.valid bits) ∧
      (readTapeBit (output 360) 0=true ↔ (CanonicalBinary.decodeInt (value (numeratorWord bits))).isSome) ∧
      (readTapeBit (output 536) 0=true ↔ (CanonicalBinary.decodeNat (value (denominatorWord bits))).isSome) ∧
      output 166=frame (RecoveryFixedUnpair.leftWord (numeratorWord bits)) ∧
      output 343=frame (numerator bits) ∧ output 535=frame (denominator bits) ∧
      (readTapeBit (output 536) 0=true →
        CanonicalBinary.decodeNat (value (denominatorWord bits))=some (value (denominator bits))):=by
  have hh:=(PairHeader.header_run bits).1.focus headerSlots header_injective (booted bits) (header_input bits)
  have h0:=ClockJoin.join boot header _ _ _ _ _ (boot_run bits) hh
  obtain ⟨z,hz,zf,zs,zp,_,_⟩:=CloseoutRowsIntegerGuard.guard_run (numeratorWord bits)
  have hz':=hz.focus integerSlots integer_injective (headerDone bits) (integer_input bits)
  have h1:=ClockJoin.join first integer _ _ _ _ _ h0 hz'
  obtain ⟨d,hd,dp,_,df,dv⟩:=NatCold.nat_run (denominatorWord bits)
  have hd':=hd.focus naturalSlots natural_injective (integerDone bits z) (natural_input bits z)
  have h:=ClockJoin.join second natural _ _ _ _ _ h1 hd'
  refine ⟨result bits z d,h,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [result_header]
    exact (PairHeader.header_run bits).2.1
  · change readTapeBit (result bits z d (integerSlots 211)) 0=true ↔ _
    rw [result_integer]
    exact zf
  · change readTapeBit (result bits z d (naturalSlots 175)) 0=true ↔ _
    rw [result_natural]
    exact df
  · exact (result_integer bits z d 17).trans zs
  · exact (result_integer bits z d 194).trans zp
  · exact (result_natural bits z d 174).trans dp
  · change readTapeBit (result bits z d (naturalSlots 175)) 0=true → _
    rw [result_natural]
    exact dv

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
