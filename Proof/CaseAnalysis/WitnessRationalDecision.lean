import Proof.CaseAnalysis.WitnessRationalSign
import Proof.CaseAnalysis.WitnessRationalGcd
import Proof.Amplification.RecoveryCursorCalls

/-! One total rational decision. Canonicality, positivity and original
payload lengths are tested before the cold gcd branch. Every raw word halts
under the same exact source cap; accepted coefficient fields stay retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalDecision
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 552) : Fin 568:=i.castAdd 16
def gcdSlots (i : Fin 18) : Fin 568:=
  if i.val=0 then 540 else if i.val=1 then 543 else ⟨550+i.val,by omega⟩
theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 568=>k.val) h)
theorem gcd_injective : Function.Injective gcdSlots:=by decide
def input (b : ℕ) (bits : List Bool) (i : Fin 568):=
  if i.val=539 then List.replicate b true else if i.val=1 then frame bits else []
noncomputable def normal:=RecoveryFocus.machine old RationalNormalize.machine
noncomputable def gcd:=RecoveryFocus.machine gcdSlots RationalGcd.machine
def stateCount {t s : ℕ} (_ : Machine t s):=s
noncomputable def sizes : Fin 2→ℕ:=![stateCount normal,stateCount gcd]
noncomputable def programs : (j : Fin 2)→Machine 568 (sizes j)
  | ⟨0,_⟩=>normal
  | ⟨1,_⟩=>gcd
  | ⟨j+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scan : Fin 568→Bool) : Option (Fin 2):=
  if j.val=0 ∧ scan 551=true then some 1 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
def tailBudget (b C : ℕ):=44*b+62+(4*C+1)*(32*b+40)
def budget (C : ℕ) (bits : List Bool):=
  RationalNormalize.budget (natBitLength C) bits+1+tailBudget (natBitLength C) C+1
noncomputable def middle (b : ℕ) (bits : List Bool) (out : Fin 552→List Bool):=
  install old (input b bits) out

theorem middle_old (b : ℕ) (bits : List Bool) (out : Fin 552→List Bool) (i : Fin 552) :
    middle b bits out (old i)=out i:=install_slot _ old_injective _ _ _
theorem middle_fresh (b : ℕ) (bits : List Bool) (out : Fin 552→List Bool)
    (i : Fin 568) (hi : 552 ≤ i.val) : middle b bits out i=[]:=by
  rw [middle,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;change j.val=i.val at hv;omega)]
  simp only [input,if_neg (show i.val≠539 by omega),if_neg (show i.val≠1 by omega)]

theorem passes_iff (b : ℕ) (bits : List Bool) (hb : 1 ≤ b) :
    (RationalNormalize.passes b bits ∧
      (value (RationalCold.numerator bits)).gcd (value (RationalCold.denominator bits))=1) ↔
    ∃ q,decodeCanonicalRational (value bits)=some q ∧
      natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b:=by
  rw [←RationalCold.length_guarded_iff bits b hb]
  unfold RationalNormalize.passes RationalCold.valid
  tauto

theorem tail_bound (b C a d : ℕ) (ha : a<2*C) (hd : d<2*C) :
    RationalGcd.budget b a d ≤ tailBudget b C:=by
  have hm:=Nat.mul_le_mul_right (32*b+40) (show a+d+1 ≤ 4*C+1 by omega)
  unfold RationalGcd.budget tailBudget
  omega

theorem decision_run (C : ℕ) (bits : List Bool) (hC : 0<C) : ∃ output,
    ClockJoin.ReadyRun machine (budget C bits) (input (natBitLength C) bits) output ∧
      (readTapeBit (output 564) 0=true ↔ ∃ q,decodeCanonicalRational (value bits)=some q ∧
        natBitLength q.num.natAbs ≤ natBitLength C ∧ natBitLength q.den ≤ natBitLength C) ∧
      (readTapeBit (output 564) 0=true →
        output 540=frame (SignedSortKey.binary (natBitLength C) (value (RationalCold.numerator bits))) ∧
        output 543=frame (SignedSortKey.binary (natBitLength C) (value (RationalCold.denominator bits)))) ∧
      output 166=frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits)):=by
  let b:=natBitLength C
  have hb:1 ≤ b:=by dsimp only [b,natBitLength];omega
  obtain ⟨out,hn,hflag,hbraw,haWord,hdWord⟩:=RationalNormalize.normalize_run b bits
  have hsign:=RationalNormalize.retained_sign b bits out hn
  obtain ⟨nr,hnr,nrt,nrh,_⟩:=hn.focus old old_injective (input b bits) (by intro i;rfl)
  have flag:readTapeBit (nr.final.tapes 551) (nr.final.heads 551)=decide (RationalNormalize.passes b bits):=by
    rw [nrh,nrt]
    change readTapeBit (middle b bits out (old 551)) 0=_
    rw [middle_old,hflag]
    rfl
  by_cases hp:RationalNormalize.passes b bits
  · have hl:=(hp.2.2.2.2.1)
    have hd:=(hp.2.2.2.2.2)
    have ha:value (RationalCold.numerator bits)<2^b:=
      (value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) hl)
    have hden:value (RationalCold.denominator bits)<2^b:=
      (value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) hd)
    have hac:value (RationalCold.numerator bits)<2*C:=RationalGuard.bit_cap_numeric C _ hC
      ((GcdGuard.bits_iff b _ hb).mpr ha)
    have hdc:value (RationalCold.denominator bits)<2*C:=RationalGuard.bit_cap_numeric C _ hC
      ((GcdGuard.bits_iff b _ hb).mpr hden)
    have gin:∀ i,middle b bits out (gcdSlots i)=RationalGcd.input b
        (value (RationalCold.numerator bits)) (value (RationalCold.denominator bits)) i:=by
      intro i;fin_cases i
      · change middle b bits out (old 540)=_
        rw [middle_old,haWord,ClockScalarFields.resize_binary b _ hl]
        rfl
      · change middle b bits out (old 543)=_
        rw [middle_old,hdWord,ClockScalarFields.resize_binary b _ hd]
        rfl
      all_goals exact middle_fresh b bits out _ (by decide)
    obtain ⟨gout,hg,ga,gd,gflag⟩:=RationalGcd.gcd_run b
      (value (RationalCold.numerator bits)) (value (RationalCold.denominator bits)) ha hden
    have hg':=ClockJoin.enlarge RationalGcd.machine _ (tailBudget b C) _ _ hg (tail_bound _ _ _ _ hac hdc)
    obtain ⟨gr,hgr,grt,grh,_⟩:=hg'.focus gcdSlots gcd_injective (middle b bits out) gin
    obtain ⟨nt,hnt,hncall⟩:=call_receipt sizes programs 0 next 0 1
      (RationalNormalize.budget b bits) _ nr hnr (by
        change (if (0 : ℕ)=0 ∧ readTapeBit (nr.final.tapes 551) (nr.final.heads 551)=true then some (1 : Fin 2) else none)=_
        rw [flag,decide_eq_true hp]
        rfl)
    have he:RecoveryCalls.restarted (programs 1) nr.final.heads nr.final.tapes=
        initialConfiguration (programs 1) (middle b bits out):=by
      apply configuration_ext
      · rfl
      · exact funext nrh
      · simpa only [RecoveryCalls.restarted,initialConfiguration,middle] using nrt
    rw [he] at hncall
    obtain ⟨gt,hgt,hgstop⟩:=stop_receipt sizes programs 0 next 1 (tailBudget b C) _ gr hgr (by rfl)
    have hall:=hncall.trans hgstop
    obtain ⟨r,hr,rf,rs⟩:=hall.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht:nt+gt ≤ budget C bits:=by
      change nt+gt ≤ RationalNormalize.budget b bits+1+tailBudget b C+1
      omega
    have more:=run_moreFuel machine (nt+gt) (budget C bits-(nt+gt)) (input b bits) r hr
    rw [Nat.add_sub_of_le ht] at more
    let output:=install gcdSlots (middle b bits out) gout
    have hout:r.final.tapes=output:=by
      rw [rf]
      simpa only [RecoveryCalls.stopped,output] using grt
    have oh:∀ i,r.final.heads i=0:=by intro i;rw [rf];exact grh i
    have hf:output 564=[decide ((value (RationalCold.numerator bits)).gcd (value (RationalCold.denominator bits))=1)]:=by
      change install gcdSlots _ _ (gcdSlots 14)=_
      rw [install_slot _ gcd_injective]
      exact gflag
    refine ⟨output,⟨r,more,hout,oh,rs.le.trans ht⟩,?_,?_,?_⟩
    · rw [hf,←passes_iff b bits hb]
      simp only [readTapeBit,List.getD,List.getElem?_cons_zero,Option.getD_some,decide_eq_true_eq,hp,true_and]
    · intro _
      exact ⟨(install_slot gcdSlots gcd_injective _ gout 0).trans ga,
        (install_slot gcdSlots gcd_injective _ gout 1).trans gd⟩
    · rw [show output=install gcdSlots (middle b bits out) gout by rfl,
        install_other _ _ _ _ (by intro i;fin_cases i <;> decide)]
      exact (middle_old b bits out 166).trans hsign
  · obtain ⟨nt,hnt,hstop⟩:=stop_receipt sizes programs 0 next 0
      (RationalNormalize.budget b bits) _ nr hnr (by
        change (if (0 : ℕ)=0 ∧ readTapeBit (nr.final.tapes 551) (nr.final.heads 551)=true then some (1 : Fin 2) else none)=_
        rw [flag,decide_eq_false hp]
        rfl)
    obtain ⟨r,hr,rf,rs⟩:=hstop.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht:nt ≤ budget C bits:=by
      change nt ≤ RationalNormalize.budget b bits+1+tailBudget b C+1
      omega
    have more:=run_moreFuel machine nt (budget C bits-nt) (input b bits) r hr
    rw [Nat.add_sub_of_le ht] at more
    have hfalse:middle b bits out 564=[]:=middle_fresh b bits out _ (by decide)
    refine ⟨middle b bits out,⟨r,more,by
      rw [rf]
      simpa only [RecoveryCalls.stopped,middle] using nrt,
      by intro i;rw [rf];exact nrh i,rs.le.trans ht⟩,?_,?_,?_⟩
    · rw [hfalse,←passes_iff b bits hb]
      simp only [readTapeBit,List.getD,List.getElem?_nil,Option.getD_none,Bool.false_eq_true,hp,false_and]
    · rw [hfalse]
      intro h
      cases h
    · exact (middle_old b bits out 166).trans hsign

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalDecision
