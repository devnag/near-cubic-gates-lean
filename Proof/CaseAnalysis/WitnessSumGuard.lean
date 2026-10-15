import Proof.CaseAnalysis.WitnessSumFields
import Proof.CaseAnalysis.WitnessCountBound
import Proof.CaseAnalysis.WitnessNumericEquality
import Proof.CaseAnalysis.WitnessNodeFlag

/-! The whole sum header guard compares its canonical arity with the same
produced source arity, and its actual term count with the paid exact cap.
Every raw sum has a complete run; term parsing starts only after this flag. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumGuard
open LocalBitMultitape RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 501) : Fin 510:=i.castAdd 9
def equalSlots : Fin 4→Fin 510:=![323,501,499,503]
def boundSlots : Fin 8→Fin 510:=![368,502,504,505,506,507,508,509]
def headerSlots : Fin 2→Fin 510:=![148,499]
def natSlots : Fin 2→Fin 510:=![324,499]
def countSlots : Fin 2→Fin 510:=![508,499]
def fields:=RecoveryFocus.machine old SumFields.machine
def equality:=RecoveryFocus.machine equalSlots NumericEquality.readyMachine
def bound:=RecoveryFocus.machine boundSlots CountBound.machine
def header:=RecoveryFocus.machine headerSlots NodeRound.flagMachine
def natural:=RecoveryFocus.machine natSlots NodeRound.flagMachine
def count:=RecoveryFocus.machine countSlots NodeRound.flagMachine
def first:=Composition.machine fields equality
def second:=Composition.machine first bound
def third:=Composition.machine second header
def fourth:=Composition.machine third natural
def machine:=Composition.machine fourth count
def input (bits arityBits : List Bool) (cap : ℕ) (i : Fin 510):=
  if i.val=1 then frame bits else if i.val=501 then frame arityBits
  else if i.val=502 then List.replicate cap true else []
def budget (bits arityBits : List Bool) (cap : ℕ):=SumFields.budget bits+1+
  (4*max (SumFields.payload bits).length arityBits.length+4)+1+
  CountBound.budget (SumFields.count bits) cap+1+1+1+1+1+1
def Passes (bits arityBits : List Bool) (cap : ℕ):=PairHeader.valid bits ∧
  CanonicalBinary.decodeNat (value (SumFields.arityCode bits))=some (value arityBits) ∧
  (∃ codes,CanonicalBinary.encodeBalancedList codes=value (SumFields.listCode bits)) ∧
  SumFields.count bits ≤ cap
local instance (bits arityBits : List Bool) (cap : ℕ) : Decidable (Passes bits arityBits cap):=
  Classical.propDecidable _

theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 510=>k.val) h)
theorem old_outside (i : Fin 510) (hi : 501 ≤ i.val) : ∀ j,old j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 510=>k.val) h
  change j.val=i.val at hv
  omega
theorem fold_ready (bits : List Bool) (flag : Bool) :
    ClockJoin.ReadyRun NodeRound.flagMachine 1 ![bits,[flag]]
      ![bits,[flag && readTapeBit bits 0]]:=by
  obtain ⟨r,hr,rt,rh,rs⟩:=NodeRound.flag_ready bits flag
  exact ⟨r,hr,rt,rh,rs.le⟩

theorem guard_run (bits arityBits : List Bool) (cap : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits arityBits cap) (input bits arityBits cap) output ∧
      output 501=frame arityBits ∧ output 502=List.replicate cap true ∧
      output 357=atomStream (SumFields.listCode bits).length (SumFields.atoms bits) ∧
      output 368=CompareMachine.word (SumFields.count bits) ∧
      output 504=List.replicate (SumFields.count bits) true ∧
      output 499=[decide (Passes bits arityBits cap)]:=by
  obtain ⟨f,hf,fp,fs,fc,ff,fh,fn,fd⟩:=SumFields.fields_run bits
  have hff:=hf.focus old old_injective (input bits arityBits cap) (by
    intro i
    simp only [old,Fin.val_castAdd,input,SumFields.input,
      if_neg (show i.val≠501 by omega),if_neg (show i.val≠502 by omega)])
  let bank:=install old (input bits arityBits cap) f
  have keep (i : Fin 501) : bank (old i)=f i:=install_slot _ old_injective _ _ _
  have fresh (i : Fin 510) (hi : 501 ≤ i.val) : bank i=input bits arityBits cap i:=
    install_other _ _ _ _ (old_outside i hi)
  let cflag:=CloseoutRowsCanonicalFlag.flag (SumFields.listCode bits)
  let eqflag:=cflag && decide (value (SumFields.payload bits)=value arityBits)
  obtain ⟨er,her,ert,erh,ers⟩:=NumericEquality.equality_ready
    (SumFields.payload bits) arityBits [] [] cflag 0
  have he:ClockJoin.ReadyRun NumericEquality.readyMachine
      (4*max (SumFields.payload bits).length arityBits.length+4)
      ![frame (SumFields.payload bits),frame arityBits,[cflag],[]]
      ![frame (SumFields.payload bits),frame arityBits,[eqflag],
        List.replicate (2*max (SumFields.payload bits).length arityBits.length+1) false]:=by
    simpa only [List.append_nil,List.replicate_zero,Nat.zero_max] using
      (show ClockJoin.ReadyRun NumericEquality.readyMachine _ _ _ from ⟨er,her,ert,erh,ers.le⟩)
  have hef:=he.focus equalSlots (by decide) bank (by
    intro i;fin_cases i
    · exact (keep 323).trans fp
    · exact fresh _ (by decide)
    · exact (keep 499).trans ff
    · exact fresh _ (by decide))
  let eqout : Fin 4→List Bool:=![frame (SumFields.payload bits),frame arityBits,[eqflag],
    List.replicate (2*max (SumFields.payload bits).length arityBits.length+1) false]
  let ebank:=install equalSlots bank eqout
  have ekept (i : Fin 510) (hi : ∀ j,equalSlots j≠i) : ebank i=bank i:=install_other _ _ _ _ hi
  obtain ⟨b,hb,b0,b1,b2,b6⟩:=CountBound.bound_run (SumFields.count bits) cap
  have hbf:=hb.focus boundSlots (by decide) ebank (by
    intro i;fin_cases i
    · rw [ekept _ (by decide)];exact (keep 368).trans fc
    · rw [ekept _ (by decide)];exact fresh _ (by decide)
    all_goals rw [ekept _ (by decide)];exact fresh _ (by decide))
  let bbank:=install boundSlots ebank b
  have bf:bbank 499=[eqflag]:=by
    rw [show bbank=install boundSlots _ _ by rfl,install_other _ _ _ _ (by decide)]
    exact install_slot equalSlots (by decide) _ _ 2
  have bh:bbank 148=f 148:=by
    rw [show bbank=install boundSlots _ _ by rfl,install_other _ _ _ _ (by decide),ekept _ (by decide)]
    exact keep 148
  have bn:bbank 324=f 324:=by
    rw [show bbank=install boundSlots _ _ by rfl,install_other _ _ _ _ (by decide),ekept _ (by decide)]
    exact keep 324
  have bc:bbank 508=[decide (SumFields.count bits ≤ cap)]:=
    (install_slot boundSlots (by decide) _ b 6).trans b6
  let hflag:=eqflag && readTapeBit (f 148) 0
  have hhr:=(fold_ready (f 148) eqflag).focus headerSlots (by decide) bbank (by
    intro i;fin_cases i <;> assumption)
  let hbank:=install headerSlots bbank ![f 148,[hflag]]
  have nh:hbank 324=f 324:=by
    rw [show hbank=install headerSlots _ _ by rfl,install_other _ _ _ _ (by decide)];exact bn
  have nf:hbank 499=[hflag]:=install_slot headerSlots (by decide) _ _ 1
  let nflag:=hflag && readTapeBit (f 324) 0
  have hnr:=(fold_ready (f 324) hflag).focus natSlots (by decide) hbank (by
    intro i;fin_cases i <;> assumption)
  let nbank:=install natSlots hbank ![f 324,[nflag]]
  have cc:nbank 508=[decide (SumFields.count bits ≤ cap)]:=by
    rw [show nbank=install natSlots _ _ by rfl,install_other _ _ _ _ (by decide),
      show hbank=install headerSlots _ _ by rfl,install_other _ _ _ _ (by decide)]
    exact bc
  have cf:nbank 499=[nflag]:=install_slot natSlots (by decide) _ _ 1
  have hcr:=(fold_ready [decide (SumFields.count bits ≤ cap)] nflag).focus countSlots (by decide) nbank (by
    intro i;fin_cases i <;> assumption)
  have hall:=ClockJoin.join fourth count _ _ _ _ _
    (ClockJoin.join third natural _ _ _ _ _
      (ClockJoin.join second header _ _ _ _ _
        (ClockJoin.join first bound _ _ _ _ _
          (ClockJoin.join fields equality _ _ _ _ _ hff hef) hbf) hhr) hnr) hcr
  have hn:(readTapeBit (f 324) 0=true ∧ value (SumFields.payload bits)=value arityBits) ↔
      CanonicalBinary.decodeNat (value (SumFields.arityCode bits))=some (value arityBits):=by
    constructor
    · rintro ⟨hn,heq⟩
      rw [fd hn,heq]
    · intro hd
      have hn:readTapeBit (f 324) 0=true:=fn.mpr (by rw [hd];rfl)
      exact ⟨hn,Option.some.inj ((fd hn).symm.trans hd)⟩
  have hcan:cflag=true ↔∃ codes,CanonicalBinary.encodeBalancedList codes=value (SumFields.listCode bits):=by
    dsimp only [cflag,CloseoutRowsCanonicalFlag.flag]
    rw [decide_eq_true_eq,RecoveryUnpair.bits_value]
    exact eq_comm.trans (tree_canonical_iff _)
  have hpass:(nflag && readTapeBit [decide (SumFields.count bits ≤ cap)] 0)=
      decide (Passes bits arityBits cap):=by
    apply Bool.eq_iff_iff.mpr
    change (nflag && decide (SumFields.count bits ≤ cap))=true ↔_
    simp only [nflag,hflag,eqflag,Bool.and_eq_true,decide_eq_true_eq,hcan,fh,Passes]
    constructor
    · rintro ⟨⟨⟨⟨hc,heq⟩,hh⟩,hnat⟩,hncap⟩
      exact ⟨hh,hn.mp ⟨hnat,heq⟩,hc,hncap⟩
    · rintro ⟨hh,hd,hc,hncap⟩
      obtain ⟨hnat,heq⟩:=hn.mpr hd
      exact ⟨⟨⟨⟨hc,heq⟩,hh⟩,hnat⟩,hncap⟩
  have untouched (i : Fin 510) (hi : i≠148 ∧ i≠324 ∧ i≠499 ∧ i≠508) :
      install countSlots nbank ![[decide (SumFields.count bits ≤ cap)],
        [nflag && readTapeBit [decide (SumFields.count bits ≤ cap)] 0]] i=bbank i:=by
    rw [install_other _ _ _ _ (by
        intro j;fin_cases j
        · exact Ne.symm hi.2.2.2
        · exact Ne.symm hi.2.2.1),
      show nbank=install natSlots _ _ by rfl,
      install_other _ _ _ _ (by
        intro j;fin_cases j
        · exact Ne.symm hi.2.1
        · exact Ne.symm hi.2.2.1),
      show hbank=install headerSlots _ _ by rfl,
      install_other _ _ _ _ (by
        intro j;fin_cases j
        · exact Ne.symm hi.1
        · exact Ne.symm hi.2.2.1)]
  refine ⟨_,hall,?_,?_,?_,?_,?_,?_⟩
  · rw [untouched _ ⟨by decide,by decide,by decide,by decide⟩,
      show bbank=install boundSlots _ _ by rfl,install_other _ _ _ _ (by decide)]
    exact install_slot equalSlots (by decide) _ _ 1
  · rw [untouched _ ⟨by decide,by decide,by decide,by decide⟩]
    exact (install_slot boundSlots (by decide) _ b 1).trans b1
  · rw [untouched _ ⟨by decide,by decide,by decide,by decide⟩,
      show bbank=install boundSlots _ _ by rfl,install_other _ _ _ _ (by decide),ekept _ (by decide)]
    exact (keep 357).trans fs
  · rw [untouched _ ⟨by decide,by decide,by decide,by decide⟩]
    exact (install_slot boundSlots (by decide) _ b 0).trans b0
  · rw [untouched _ ⟨by decide,by decide,by decide,by decide⟩]
    exact (install_slot boundSlots (by decide) _ b 2).trans b2
  · change install countSlots _ _ (countSlots 1)=_
    rw [install_slot _ (by decide),hpass]
    rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumGuard
