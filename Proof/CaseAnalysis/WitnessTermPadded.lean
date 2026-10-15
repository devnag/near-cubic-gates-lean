import Proof.CaseAnalysis.WitnessFamilySeal
import Proof.CaseAnalysis.WitnessTermCoefficient

/-! The all-raw term/coefficient reader on the physically allocated
parser bank. Its exact fields have only trailing zero allocation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermPadded
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (P b : ℕ) (bits : List Bool) (i : Fin 720):=
  ZeroPadding.pad P (TermCoefficient.input b bits i)

theorem fields_run (P C : ℕ) (bits : List Bool) (hC : 0<C)
    (hbudget : TermCoefficient.budget C bits+1≤P)
    (hraw : 2*bits.length+1≤P) (hb : natBitLength C≤P) : ∃ output,
    ClockJoin.ReadyRun TermCoefficient.machine (TermCoefficient.budget C bits)
      (input P (natBitLength C) bits) output ∧
      output 78=ZeroPadding.pad P (frame (TermCoefficient.circuitCode bits)) ∧
      (readTapeBit (output 719) 0=true ↔ PairHeader.valid bits ∧
        ∃ q,decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
          natBitLength q.num.natAbs≤natBitLength C ∧ natBitLength q.den≤natBitLength C) ∧
      (readTapeBit (output 719) 0=true→
        output 690=ZeroPadding.pad P (frame (SignedSortKey.binary (natBitLength C)
          (value (RationalCold.numerator (TermCoefficient.coefficientCode bits))))) ∧
        output 693=ZeroPadding.pad P (frame (SignedSortKey.binary (natBitLength C)
          (value (RationalCold.denominator (TermCoefficient.coefficientCode bits)))))) ∧
      output 316=ZeroPadding.pad P
        (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord (TermCoefficient.coefficientCode bits)))) ∧
      (∀ i,(output i).length≤P):=by
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,hcir,hflag,hcoef,hsign⟩:=TermCoefficient.coefficient_run C bits hC
  have hin (i : Fin 720) : (TermCoefficient.input (natBitLength C) bits i).length≤P:=by
    unfold TermCoefficient.input
    split
    · simpa only [frame_length] using hraw
    · split
      · simpa only [List.length_replicate] using hb
      · simp
  have hsupport:=RecoveryTapeSupport.run_support TermCoefficient.machine _ _ base hr P 0
    (by intro i;exact Nat.zero_le _) (fun i=>(hin i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 720) : (base.final.tapes i).length≤P:=by
    have hmax:base.steps+1≤P:=by omega
    simpa only [Nat.zero_add,max_eq_left hmax] using hsupport i
  obtain ⟨r,hrun,rf,rt,_⟩:=ZeroPadding.run_config TermCoefficient.machine (fun _=>P) _ _ base hr
  have fields (i : Fin 720) : r.final.tapes i=ZeroPadding.pad P (out i):=by
    rw [rf]
    change ZeroPadding.pad P (base.final.tapes i)=_
    rw [ht]
  have flag:readTapeBit (r.final.tapes 719) 0=readTapeBit (out 719) 0:=by
    rw [fields,ZeroPadding.read_pad]
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,rt.trans_le hs⟩,?_,?_,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · rw [fields,hcir]
  · rw [flag];exact hflag
  · intro h
    obtain ⟨hn,hd⟩:=hcoef (by rwa [flag] at h)
    exact ⟨(fields 690).trans (congrArg (ZeroPadding.pad P) hn),
      (fields 693).trans (congrArg (ZeroPadding.pad P) hd)⟩
  · rw [fields,hsign]
  · intro i;rw [rf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le le_rfl (hbound i)

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermPadded
