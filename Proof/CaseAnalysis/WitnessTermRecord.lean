import Proof.CaseAnalysis.WitnessCoefficientRecord

/-! The retained coefficient stream shares the term loader's restored
scratch tape. Its only new tape is the output, at its logical cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRecord
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5→Fin 827:=![316,690,693,826,723]
noncomputable def machine:=RecoveryFocus.machine slots CoefficientRecord.machine

theorem record_run (P : ℕ) (source nb db out : List Bool)
    (heads : Fin 827→ℕ) (tapes : Fin 827→List Bool)
    (hh : ∀ i,heads (slots i)=CoefficientRecord.heads out i)
    (ht : ∀ i,tapes (slots i)=CoefficientRecord.tapes P source nb db out i)
    (hn : 2*nb.length+1≤P) (hd : 2*db.length+1≤P) : ∃ result,
    runFrom machine (CoefficientRecord.budget nb db) ⟨machine.start,heads,tapes⟩=some result ∧
      result.steps=CoefficientRecord.budget nb db ∧
      result.final.heads=Function.update heads 826 (out++CoefficientRecord.produced source nb db).length ∧
      result.final.tapes=Function.update tapes 826 (out++CoefficientRecord.produced source nb db):=by
  classical
  obtain ⟨base,hb,bs,bh,bt⟩:=CoefficientRecord.record_run P source nb db out hn hd
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots (by decide)
    CoefficientRecord.machine _ heads tapes _ hh ht base hb
  refine ⟨r,hr,rs.trans bs,?_,?_⟩
  · funext i
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh,bh]
      fin_cases j
      · exact (hh 0).symm
      · exact (hh 1).symm
      · exact (hh 2).symm
      · simp [slots,CoefficientRecord.heads]
      · exact (hh 4).symm
    · have hi:i≠826:=by intro h;exact hs ⟨3,h.symm⟩
      rw [Function.update_of_ne hi]
      exact (keep i (by simpa using hs)).1
  · funext i
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rt,bt]
      fin_cases j
      · exact (ht 0).symm
      · exact (ht 1).symm
      · exact (ht 2).symm
      · simp [slots,CoefficientRecord.tapes]
      · exact (ht 4).symm
    · have hi:i≠826:=by intro h;exact hs ⟨3,h.symm⟩
      rw [Function.update_of_ne hi]
      exact (keep i (by simpa using hs)).2

def word (b : ℕ) (q : ℚ):=frame [decide (q.num<0)]++
  frame (SignedSortKey.binary b q.num.natAbs)++frame (SignedSortKey.binary b q.den)
theorem word_length (b : ℕ) (q : ℚ) : (word b q).length=4*b+5:=by
  simp only [word,List.length_append,frame_length,List.length_singleton,SignedSortKey.binary_length]
  omega
theorem same_word (P b : ℕ) (bits : List Bool) (q : ℚ)
    (hd : CanonicalWitnessCodec.decodeCanonicalRational (RadixSemantics.value bits)=some q) :
    CoefficientRecord.produced
      (ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits))))
      (SignedSortKey.binary b q.num.natAbs) (SignedSortKey.binary b q.den)=word b q:=by
  unfold CoefficientRecord.produced
  rw [CoefficientRecord.sign_meaning P bits q hd]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRecord
