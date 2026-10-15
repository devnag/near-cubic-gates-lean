import Proof.CaseAnalysis.WitnessTermExit

/-! The actual canonical term stream enters the shared term/mass bank.
The same rational fields and circuit payload remain live for the circuit
worker; the mass store and compact output are untouched by this read. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermBegin
open LocalBitMultitape RecoveryRootRound CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RecoveryFocus.machine TermCommit.eraseSlots TermRead.machine

theorem read_run (P C : ℕ) (bits pre tail out : List Bool) (flag : Bool)
    (ambient : Fin 94 → List Bool) (hC : 0 < C)
    (hbudget : TermCoefficient.budget C bits+1 ≤ P)
    (hraw : 2*bits.length+1 ≤ P) (hb : natBitLength C ≤ P) :
    ∃ terms : Fin 725 → List Bool, ∃ result,
      runFrom machine (TermRead.budget C bits)
        ⟨machine.start,TermCommit.heads pre.length out,
          TermCommit.data P (TermRead.data P (natBitLength C) [] (pre++frame bits++tail) flag) ambient out⟩
        =some result ∧ result.steps ≤ TermRead.budget C bits ∧
      result.final.heads=TermCommit.heads (pre.length+2*bits.length+1) out ∧
      result.final.tapes=TermCommit.data P terms ambient out ∧
      (∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length ≤ P) ∧
      terms 149=ZeroPadding.pad P (List.replicate (natBitLength C) true) ∧
      (∀ i,terms (i.natAdd 720)=TermRead.extra P (pre++frame bits++tail) flag i) ∧
      terms 78=ZeroPadding.pad P (frame (TermCoefficient.circuitCode bits)) ∧
      (readTapeBit (terms 719) 0=true ↔ PairHeader.valid bits ∧
        ∃ q,decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
          natBitLength q.num.natAbs ≤ natBitLength C ∧ natBitLength q.den ≤ natBitLength C) ∧
      (readTapeBit (terms 719) 0=true → ∃ q,
        decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
        q.num.natAbs < 2^(natBitLength C) ∧ q.den < 2^(natBitLength C) ∧
        terms 690=ZeroPadding.pad P (frame (SignedSortKey.binary (natBitLength C) q.num.natAbs)) ∧
        terms 693=ZeroPadding.pad P (frame (SignedSortKey.binary (natBitLength C) q.den))) ∧
      terms 316=ZeroPadding.pad P (frame
        (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord (TermCoefficient.coefficientCode bits)))) := by
  let source := pre++frame bits++tail
  let position := pre.length+2*bits.length+1
  obtain ⟨bank,base,hr,rs,rh,rt,hbound,hwidth,hcircuit,hflag,hvalues,hsign⟩ :=
    TermRead.read_run P C bits pre tail flag hC hbudget hraw hb
  let terms := Fin.addCases (m:=720) (n:=5) (motive:=fun _=>List Bool)
    bank (TermRead.extra P source flag)
  obtain ⟨result,run,_rf,steps,heads,tapes,keep⟩ := RecoveryFocus.dock
    TermCommit.eraseSlots (by intro i j h;exact Fin.ext (congrArg (fun z : Fin 827=>z.val) h)) TermRead.machine _
    (TermCommit.heads pre.length out)
    (TermCommit.data P (TermRead.data P (natBitLength C) [] source flag) ambient out) _
    (TermCommit.heads_core pre.length out)
    (TermCommit.data_core P _ ambient out) base hr
  refine ⟨terms,result,run,steps ▸ rs,?_,?_,?_,hwidth,?_,hcircuit,hflag,?_,hsign⟩
  · funext i
    by_cases hslot : ∃ j,TermCommit.eraseSlots j=i
    · obtain ⟨j,rfl⟩ := hslot
      rw [heads,rh,TermCommit.heads_core]
    · exact ((keep i (by simpa using hslot)).1).trans (by
        revert hslot
        refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
        · intro j
          refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
          · intro k hk;exact (hk ⟨k,rfl⟩).elim
          · intro k _;simp only [TermCommit.heads,Fin.addCases_left,TermMass.heads,Fin.addCases_right]
        · intro j _;simp only [TermCommit.heads,Fin.addCases_right])
  · funext i
    by_cases hslot : ∃ j,TermCommit.eraseSlots j=i
    · obtain ⟨j,rfl⟩ := hslot
      rw [tapes,rt,TermCommit.data_core]
    · exact ((keep i (by simpa using hslot)).2).trans
        (TermCommit.data_outside P _ terms ambient out i (by simpa using hslot))
  · intro i
    have hs := TermRead.scratch_small i
    let j : Fin 720 := ⟨(TermRead.scratchSlots i).val,by omega⟩
    have he : TermRead.scratchSlots i=j.castAdd 5 := Fin.ext rfl
    rw [he]
    simpa only [terms,Fin.addCases_left] using hbound j
  · intro i;simp only [terms,Fin.addCases_right];rfl
  · intro accepted
    obtain ⟨_,q,hq,hn,hd⟩ := hflag.mp accepted
    obtain ⟨_,hnum,hden⟩ := RationalCold.decoded_words _ q hq
    obtain ⟨n,d⟩ := hvalues accepted
    rw [RationalCold.numerator_value _ q.num hnum] at n
    rw [RationalCold.denominator_value _ q.den hden] at d
    have hbit : 1 ≤ natBitLength C := by simp only [natBitLength];omega
    exact ⟨q,hq,(GcdGuard.bits_iff _ _ hbit).mp hn,(GcdGuard.bits_iff _ _ hbit).mp hd,n,d⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermBegin
