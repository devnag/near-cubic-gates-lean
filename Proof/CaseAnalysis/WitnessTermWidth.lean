import Proof.CaseAnalysis.WitnessMassOperands
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The actual policy width is read-only throughout the all-raw term
reader. Repeated terms retain this paid field instead of copying it again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermWidth
open LocalBitMultitape RecoveryRootRound
open RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scalar_raw : NoWrite ClockNormalize.raw 0:=by
  intro q bs a ha
  fin_cases q <;> simp [ClockNormalize.raw] at ha
  · subst a;split <;> rfl
  · subst a;rfl
  · subst a;rfl
theorem scalar : NoWrite ClockNormalize.machine 0:=
  rewind ClockNormalize.raw 0 scalar_raw
theorem normal : NoWrite RationalNormalize.machine 539:=by
  apply composition
  · apply composition
    · apply composition
      · apply composition
        · exact unselected RationalNormalize.old RationalCold.machine 539 (by
            intro i h;have hv:=congrArg Fin.val h;change i.val=539 at hv;omega)
        · exact focus RationalNormalize.leftSlots (by decide) ClockNormalize.machine 0 scalar
      · exact focus RationalNormalize.rightSlots (by decide) ClockNormalize.machine 0 scalar
    · exact unselected RationalNormalize.kindSlots CompetitorWitnessKind.machine 539 (by decide)
  · intro q bs a ha
    simp only [RationalNormalize.finish] at ha
    split at ha
    · cases ha;rfl
    · contradiction
theorem rational : NoWrite RationalDecision.machine 539:=by
  apply calls
  intro j
  fin_cases j
  · exact focus RationalDecision.old RationalDecision.old_injective RationalNormalize.machine 539 normal
  · exact unselected RationalDecision.gcdSlots RationalGcd.machine 539 (by decide)
theorem term : NoWrite TermCoefficient.machine 149:=by
  apply composition
  · apply composition
    · apply composition
      · exact unselected TermCoefficient.printSlots _ 149 (by decide)
      · exact unselected TermCoefficient.headerSlots PairHeader.machine 149 (by
          intro i h;have hv:=congrArg Fin.val h;change i.val=149 at hv;omega)
    · exact focus TermCoefficient.rationalSlots TermCoefficient.rational_injective
        RationalDecision.machine 539 rational
  · exact unselected TermCoefficient.finishSlots TermCoefficient.finishMachine 149 (by decide)

theorem retained (P C : ℕ) (bits : List Bool) (output : Fin 720→List Bool)
    (h : ClockJoin.ReadyRun TermCoefficient.machine (TermCoefficient.budget C bits)
      (TermPadded.input P (natBitLength C) bits) output) :
    output 149=ZeroPadding.pad P (List.replicate (natBitLength C) true):=by
  obtain ⟨r,hr,ht,_,_⟩:=h
  have hp:=run_tape TermCoefficient.machine 149 term _ _ r hr
  rw [ht] at hp
  exact hp

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermWidth
