import Proof.Hierarchy.CompetitorWitnessBounded
import Proof.CaseAnalysis.WitnessInput

/-! The existing bounded tagged header supplies the three cold inputs
and the actual mode bit. Payload lengths inherit its single N/16 guard. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def oracle (bits : List Bool):=RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 3)
def family (bits : List Bool):=RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 5)
def symmetric (bits : List Bool):=decide (CompetitorWitnessTriple.field bits 1=0)

theorem lengths (bits : List Bool) : (oracle bits).length=bits.length ∧ (family bits).length=bits.length:=by
  exact ⟨(RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits 3),
    (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits 5)⟩

private theorem stage_original (x bits : List Bool) (k : ℕ) : CompetitorWitnessTriple.stage x bits k 0=frame x:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [CompetitorWitnessTriple.stage]
    split_ifs with hk
    · rw [install_other]
      · exact ih
      · intro j he
        have hv:=congrArg Fin.val he
        dsimp only [CompetitorWitnessTriple.slots] at hv
        split_ifs at hv <;> dsimp at hv <;> omega
    · exact ih

private theorem header_original (x bits : List Bool) : CompetitorWitnessHeader.output x bits 0=frame x:=by
  rw [CompetitorWitnessHeader.output,install_other _ _ _ _ (by intro j;fin_cases j <;> decide)]
  rw [CompetitorWitnessHeader.before_other x bits 5 0 (by intro j z;fin_cases j <;> fin_cases z <;> decide)]
  exact stage_original x bits 6

theorem fields (x bits : List Bool) (scratch : ℕ)
    (h:readTapeBit (CompetitorWitnessBounded.output x bits scratch 147) 0=true) :
    16*(oracle bits).length≤x.length ∧ 16*(family bits).length≤x.length ∧
      CompetitorWitnessBounded.output x bits scratch 0=frame x ∧
      CompetitorWitnessBounded.output x bits scratch 78=frame (oracle bits) ∧
      CompetitorWitnessBounded.output x bits scratch 118=frame (family bits) ∧
      CompetitorWitnessBounded.output x bits scratch 142=[symmetric bits]:=by
  have cap:=((CompetitorWitnessBounded.output_valid x bits scratch).mp h).1
  have out:CompetitorWitnessBounded.output x bits scratch=
      CompetitorWitnessBounded.bank (CompetitorWitnessHeader.output x bits) true scratch:=by
    rw [CompetitorWitnessBounded.output,if_pos cap]
  refine ⟨by rw [(lengths bits).1];exact cap,by rw [(lengths bits).2];exact cap,?_,?_,?_,?_⟩
  · rw [out];exact header_original x bits
  · rw [out];exact CompetitorWitnessHeader.output_oracle x bits
  · rw [out];exact CompetitorWitnessHeader.output_sum x bits
  · rw [out];exact CompetitorWitnessHeader.output_family x bits

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
