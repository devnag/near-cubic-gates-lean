import Proof.Hierarchy.CompetitorCountProducerHeads
import Proof.Hierarchy.CompetitorDimensions
import Proof.Hierarchy.CompetitorRawRecordEmit

/-! Cold preparation for the six-field count record. The sole size input is
the short scalar width. The existing dimension producer writes its wide
width; the zero normalizer then writes both the fourth field and the exact
zero counter used to append all six fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordPrepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b : ℕ) : Fin 23 → List Bool :=
  fun i => if i.val=0 then List.replicate b true else []
def dimensionSlots (i : Fin 19) : Fin 23 := i.castAdd 4
def zeroSlots : Fin 5 → Fin 23 := ![15,19,20,21,22]
noncomputable def dimensions := RecoveryFocus.machine dimensionSlots CompetitorDimensions.machine
noncomputable def zero := RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def machine := Composition.machine dimensions zero
def budget (b : ℕ) := CompetitorDimensions.budget b+1+4*CompetitorRationalDecision.width b+4

theorem dimension_injective : Function.Injective dimensionSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 23 => k.val) h)

theorem prepare_run (b : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget b) (input b) out ∧
      out 0=List.replicate b true ∧
      out 20=frame (binary (CompetitorRationalDecision.width b) 0) ∧
      out 22=List.replicate (2*CompetitorRationalDecision.width b+1) false := by
  obtain ⟨d,hd,hd0,hd15,_⟩ := CompetitorDimensions.dimensions_run b
  have hdim := bounded_focus dimensionSlots dimension_injective _ _ _ hd (input b)
    (by intro i; fin_cases i <;> rfl)
  let middle := install dimensionSlots (input b) d
  have fresh (i : Fin 23) (hi : 19 ≤ i.val) : middle i=[] := by
    rw [show middle i=install dimensionSlots (input b) d i from rfl]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv := congrArg Fin.val hj
      change j.val=i.val at hv
      omega)]
    simp [input,show i.val≠0 by omega]
  obtain ⟨z,hz,_,_,hz2,_,hz4,hzh,hzs⟩ := ClockScalarFields.zero_run (CompetitorRationalDecision.width b)
  have rz : ClockJoin.ReadyRun ClockNormalize.machine (4*CompetitorRationalDecision.width b+4)
      (ClockScalarFields.zeroInput (CompetitorRationalDecision.width b)) z.final.tapes :=
    ⟨z,hz,rfl,hzh,hzs.le⟩
  have hzero := bounded_focus zeroSlots (by decide) _ _ _ rz middle (by
    intro i
    fin_cases i
    · exact (install_slot dimensionSlots dimension_injective _ d 15).trans hd15
    all_goals exact fresh _ (by decide))
  refine ⟨install zeroSlots middle z.final.tapes,?_,?_,?_,?_⟩
  · have hj := ClockJoin.join dimensions zero _ _ _ _ _ hdim hzero
    have he : CompetitorDimensions.budget b+1+(4*CompetitorRationalDecision.width b+4)=budget b := by
      unfold budget
      omega
    rw [he] at hj
    exact hj
  · exact (install_other zeroSlots _ _ 0 (by decide)).trans
      ((install_slot dimensionSlots dimension_injective _ d 0).trans hd0)
  · exact (install_slot zeroSlots (by decide) _ z.final.tapes 2).trans hz2
  · exact (install_slot zeroSlots (by decide) _ z.final.tapes 4).trans hz4

end NearCubicWires.RepairOrdinary.CompetitorCountRecordPrepare
