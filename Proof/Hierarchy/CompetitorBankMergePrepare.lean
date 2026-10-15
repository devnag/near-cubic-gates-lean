import Proof.Hierarchy.CompetitorBankMergeFields

/-! Reuse the accepted physical W/capacity preparation while retaining the
second raw bank on an unselected tape. No loaded operand or scratch is given
for free; all capacities and width copies are actual executed outputs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prepareSlots (i : Fin 46) : Fin 47 := if i=23 then 46 else i.castAdd 1
def bodySlots (i : Fin 27) : Fin 47 := i.castAdd 20
def input (w n : ℕ) (left right : List Bool) : Fin 47 → List Bool := fun i =>
  if i=9 then List.replicate w true else if i=19 then left else if i=23 then right
  else if i=27 then CompareMachine.word n else []
noncomputable def prepareProgram := RecoveryFocus.machine prepareSlots CompetitorResidueTable.coldPrepareProgram

theorem prepare_run (w n : ℕ) (left right : List Bool) :
    ∃ out,ClockJoin.ReadyRun prepareProgram (CompetitorResidueTable.coldPrepareBudget w) (input w n left right) out ∧
      Store w left right [] (out ∘ bodySlots) ∧ out 27=CompareMachine.word n := by
  obtain ⟨prepared,hready,hstore,hcount⟩ := CompetitorResidueTable.cold_prepare_run w 0 n left
  have hin : ∀ i,input w n left right (prepareSlots i)=CompetitorResidueTable.input w 0 n left i := by
    intro i
    fin_cases i <;> simp [input,prepareSlots,CompetitorResidueTable.input]
  let out := install prepareSlots (input w n left right) prepared
  have hall := CompetitorRationalProducts.bounded_focus prepareSlots (by decide) _ _ _ hready (input w n left right) hin
  have outputAt (i : Fin 46) (hi : i≠23) : out (i.castAdd 1)=prepared i := by
    have he := install_slot prepareSlots (by decide) (input w n left right) prepared i
    simpa only [prepareSlots,if_neg hi] using he
  have rightAt : out 23=right :=
    install_other prepareSlots (input w n left right) prepared 23 (by decide)
  refine ⟨out,hall,?_,(outputAt 27 (by decide)).trans hcount⟩
  constructor
  · exact (outputAt 9 (by decide)).trans hstore.width
  · exact (outputAt 20 (by decide)).trans hstore.widthCopy
  · exact (outputAt 19 (by decide)).trans hstore.source
  · exact rightAt
  · exact (outputAt 8 (by decide)).trans hstore.output
  · exact (outputAt 21 (by decide)).trans hstore.erase
  · exact (outputAt 22 (by decide)).trans hstore.reset
  · intro i
    change (out ((workSlots i).castAdd 20)).length≤capacity w
    have he : out ((workSlots i).castAdd 20)=prepared ((workSlots i).castAdd 19) :=
      outputAt ((workSlots i).castAdd 19) (by fin_cases i <;> decide)
    rw [he]
    exact hstore.support i

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
