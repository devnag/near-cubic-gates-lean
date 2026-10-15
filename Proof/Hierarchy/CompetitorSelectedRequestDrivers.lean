import Proof.Hierarchy.CompetitorSelectedDimensionsBounds
import Proof.Hierarchy.CompetitorSelectedRequestFieldsBounds

/-! Original Request and its raw row modulus width produce every physical
driver used by the cold selector/SUM program. All output heads are zero. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestDrivers
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open MatrixScoreBatch CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (r : Request) (Q : ℕ) : Fin 78 → List Bool :=
  Fin.addCases (m := 64) (n := 14) (motive := fun _ => List Bool)
    (CompetitorSelectedRequestFields.input r Q) (fun _ => [])
def slots (i : Fin 17) : Fin 78 :=
  if i.val=0 then 61 else if i.val=1 then 62 else if i.val=2 then 54 else ⟨i.val+61,by omega⟩
theorem slots_injective : Function.Injective slots := by decide
def outputSlots (i : Fin 7) : Fin 78 := slots (CompetitorSelectedDimensions.outputSlots i)
noncomputable def first := ClockJoin.lifted (e := 14) (Equiv.refl (Fin 78)) CompetitorSelectedRequestFields.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorSelectedDimensions.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) (Q : ℕ) := CompetitorSelectedRequestFields.budget r+1+
  CompetitorSelectedDimensions.budget Q (extraWidth r) (r.U*r.U)

theorem drivers_run (r : Request) (Q : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget r Q) (input r Q) out ∧
      out 0=MatrixScoreBatch.physicalInput r ∧
      (∀ i,out (outputSlots i)=CompetitorSelectedDimensions.outputWords Q (extraWidth r) (r.U*r.U) i) := by
  obtain ⟨fields,hf,f0,f54,f61,f62⟩ := CompetitorSelectedRequestFields.fields_run r Q
  let ambient : Fin 78 → List Bool := Fin.addCases (m := 64) (n := 14)
    (motive := fun _ => List Bool) fields (fun _ => [])
  have hfirst : ClockJoin.ReadyRun first (CompetitorSelectedRequestFields.budget r) (input r Q) ambient :=
    ClockJoin.lift (e := 14) (Equiv.refl (Fin 78)) _ _ _ _ (fun _ : Fin 14 => []) hf
  have hlast := bounded_focus slots slots_injective _ _ _
    (CompetitorSelectedDimensions.dimensions_run Q (extraWidth r) (r.U*r.U)) ambient (by
      intro i
      fin_cases i
      · exact f61
      · exact f62
      · exact f54
      all_goals rfl)
  let out := install slots ambient (CompetitorSelectedDimensions.data7 Q (extraWidth r) (r.U*r.U))
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hfirst hlast,?_,?_⟩
  · exact (install_other slots _ _ _ (by decide)).trans f0
  · intro i
    exact (install_slot slots slots_injective _ _ (CompetitorSelectedDimensions.outputSlots i)).trans
      (CompetitorSelectedDimensions.output_read Q (extraWidth r) (r.U*r.U) i)

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestDrivers
