import Proof.Hierarchy.CompetitorSelectedWidth

/-! Re-read the retained original Request to produce U² and the short
scalar-width increment. All dimensions are physical unary outputs of the
accepted request parser and sum machines. Raw Q is retained from the row. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestFields
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (Q : ℕ) : Fin 3 → List Bool := ![List.replicate Q true,[],[]]
def input (r : Request) (Q : ℕ) : Fin 64 → List Bool :=
  Fin.addCases (m := 61) (n := 3) (motive := fun _ => List Bool)
    (CompetitorCrossRequestFields.input r) (extra Q)
def slots : Fin 4 → Fin 64 := ![52,48,62,63]
noncomputable def first := ClockJoin.lifted (e := 3) (Equiv.refl (Fin 64)) CompetitorCrossRequestFields.machine
noncomputable def last := RecoveryFocus.machine slots ClockUnarySum.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) := CompetitorCrossRequestFields.budget r+1+
  (2*CompetitorSelectedCount.extraWidth r+6)

theorem fields_run (r : Request) (Q : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget r) (input r Q) out ∧
      out 0=MatrixScoreBatch.physicalInput r ∧
      out 54=List.replicate (r.U*r.U) true ∧ out 61=List.replicate Q true ∧
      out 62=List.replicate (CompetitorSelectedCount.extraWidth r) true := by
  obtain ⟨source,hs,h0,_,_,h48,h52,h54⟩ := CompetitorCrossRequestFields.fields_run r
  let ambient : Fin 64 → List Bool := Fin.addCases (m := 61) (n := 3)
    (motive := fun _ => List Bool) source (extra Q)
  have hf : ClockJoin.ReadyRun first (CompetitorCrossRequestFields.budget r) (input r Q) ambient :=
    ClockJoin.lift (e := 3) (Equiv.refl (Fin 64)) _ _ _ _ (extra Q) hs
  have hl := bounded_focus slots (by decide) _ _ _
    (CompetitorSameBucketGroupColdDimensions.sum_ready
      (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (natBitLength r.U)) ambient (by
        intro i
        fin_cases i
        · exact h52
        · exact h48
        · rfl
        · rfl)
  let out := install slots ambient
    (CompetitorSameBucketGroupColdDimensions.sumOutput
      (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (natBitLength r.U))
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hf hl,?_,?_,?_,?_⟩
  · exact (install_other slots _ _ _ (by decide)).trans h0
  · exact (install_other slots _ _ _ (by decide)).trans h54
  · exact install_other slots _ _ _ (by decide)
  · exact install_slot slots (by decide) _ _ 2

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestFields
