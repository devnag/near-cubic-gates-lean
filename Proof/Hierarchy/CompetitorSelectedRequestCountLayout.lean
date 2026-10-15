import Proof.Hierarchy.CompetitorSelectedRequestDrivers
import Proof.Hierarchy.CompetitorSelected

/-! Physical input layout for the original-Request selected-total program.
The actual request-derived driver endpoint supplies every cold driver slot. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (Q : ℕ) (xs : List (Bool × ℕ)) : Fin 13 → List Bool :=
  ![mask xs,CompetitorCountFold.raw Q (counts xs),[],[],[],[],[],[],[],[],[],[],[]]
def input (r : Request) (Q : ℕ) (xs : List (Bool × ℕ)) : Fin 91 → List Bool :=
  Fin.addCases (m := 78) (n := 13) (motive := fun _ => List Bool)
    (CompetitorSelectedRequestDrivers.input r Q) (extra Q xs)
def slots : Fin 20 → Fin 91 := ![64,78,80,66,72,81,70,74,79,82,83,61,76,84,85,86,87,88,89,90]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := ClockJoin.lifted (e := 13) (Equiv.refl (Fin 91)) CompetitorSelectedRequestDrivers.machine
noncomputable def last := RecoveryFocus.machine slots coldMachine
noncomputable def machine := Composition.machine first last
def budget (r : Request) (Q : ℕ) := CompetitorSelectedRequestDrivers.budget r Q+1+
  coldBudget Q (scalarWidth r Q) (r.U*r.U)
noncomputable def outputHeads (Q N : ℕ) (i : Fin 91) : ℕ :=
  match RecoveryFocus.pick slots i with | some j => finalHeads Q N j | none => 0

def prepared (Q : ℕ) (xs : List (Bool × ℕ)) (out : Fin 78 → List Bool) : Fin 91 → List Bool :=
  Fin.addCases (m := 78) (n := 13) (motive := fun _ => List Bool) out (extra Q xs)

theorem projected_input (r : Request) (Q : ℕ) (xs : List (Bool × ℕ))
    (hn : xs.length≤r.U*r.U) (out : Fin 78 → List Bool)
    (ht : ∀ i,out (CompetitorSelectedRequestDrivers.outputSlots i)=
    CompetitorSelectedDimensions.outputWords Q (extraWidth r) (r.U*r.U) i)
    (i : Fin 20) : prepared Q xs out (slots i)=shortTapes Q (scalarWidth r Q) (r.U*r.U) xs i := by
  fin_cases i
  · exact ht 1
  · rfl
  · rfl
  · change out (CompetitorSelectedRequestDrivers.outputSlots 2)=UnaryTemplate.tape (mask (padded (r.U*r.U) xs)).length
    rw [mask_length,padded_length _ _ hn]
    exact ht 2
  · exact ht 4
  · rfl
  · change out (CompetitorSelectedRequestDrivers.outputSlots 3)=UnaryTemplate.tape (Q*(padded (r.U*r.U) xs).length)
    rw [padded_length _ _ hn]
    exact ht 3
  · exact ht 5
  · rfl
  · rfl
  · rfl
  · exact ht 0
  · exact ht 6
  all_goals rfl

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
