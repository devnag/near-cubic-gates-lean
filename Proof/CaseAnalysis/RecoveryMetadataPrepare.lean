import Proof.CaseAnalysis.RecoveryMetadataResources

/-! Allocate the thirty initially empty scalar destinations and scratch
tapes by one existing erase sweep. The five paid raw inputs remain retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
open LocalBitMultitape RecoveryRootRound RecoveryBoundedGrammarAdvance
open RecoveryBoundedGrammarScalarAdd (unary)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def retained (i : Fin 33) : Prop := i=18 ∨ i=20 ∨ i=23 ∨ i=24 ∨ i=25
instance (i : Fin 33) : Decidable (retained i) := inferInstanceAs
  (Decidable (i=18 ∨ i=20 ∨ i=23 ∨ i=24 ∨ i=25))
def freshInput (q bound C Q clauses B : ℕ) : Fin 37 → List Bool :=
  Fin.addCases (m:=33) (n:=4)
    (fun i => if retained i then words B (initialValues q bound C Q clauses) i else [])
    ![[],[],List.replicate B true,List.replicate (B+1) false]
def eraseSlots : Fin 32 → Fin 37 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,21,22,26,27,28,29,30,31,32,33,34,35,36]
def eraseData (B : ℕ) (word : List Bool) : Fin 32 → List Bool :=
  Fin.addCases (m:=30) (n:=2) (fun _ => word) ![List.replicate B true,List.replicate (B+1) false]
noncomputable def prepare := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 30)

theorem erase_local (B : ℕ) :
    ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 30) (2*B+4)
      (eraseData B []) (eraseData B (List.replicate B false)) := by
  obtain ⟨r,rr,rt,rh,rs⟩ := RecoveryScratchErase.erase_ready B (B+1)
    (fun _ : Fin 30 => []) (by intro i;exact Nat.zero_le B)
  have hi : (Fin.addCases (m:=31) (n:=1) (motive:=fun _ : Fin 32 => List Bool)
      (Fin.addCases (m:=30) (n:=1) (motive:=fun _ : Fin 31 => List Bool)
        (fun _ : Fin 30 => []) (fun _ => List.replicate B true))
      (fun _ => List.replicate (B+1) false)) = eraseData B [] := by
    funext i;fin_cases i <;> rfl
  rw [hi] at rr
  refine ⟨r,rr,?_,rh,rs.le⟩
  rw [rt,Nat.max_self]
  funext i;fin_cases i <;> rfl

theorem prepare_ready (q bound C Q clauses B : ℕ) :
    ClockJoin.ReadyRun prepare (2*B+4) (freshInput q bound C Q clauses B)
      (input q bound C Q clauses B) := by
  have h := (erase_local B).focus eraseSlots (by decide) (freshInput q bound C Q clauses B) (by
    intro j;fin_cases j <;> rfl)
  have he : install eraseSlots (freshInput q bound C Q clauses B)
      (eraseData B (List.replicate B false)) = input q bound C Q clauses B := by
    apply HierarchyWidth.install_eq eraseSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      have keep : i=18 ∨ i=20 ∨ i=23 ∨ i=24 ∨ i=25 := by
        have hfinite : ∀ k : Fin 37,(∀ j,eraseSlots j ≠ k) →
            k=18 ∨ k=20 ∨ k=23 ∨ k=24 ∨ k=25 := by decide
        exact hfinite i hi
      rcases keep with rfl|rfl|rfl|rfl|rfl <;> rfl
  rw [he] at h
  exact h

noncomputable def freshMachine := Composition.machine prepare machine
def freshBudget (B : ℕ) := 1024*(B+2)

theorem fresh_ready (q bound C Q clauses B : ℕ) (hB : 2*(q+bound+1)+8 ≤ B) :
    ClockJoin.ReadyRun freshMachine (freshBudget B) (freshInput q bound C Q clauses B)
      (output q bound C Q clauses B) := by
  have h := ClockJoin.join _ _ _ _ _ _ _ (prepare_ready q bound C Q clauses B)
    (ready q bound C Q clauses B hB)
  exact ClockJoin.enlarge _ _ (freshBudget B) _ _ h (by unfold budget freshBudget;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
