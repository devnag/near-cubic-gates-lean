import Proof.CaseAnalysis.RecoveryTableReferenceBank

/-! One paid step advances the three retained original row indices. The
existing raw incrementer reuses the same cleared log for all three calls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexStep
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (v : Fin 3→ℕ) (C : ℕ) : Fin 4→List Bool:=
  Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) (fun i=>List.replicate (v i) true) (fun _=>List.replicate C false)
def slots (j : Fin 3) : Fin 2→Fin 4:=![j.castAdd 1,3]
theorem slots_injective (j : Fin 3) : Function.Injective (slots j) := by fin_cases j <;> decide
noncomputable def advance (j : Fin 3):=RecoveryFocus.machine (slots j) RepairSource.RecoveryTseitinRawIncrement.machine

theorem advance_ready (v : Fin 3→ℕ) (C : ℕ) (j : Fin 3) (hC : v j+1 ≤ C) :
    ReadyRun (advance j) (2*v j+4) (data v C) (data (Function.update v j (v j+1)) C) := by
  have h:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready (v j) C hC).focus (slots j) (slots_injective j)
    (data v C) (by intro k;fin_cases j <;> fin_cases k <;> rfl)
  have he : install (slots j) (data v C) ![List.replicate (v j+1) true,List.replicate C false]=
      data (Function.update v j (v j+1)) C := by
    apply HierarchyWidth.install_eq (slots j) (slots_injective j)
    · intro k
      fin_cases j <;> fin_cases k <;> rfl
    · intro i hi
      fin_cases j <;> fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl)
  rw [he] at h
  exact h

noncomputable def pair:=Composition.machine (advance 0) (advance 1)
noncomputable def machine:=Composition.machine pair (advance 2)
def budget (a b c : ℕ):=2*a+2*b+2*c+14

theorem step_ready (a b c C : ℕ) (ha : a+1 ≤ C) (hb : b+1 ≤ C) (hc : c+1 ≤ C) :
    ReadyRun machine (budget a b c) (data ![a,b,c] C) (data ![a+1,b+1,c+1] C) := by
  have h0:=advance_ready ![a,b,c] C 0 ha
  have h1:=advance_ready ![a+1,b,c] C 1 hb
  have h2:=advance_ready ![a+1,b+1,c] C 2 hc
  have e0 : Function.update (![a,b,c] : Fin 3→ℕ) 0 (a+1)=![a+1,b,c] := by funext i;fin_cases i <;> rfl
  have e1 : Function.update (![a+1,b,c] : Fin 3→ℕ) 1 (b+1)=![a+1,b+1,c] := by funext i;fin_cases i <;> rfl
  have e2 : Function.update (![a+1,b+1,c] : Fin 3→ℕ) 2 (c+1)=![a+1,b+1,c+1] := by funext i;fin_cases i <;> rfl
  change ReadyRun (advance 0) (2*a+4) (data ![a,b,c] C) (data (Function.update ![a,b,c] 0 (a+1)) C) at h0
  change ReadyRun (advance 1) (2*b+4) (data ![a+1,b,c] C) (data (Function.update ![a+1,b,c] 1 (b+1)) C) at h1
  change ReadyRun (advance 2) (2*c+4) (data ![a+1,b+1,c] C) (data (Function.update ![a+1,b+1,c] 2 (c+1)) C) at h2
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have hp:=HierarchyMultiplyEntry.join_exact (advance 0) (advance 1) _ _ _ _ _ h0 h1
  have full:=HierarchyMultiplyEntry.join_exact pair (advance 2) _ _ _ _ _ hp h2
  have he : ((2*a+4)+1+(2*b+4))+1+(2*c+4)=budget a b c := by unfold budget;omega
  simpa only [machine,he] using full

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexStep
