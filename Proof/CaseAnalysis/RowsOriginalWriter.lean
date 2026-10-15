import Proof.CaseAnalysis.RowsOriginalBlock
import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock
import Proof.CaseAnalysis.RowsOriginalTemplates

/-! A fixed source-test template copies its runtime proof-coordinate
indices in order, including repeats, then writes the factor terminator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsEstimator CloseoutRowsTupleSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 4→ℕ:=![0,0,out.length,0]
def data (C : ℕ) (indices : Fin 2→ℕ) (out : List Bool) : Fin 4→List Bool:=
  ![ZeroPadding.pad C (List.replicate (indices 0) true),
    ZeroPadding.pad C (List.replicate (indices 1) true),out,List.replicate C false]
def slots (side : Fin 2) : Fin 3→Fin 4:=![side.castAdd 2,2,3]
noncomputable def one (side : Fin 2):=RecoveryFocus.machine (slots side) CloseoutRowsOriginalBlock.machine
def finishSlots : Fin 2→Fin 4:=![0,2]
noncomputable def finish:=RecoveryFocus.machine finishSlots (CloseoutRowsOriginalBlock.mark false)
noncomputable def program : List (Fin 2)→Σ s,Machine 4 s
  | []=>⟨_,finish⟩
  | side::rest=>⟨_,Composition.machine (one side) (program rest).2⟩
noncomputable def machine (factors : List (Fin 2)):= (program factors).2
def indicesWord (indices : Fin 2→ℕ) (factors : List (Fin 2)):=
  (factors.map indices).flatMap ExtIncidence.block++[false]
def budget (indices : Fin 2→ℕ) (factors : List (Fin 2)):=
  (factors.map (fun side=>2*indices side+9)).sum+1

theorem one_run (C : ℕ) (indices : Fin 2→ℕ) (out : List Bool) (side : Fin 2)
    (hc : indices side+3≤C) :
    Step (one side) (2*indices side+8) (heads out) (data C indices out)
      (heads (out++ExtIncidence.block (indices side)))
      (data C indices (out++ExtIncidence.block (indices side))) := by
  refine SubstitutionDock.run _ _ (by fin_cases side <;> decide) _ _ _ _ _ _ _ _
    (CloseoutRowsOriginalBlock.run C (indices side) out hc) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases side <;>fin_cases j <;>rfl)
  | (intro j hj;fin_cases side <;>fin_cases j <;> first | rfl | exact False.elim (hj 1 rfl))

theorem finish_run (C : ℕ) (indices : Fin 2→ℕ) (out : List Bool) :
    Step finish 1 (heads out) (data C indices out)
      (heads (out++[false])) (data C indices (out++[false])) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _
    (CloseoutRowsOriginalBlock.mark_run false (ZeroPadding.pad C (List.replicate (indices 0) true)) out)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 1 rfl))

theorem run (C : ℕ) (indices : Fin 2→ℕ) (factors : List (Fin 2))
    (out : List Bool) (hc : ∀ side,indices side+3≤C) :
    Step (machine factors) (budget indices factors) (heads out) (data C indices out)
      (heads (out++indicesWord indices factors)) (data C indices (out++indicesWord indices factors)) := by
  induction factors generalizing out with
  | nil=>exact finish_run C indices out
  | cons side rest ih=>
    have whole:=(one_run C indices out side (hc side)).seq (ih (out++ExtIncidence.block (indices side)))
    have time : (2*indices side+8)+1+budget indices rest=budget indices (side::rest) := by
      simp only [budget,List.map_cons,List.sum_cons];omega
    rw [time] at whole
    simpa only [machine,program,indicesWord,List.map_cons,List.flatMap_cons,List.append_assoc] using whole

theorem budget_bound (indices : Fin 2→ℕ) (factors : List (Fin 2)) (B : ℕ)
    (hb : ∀ side,indices side≤B) (hl : factors.length≤4) : budget indices factors≤8*B+37 := by
  have aux : ∀ fs : List (Fin 2),(fs.map (fun side=>2*indices side+9)).sum≤fs.length*(2*B+9) := by
    intro fs;induction fs with
    | nil=>simp
    | cons side rest ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul];have h:=hb side;omega
  have h:=aux factors
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
