import Proof.CaseAnalysis.RecoveryMetadataSeed

/-! The fixed arithmetic schedule for the original row-zero scalar bank.
Only retained inputs and the paid literal one occur in this schedule. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
open LocalBitMultitape RecoveryRootRound RecoveryBoundedGrammarAdvance
open RecoveryBoundedGrammarScalarAdd (unary)
open RecoveryBoundedGrammarCold (metadata numbers)
open BoundedOracleStructuralCircuit (rowWidth)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initialValues (q bound C Q clauses : ℕ) (i : Fin 33) : ℕ :=
  if i=18 then q else if i=20 then C else if i=23 then bound else
    if i=24 then Q else if i=25 then clauses else 0
def seededValues (q bound C Q clauses : ℕ) := Function.update (initialValues q bound C Q clauses) 11 1
def additions : List (Fin 33 × Fin 33) :=
  [(12,11),(12,11),(13,12),(13,11),(14,12),(14,12),(15,14),(15,11),
   (16,13),(16,13),(1,16),(2,16),(4,16),(6,12),(7,13),(8,15),
   (9,23),(9,11),(5,18),(5,9),(2,5),(21,2),(21,5),(26,18),(26,11)]
def afterAdd (p : Fin 33 × Fin 33) (v : Fin 33 → ℕ) :=
  Function.update v p.1 (v p.1 + v p.2)
def result : List (Fin 33 × Fin 33) → (Fin 33 → ℕ) → Fin 33 → ℕ
  | [],v => v
  | p::ps,v => result ps (afterAdd p v)
def Fits (B : ℕ) : List (Fin 33 × Fin 33) → (Fin 33 → ℕ) → Prop
  | [],_ => True
  | p::ps,v => p.1 ≠ p.2 ∧ v p.1 + v p.2 + 2 ≤ B ∧ Fits B ps (afterAdd p v)
def extraValues (q bound Q clauses : ℕ) : Fin 12 → ℕ :=
  ![rowWidth q bound,0,bound,Q,clauses,q+1,0,0,0,0,0,0]
def extra (q bound Q clauses B : ℕ) : Fin 12 → List Bool :=
  fun i => unary B (extraValues q bound Q clauses i)

theorem additions_fit (q bound C Q clauses B : ℕ) (hB : 2*(q+bound+1)+8 ≤ B) :
    Fits B additions (seededValues q bound C Q clauses) := by
  dsimp [Fits,additions,afterAdd,seededValues,initialValues,Function.update]
  norm_num [Fin.ext_iff]
  omega

theorem result_eq (q bound C Q clauses : ℕ) :
    result additions (seededValues q bound C Q clauses) =
      Fin.addCases (m:=21) (n:=12) (numbers q bound 0 C) (extraValues q bound Q clauses) := by
  funext i
  fin_cases i <;>
    dsimp [result,additions,afterAdd,seededValues,initialValues,Function.update,
      numbers,extraValues,rowWidth,OuterPCPRecovery.boundedCircuitFieldLimit,Fin.addCases] <;> omega

theorem final_words (q bound C Q clauses B : ℕ) :
    words B (result additions (seededValues q bound C Q clauses)) =
      metadata q bound 0 C B (extra q bound Q clauses B) := by
  rw [result_eq]
  funext i
  refine Fin.addCases (m:=21) (n:=12) (motive:=fun i =>
    words B (Fin.addCases (m:=21) (n:=12) (numbers q bound 0 C) (extraValues q bound Q clauses)) i =
      metadata q bound 0 C B (extra q bound Q clauses B) i)
      (fun _ => by simp only [words,metadata,Fin.addCases_left];rfl)
      (fun _ => by simp only [words,metadata,Fin.addCases_right];rfl) i

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
