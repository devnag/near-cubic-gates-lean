import Proof.CaseAnalysis.RecoveryMetadataPlan

/-! Actual execution of the fixed cold additions. Every call is the
checked in-place unary worker, including its paid erase and rewind operations. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
open LocalBitMultitape RecoveryRootRound RecoveryBoundedGrammarAdvance
open RecoveryBoundedGrammarScalarAdd (unary)
open RecoveryBoundedGrammarCold (metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stop : Machine 37 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
private def stateCount {s : ℕ} (_ : Machine 37 s) := s
noncomputable def states : List (Fin 33 × Fin 33) → ℕ
  | [] => 1
  | p::ps => stateCount (add p.1 p.2) + states ps
noncomputable def additionsMachine : (ps : List (Fin 33 × Fin 33)) → Machine 37 (states ps)
  | [] => stop
  | p::ps => Composition.machine (add p.1 p.2) (additionsMachine ps)

theorem words_update (B : ℕ) (v : Fin 33 → ℕ) (p : Fin 33 × Fin 33) :
    Function.update (words B v) p.1 (unary B (v p.1+v p.2)) = words B (afterAdd p v) := by
  funext i
  by_cases hi : i = p.1
  · subst i
    simp only [words,afterAdd,Function.update_self]
  · simp only [words,afterAdd,Function.update_of_ne hi]

theorem additions_run (ps : List (Fin 33 × Fin 33)) (B : ℕ) (v : Fin 33 → ℕ)
    (h : Fits B ps v) :
    ClockJoin.ReadyRun (additionsMachine ps) (ps.length*(8*B+22))
      (bank B (words B v)) (bank B (words B (result ps v))) := by
  induction ps generalizing v with
  | nil =>
    simp only [List.length_nil,Nat.zero_mul]
    let r : ExecutionReceipt 37 1 :=
      ⟨initialConfiguration stop (bank B (words B v)),0,
        (initialConfiguration stop (bank B (words B v))).tapeCells⟩
    exact ⟨r,rfl,rfl,fun _ => rfl,Nat.zero_le _⟩
  | cons p ps ih =>
    rcases h with ⟨hne,hfit,hrest⟩
    have first := add_ready p.1 p.2 hne (v p.1) (v p.2) B (words B v) rfl rfl hfit
    rw [words_update] at first
    have firstBounded := ClockJoin.enlarge _ _ (8*B+21) _ _ first (by
      unfold RecoveryBoundedGrammarScalarAdd.budget
      omega)
    have last := ih (afterAdd p v) hrest
    have joined := ClockJoin.join _ _ _ _ _ _ _ firstBounded last
    have hc : (8*B+21)+1+ps.length*(8*B+22) = (p::ps).length*(8*B+22) := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    rw [hc] at joined
    exact joined

noncomputable def machine := Composition.machine seed (additionsMachine additions)
def budget (B : ℕ) := 512*(B+2)
def input (q bound C Q clauses B : ℕ) := bank B (words B (initialValues q bound C Q clauses))
def output (q bound C Q clauses B : ℕ) := bank B (metadata q bound 0 C B (extra q bound Q clauses B))

theorem ready (q bound C Q clauses B : ℕ) (hB : 2*(q+bound+1)+8 ≤ B) :
    ClockJoin.ReadyRun machine (budget B) (input q bound C Q clauses B) (output q bound C Q clauses B) := by
  have first := seed_ready B (initialValues q bound C Q clauses) rfl (by omega)
  have last := additions_run additions B (seededValues q bound C Q clauses)
    (additions_fit q bound C Q clauses B hB)
  rw [final_words] at last
  have joined := ClockJoin.join _ _ _ _ _ _ _ first last
  exact ClockJoin.enlarge _ _ (budget B) _ _ joined (by
    change 4+1+25*(8*B+22) ≤ 512*(B+2)
    omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
