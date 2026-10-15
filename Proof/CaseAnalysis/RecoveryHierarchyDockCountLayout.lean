import Proof.CaseAnalysis.RecoveryHierarchyDock
import Proof.CaseAnalysis.RecoveryClauseCount

/-! One fresh scratch tape for the paid original clause-counter extraction.
The count is written directly to retained scalar157. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock.Count
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tapes (k : ℕ):=RecoveryBoundedColdHierarchyDock.tapes source k+1
def prior (k : ℕ) (i : Fin (RecoveryBoundedColdHierarchyDock.tapes source k)) : Fin (tapes source k):=i.castAdd 1
def old (k : ℕ) (i : Fin 158):=prior source k (RecoveryBoundedColdHierarchyDock.old source k i)
def scratch (k : ℕ) : Fin (tapes source k):=(0 : Fin 1).natAdd (RecoveryBoundedColdHierarchyDock.tapes source k)
def counter (k : ℕ):=prior source k (clauseCountPort source k)
def slots (k : ℕ) : Fin 3→Fin (tapes source k):=![counter source k,old source k 157,scratch source k]

theorem prior_injective (k : ℕ) : Function.Injective (prior source k):=
  Fin.castAdd_injective _ _
theorem counter_ne_output (k : ℕ) : counter source k≠old source k 157:=by
  intro he
  exact slots_other source k 157 (by decide) (by decide)
    (HierarchyStreams.slots source k 46) (prior_injective source k he)
theorem prior_ne_scratch (k : ℕ) (i : Fin (RecoveryBoundedColdHierarchyDock.tapes source k)) :
    prior source k i≠scratch source k:=by
  intro he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  dsimp only [prior,scratch] at hv
  simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Nat.add_zero] at hv
  omega
theorem slots_injective (k : ℕ) : Function.Injective (slots source k):=by
  intro i j he
  fin_cases i <;>fin_cases j
  all_goals first
    | rfl
    | exact False.elim (counter_ne_output source k he)
    | exact False.elim (counter_ne_output source k he.symm)
    | exact False.elim (prior_ne_scratch source k _ he)
    | exact False.elim (prior_ne_scratch source k _ he.symm)

theorem slots_away (k : ℕ) (i : Fin (RecoveryBoundedColdHierarchyDock.tapes source k))
    (ho : i≠RecoveryBoundedColdHierarchyDock.old source k 157) (hc : i≠clauseCountPort source k) :
    ∀ j,slots source k j≠prior source k i:=by
  intro j he
  fin_cases j
  · exact hc (prior_injective source k he.symm)
  · exact ho (prior_injective source k he.symm)
  · exact prior_ne_scratch source k i he.symm

def first (k CH Cpad : ℕ) (code : List Bool):=
  TapeEmbedding.machine 1 (RecoveryBoundedColdHierarchyDock.machine source k CH Cpad code)
def last (k : ℕ):=RecoveryFocus.machine (slots source k) RecoveryBoundedColdClauseCount.machine
def machine (k CH Cpad : ℕ) (code : List Bool):=Composition.machine (first source k CH Cpad code) (last source k)
def input (k : ℕ) (A : Fin 158→List Bool) (word : List Bool) : Fin (tapes source k)→List Bool:=
  Fin.addCases (RecoveryBoundedColdHierarchyDock.input source k A word) (fun _=>[])
def heads (k : ℕ) (H : Fin 158→ℕ) : Fin (tapes source k)→ℕ:=
  Fin.addCases (RecoveryBoundedColdHierarchyDock.heads source k H) (fun _=>0)
def clauses (k CH Cpad : ℕ) (code x : List Bool):=
  (Codec.clauses (source.output (HierarchyStreams.request k CH Cpad code x))).length
def budget (k CH Cpad : ℕ) (code x : List Bool):=
  HierarchyStreams.budget source k CH Cpad code x+1+
    RecoveryBoundedColdClauseCount.budget (clauses source k CH Cpad code x)

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock.Count
