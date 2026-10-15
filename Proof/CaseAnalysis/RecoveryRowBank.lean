import Proof.CaseAnalysis.RecoveryQueryListOutputRun
import Proof.CaseAnalysis.RecoveryClausesRun

/-! The original query and clause consumers share their physical ports.
The literal source, reverse stack and actual clause driver are retained
while the query machine runs; blank decoder tapes need no allocation pass. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
open RecoveryBoundedClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def querySlots (j : Fin 61) : Fin 73:=j.castAdd 12
theorem querySlots_injective : Function.Injective querySlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 73=>i.val) h)
def clauseSlots (j : Fin 71) : Fin 73:=j.castAdd 2
def extraHeads (pre stack : List Bool) (i : Fin 12):=
  if i=9 then pre.length else if i=10 then stack.length else if i=11 then 1 else 0
def extraData (source stack : List Bool) (count : ℕ) (i : Fin 12):=
  if i=9 then source else if i=10 then stack else if i=11 then CompareMachine.word count else []
def heads (out pre stack : List Bool) : Fin 73→ℕ:=
  Fin.addCases (m:=61) (n:=12) (motive:=fun _=>ℕ)
    (RecoveryBoundedQueries.bankHeads out 0 []) (extraHeads pre stack)
def data (node C D F L : ℕ) (out : List Bool) (n total : ℕ)
    (addresses refs : List Bool) (queries : ℕ) (source stack : List Bool) (count : ℕ) : Fin 73→List Bool:=
  Fin.addCases (m:=61) (n:=12) (motive:=fun _=>List Bool)
    (RecoveryBoundedQueries.bankData node C D F L out n total addresses refs queries)
    (extraData source stack count)

theorem query_heads (out pre stack : List Bool) (j : Fin 61) :
    heads out pre stack (querySlots j)=RecoveryBoundedQueries.bankHeads out 0 [] j := by
  exact Fin.addCases_left j
theorem query_data (node C D F L : ℕ) (out : List Bool) (n total : ℕ)
    (addresses refs : List Bool) (queries : ℕ) (source stack : List Bool) (count : ℕ) (j : Fin 61) :
    data node C D F L out n total addresses refs queries source stack count (querySlots j)=
      RecoveryBoundedQueries.bankData node C D F L out n total addresses refs queries j := by
  exact Fin.addCases_left j

theorem clause_state (node C D F L : ℕ) (out pre : List Bool) (n total : ℕ)
    (addresses refs : List Bool) (queries : ℕ) (source stack : List Bool) (count : ℕ) :
    State ((heads out pre stack)∘clauseSlots)
      ((data node C D F L out n total addresses refs queries source stack count)∘clauseSlots)
      node 0 0 C L out pre source refs := by
  constructor
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j <;> first | rfl | exact (ZeroPadding.pad_zero _).symm
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j <;> rfl
  · rfl
  · rfl
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j
    all_goals first
      | exact Nat.zero_le C
      | (change (List.replicate C false).length ≤ C;simp only [List.length_replicate,le_refl])
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow
