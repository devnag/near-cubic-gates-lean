import Proof.Gates.GadgetTableTransfer
import Mathlib.Data.Fin.VecNotation

/-! Literal construction of the unsigned five-entry lists with a fresh helper
    for every clause, including repeated coordinate names and literal signs. -/

set_option autoImplicit false

namespace NearCubicGates.FreshHelperTable

open GadgetTableTransfer FiniteAverages FiveCycle

structure Clause (Name : Type*) where
  name : Fin 3 → Name
  negative : Fin 3 → Bool

def Clause.eval {Name : Type*} (C : Clause Name) (assignment : Name → Bool) : Bool :=
  Gadget.originalClause (literal (C.negative 0) (assignment (C.name 0)))
    (literal (C.negative 1) (assignment (C.name 1)))
    (literal (C.negative 2) (assignment (C.name 2)))

def names {G Name : Type*} (clauses : G → Clause Name) (a : G) : Fin 5 → Name ⊕ G :=
  ![Sum.inl ((clauses a).name 0), Sum.inl ((clauses a).name 1),
    Sum.inl ((clauses a).name 2), Sum.inr a, Sum.inr a]

def honestAssignment {G Name Input : Type*} (clauses : G → Clause Name)
    (original : Name → Input → Bool) : Name ⊕ G → Input → Bool
  | Sum.inl X, x => original X x
  | Sum.inr a, x => Gadget.honestHelper
      (literal ((clauses a).negative 0) (original ((clauses a).name 0) x))
      (literal ((clauses a).negative 1) (original ((clauses a).name 1) x))
      (literal ((clauses a).negative 2) (original ((clauses a).name 2) x))

theorem fresh_helper {G Name : Type*} (clauses : G → Clause Name) (a : G) (i : Fin 3) :
    names clauses a (Fin.castAdd 2 i) ≠ names clauses a 3 := by
  fin_cases i <;> simp [names]

theorem distinct_helpers {G Name : Type*} (clauses : G → Clause Name) (a b : G) :
    names clauses a 3 = names clauses b 3 ↔ a = b := by simp [names]

theorem duplicate_helper {G Name : Type*} (clauses : G → Clause Name) (a : G) :
    names clauses a 4 = names clauses a 3 := rfl

/-- The constructed unsigned table and its selected cofactors have the exact
    stability bound. Freshness and helper correctness are derived from the
    construction, rather than supplied as premises. -/
theorem constructed_table_penalty_bound {G Name Input : Type*}
    [Fintype G] [Nonempty G] [Fintype Input] [Nonempty Input]
    (P : ℕ) (hP : 5 ≤ P) (clauses : G → Clause Name) (original : Name → Input → Bool)
    (htrue : ∀ a x, (clauses a).eval (fun X => original X x) = true)
    (candidate : G × Fin P → Input → Bool) :
    let name := names clauses
    let honest := honestAssignment clauses original
    let chosen := cofactors (by omega : 0 < P) name honest candidate
    mean (fun a => mean (penalty name (fun a => (clauses a).negative) chosen a)) ≤
      ((P : ℝ) / (P / 5 : ℕ)) *
        mean (fun a : G × Fin P => error (table name honest a) (candidate a)) := by
  apply table_penalty_bound hP (names clauses) (fun a => (clauses a).negative)
    (honestAssignment clauses original) candidate
  · simpa [names, honestAssignment, Clause.eval] using htrue
  · intro a x
    rfl
  · exact duplicate_helper clauses

def prescribed {G Name : Type*} (systematic : Name → Bool) : Name ⊕ G → Bool :=
  Sum.elim systematic (fun _ => false)

/-- Systematic coordinates are kept exact, while each auxiliary coordinate
    still uses one common minimizing cofactor. -/
theorem constructed_table_prescribed_bound {G Name Input : Type*}
    [Fintype G] [Nonempty G] [Fintype Input] [Nonempty Input]
    (P : ℕ) (hP : 5 ≤ P) (clauses : G → Clause Name) (original : Name → Input → Bool)
    (systematic : Name → Bool)
    (htrue : ∀ a x, (clauses a).eval (fun X => original X x) = true)
    (candidate : G × Fin P → Input → Bool) :
    letI : Nonempty (Fin P) := ⟨⟨0, by omega⟩⟩
    let name := names clauses
    let honest := honestAssignment clauses original
    let chosen := NameCofactors.prescribedSelected (prescribed systematic)
      (fun a : G × Fin P => name a.1 (slot a.2)) honest candidate
    mean (fun a => mean (penalty name (fun a => (clauses a).negative) chosen a)) ≤
      ((P : ℝ) / (P / 5 : ℕ)) *
        mean (fun a : G × Fin P => error (table name honest a) (candidate a)) := by
  letI : Nonempty (Fin P) := ⟨⟨0, by omega⟩⟩
  dsimp only
  apply chosen_table_penalty_bound hP (names clauses) (fun a => (clauses a).negative)
    (honestAssignment clauses original) _ candidate
  · simpa [names, honestAssignment, Clause.eval] using htrue
  · intro a x
    rfl
  · exact duplicate_helper clauses
  · intro a j
    exact NameCofactors.prescribedSelected_error_le (prescribed systematic)
      (fun a : G × Fin P => names clauses a.1 (slot a.2))
      (honestAssignment clauses original) candidate (a, j)

end NearCubicGates.FreshHelperTable
