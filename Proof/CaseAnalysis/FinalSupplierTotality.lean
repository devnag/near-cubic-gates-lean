import Proof.CaseAnalysis.WitnessWeakMachine

/-! Paper C.10: the ordinary worker is a *deterministic* machine that always
halts inside its polynomial fuel. Nothing in the paper asks the worker to be
partial, and nothing asks its decided predicate to be supplied from outside.

`ClosureAt.meaning` is a field of the closure, so the consumer is free to pin
it. Pinning it to exactly what the worker decides turns `AllInputRun` -- which
asks for a run *and* an exact characterisation -- into pure totality, because
`run` is a function: the run it produces is the only run there is.

This is a relocation of content, never an assumption. The physical obligations
do not disappear; they move to `sound` and to the two `Completeness` fields,
which are the places paper C.10 and C.12 put them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Weak
open LocalBitMultitape SourceInterfaces RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The worker halts inside its fuel on every length, every input and every
witness string. This is the whole supplier obligation once `meaning` is
pinned. -/
def Total {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (fuel : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), ∃ actual,
    run p (fuel n)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) = some actual

/-- The canonical meaning: the predicate the worker actually decides. -/
def decides {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (fuel : ℕ → ℕ) : (n : ℕ) → BitInput n → List Bool → Prop :=
  fun n x bits => ∃ actual,
    run p (fuel n)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) = some actual ∧
      actual.final.scanned result = true

/-- Totality is exactly the supplier, at the canonical meaning. -/
theorem allInputRun_of_total {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (fuel : ℕ → ℕ) (total : Total p ht result fuel) :
    AllInputRun p ht result fuel (decides p ht result fuel) := by
  intro n x bits
  obtain ⟨actual, hrun⟩ := total n x bits
  refine ⟨actual, hrun, ?_⟩
  constructor
  · intro hs
    exact ⟨actual, hrun, hs⟩
  · rintro ⟨other, hother, hs⟩
    rw [hrun] at hother
    rw [Option.some.injEq] at hother
    exact hother ▸ hs

/-- The decided predicate is decidable *by the machine*: on every input the
scanned result bit either witnesses `decides` or refutes it. Stated so the
soundness and completeness consumers can case on one run. -/
theorem decides_iff {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (fuel : ℕ → ℕ)
    (n : ℕ) (x : BitInput n) (bits : List Bool) (actual : ExecutionReceipt t s)
    (hrun : run p (fuel n)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) = some actual) :
    decides p ht result fuel n x bits ↔ actual.final.scanned result = true := by
  constructor
  · rintro ⟨other, hother, hs⟩
    rw [hrun] at hother
    rw [Option.some.injEq] at hother
    exact hother ▸ hs
  · intro hs
    exact ⟨actual, hrun, hs⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.Weak
