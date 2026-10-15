import Proof.Wire_3_5.UnionCheck

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost NearCubicWires.RepairSource

section Eventual
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **Eventual completeness of a machine**: past an onset, every accepting guess of the setup makes the
machine accept. -/
def CompleteForEventually (S : UnionSetup I) (P : FusedPrimitive I) (M : OrdinaryWeakMachine) : Prop :=
  ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), UnionAccepts S P z g → M.accepts N z

variable {S : UnionSetup I} {P : FusedPrimitive I} {M : OrdinaryWeakMachine}

theorem CompleteFor.eventually (h : CompleteFor S P M) : CompleteForEventually S P M :=
  ⟨0, fun N _ z g hg => h N z g hg⟩

/-- The Case-2 use: an accepting guess past the onset is accepted. -/
theorem accepts_of_completeForEventually (h : CompleteForEventually S P M) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (z : BitInput N), (∃ g : UnionGuess S z, UnionAccepts S P z g) →
      M.accepts N z := by
  obtain ⟨onset, h⟩ := h
  exact ⟨onset, fun N hN z ⟨g, hg⟩ => h N hN z g hg⟩

/-- A machine that, past an onset, accepts whenever some witness of its length `W(N) ≥ ⌊N/16⌋` makes `unionRun`
accept is eventually complete. -/
theorem completeForEventually_of_run (callOk : PrimRequest → Bool)
    (hok : ∀ {N : ℕ} (z : BitInput N) (g : UnionGuess S z), ∀ r ∈ (g.checkData g.translation).schedule,
      callOk r = true ↔ I.Call r)
    (W : ℕ → ℕ) (hW : ∀ N, N / 16 ≤ W N) (onset : ℕ)
    (hM : ∀ N, onset ≤ N → ∀ (z : BitInput N), (∃ w : List Bool, w.length = W N ∧
      unionRun S z UnionGuess.translation callOk P.value w = true) → M.accepts N z) :
    CompleteForEventually S P M := by
  refine ⟨onset, fun N hN z g hg => hM N hN z ?_⟩
  exact unionRun_complete P callOk g (hok z g) hg (W N) (hW N)

end Eventual

end NearCubicWires.WireExponent3_5.Transfer
