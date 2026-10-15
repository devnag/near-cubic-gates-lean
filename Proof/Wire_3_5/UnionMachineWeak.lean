import Proof.Wire_3_5.UnionCheck
import Proof.Wire_3_5.UnionEventual
import Proof.Wire_3_5.TransferUnionSound
import Proof.MachineModel.UAcceptanceCarrier

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.Transfer

/-! ## The weak machine of a worker -/

section Weak
variable {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t) (fuel : ℕ → ℕ)
  (meaning : (n : ℕ) → BitInput n → List Bool → Prop)

/-- The worker's runs on the refuter's witnesses: halting within `fuel N`, with the result cell set iff the meaning
holds. -/
def WitnessRun : Prop :=
  ∀ (n : ℕ) (x : BitInput n) (w : BitInput (n / 16)), ∃ r,
    run p (fuel n) ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) (List.ofFn w)) = some r ∧
      (r.final.scanned result = true ↔ meaning n x (List.ofFn w))

/-- **The weak machine of a worker**: the worker, then base's two-step acceptance gate. -/
def weakOf (h : WitnessRun p ht result fuel meaning) : OrdinaryWeakMachine where
  verifier := UAcceptanceCarrier.verifier p ht result
  runtime := fun n => fuel n + 2
  halts := by
    intro n x w
    obtain ⟨r, hr, _⟩ := h n x w
    exact ⟨_, (UAcceptanceCarrier.verifier_run p ht result (fuel n) _ _ r hr).1⟩

theorem weakOf_runtime (h : WitnessRun p ht result fuel meaning) (n : ℕ) :
    (weakOf p ht result fuel meaning h).runtime n = fuel n + 2 := rfl

/-- **The weak machine accepts** exactly when some `⌊N/16⌋`-bit witness has the meaning. -/
theorem weakOf_accepts (h : WitnessRun p ht result fuel meaning) (n : ℕ) (x : BitInput n) :
    (weakOf p ht result fuel meaning h).accepts n x ↔ ∃ w : BitInput (n / 16), meaning n x (List.ofFn w) := by
  unfold OrdinaryWeakMachine.accepts Verifier.language
  apply exists_congr
  intro w
  obtain ⟨r, hr, hm⟩ := h n x w
  exact (UAcceptanceCarrier.accepts_transfer p ht result (fuel n) _ _ r hr).trans hm

end Weak

/-! ## The useless inhabitants -/

/-- A three-tape worker writing `b` into its result cell (tape `2`) in one step. -/
def setWorker (b : Bool) : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun i => if i.val = 2 then some b else none, fun _ => .stay⟩
    else none

theorem setWorker_run (b : Bool) (A : Fin 3 → List Bool) (hA : A 2 = []) :
    ∃ r, run (setWorker b) 1 A = some r ∧ r.final.scanned 2 = b := by
  refine ⟨_, rfl, ?_⟩
  simp [setWorker, initialConfiguration, applyAction, Configuration.scanned, hA, writeTapeBit, readTapeBit,
    HeadMove.apply]

theorem three_le : 2 ≤ 3 := by omega

theorem setWorker_witnessRun (b : Bool) :
    WitnessRun (setWorker b) three_le (2 : Fin 3) (fun _ => 1) (fun n _ _ => b = true ∧ 0 ≤ n) := by
  intro n x w
  obtain ⟨r, hr, hs⟩ := setWorker_run b ((UAcceptanceCarrier.verifier (setWorker b) three_le (2 : Fin 3)).inputTapes
    (List.ofFn x) (List.ofFn w)) (by simp [Verifier.inputTapes, UAcceptanceCarrier.verifier])
  exact ⟨r, hr, by rw [hs]; simp⟩

/-- **The machine that never accepts.** -/
def rejectAll : OrdinaryWeakMachine := weakOf _ _ _ _ _ (setWorker_witnessRun false)

/-- **The machine that accepts every input.** -/
def acceptAll : OrdinaryWeakMachine := weakOf _ _ _ _ _ (setWorker_witnessRun true)

theorem rejectAll_rejects (n : ℕ) (x : BitInput n) : ¬ rejectAll.accepts n x := by
  rw [rejectAll, weakOf_accepts]
  rintro ⟨_, h, _⟩
  exact Bool.false_ne_true h

theorem acceptAll_accepts (n : ℕ) (x : BitInput n) : acceptAll.accepts n x := by
  rw [acceptAll, weakOf_accepts]
  exact ⟨fun _ => false, rfl, Nat.zero_le _⟩

section Controls
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **Control: never accepting is not eventually complete** for a setup and primitive with accepting guesses at
arbitrarily large lengths. -/
theorem rejectAll_not_complete (S : UnionSetup I) (P : FusedPrimitive I)
    (hacc : ∀ onset : ℕ, ∃ N, onset ≤ N ∧ ∃ (z : BitInput N) (g : UnionGuess S z), UnionAccepts S P z g) :
    ¬ CompleteForEventually S P rejectAll := by
  rintro ⟨onset, h⟩
  obtain ⟨N, hN, z, g, hg⟩ := hacc onset
  exact rejectAll_rejects N z (h N hN z g hg)

/-- **Control: accepting everything is not one-sided** for a language with no-instances at arbitrarily large
lengths. -/
theorem acceptAll_not_oneSided (L : Language) (hno : ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ x : BitInput n, L n x = false) :
    ¬ OneSided acceptAll L := by
  rintro ⟨n₀, h⟩
  obtain ⟨n, hn, x, hx⟩ := hno n₀
  have := h n hn x (acceptAll_accepts n x)
  rw [hx] at this
  exact Bool.false_ne_true this

end Controls

end NearCubicWires.WireExponent3_5.UnionMachine
