import SourceAdapters.Joins.ComputationToCNF

/-!
proof of `lem:multitape-refuter`, Step 3: half-open witness prefixes [0, high).
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.SourceInterfaces

set_option autoImplicit false

private theorem rankFold_lt (bits : List Bool) (acc : ℕ) :
    bits.foldl (fun value bit => 2 * value + if bit then 1 else 0) acc <
      (acc + 1) * 2 ^ bits.length := by
  induction bits generalizing acc with
  | nil => simp
  | cons bit bits ih =>
      have h := ih (2 * acc + if bit then 1 else 0)
      simp only [List.foldl_cons, List.length_cons, pow_succ]
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h ⊢ <;>
        nlinarith

/-- Full prefix high = 2^k contains every k-bit witness, including k = 0. -/
theorem witnessRank_lt {k : ℕ} (witness : BitInput k) : witnessRank witness < 2 ^ k := by
  simpa only [witnessRank, List.length_ofFn, Nat.zero_add, Nat.one_mul] using
    rankFold_lt (List.ofFn witness) 0

/-- The first lexicographic witness is represented at every exact length. -/
theorem witnessRank_zero (k : ℕ) : witnessRank (fun _ : Fin k => false) = 0 := by
  simp only [witnessRank, List.ofFn_const]
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [List.replicate_succ, List.foldl_cons, Bool.false_eq_true,
        ↓reduceIte, Nat.mul_zero, Nat.zero_add] using ih

/-- proof of `lem:multitape-refuter`, Step 3: the search's empty prefix has no accepting witness. -/
theorem noWitness_below_zero (r : CNFCompilationRequest) (h : r.high = 0) :
    ¬ r.accepts := by
  simp [CNFCompilationRequest.accepts, h]

/-- proof of `lem:multitape-refuter`, Step 3: full-range membership is the request with high = 2^k. -/
theorem fullWitnessRange (r : CNFCompilationRequest) (h : r.high = 2 ^ r.witnessLength) :
    r.accepts ↔ ∃ witness : BitInput r.witnessLength,
      r.verifier.acceptsAt r.fuel r.input (List.ofFn witness) := by
  constructor
  · rintro ⟨witness, _, ha⟩
    exact ⟨witness, ha⟩
  · rintro ⟨witness, ha⟩
    exact ⟨witness, h ▸ witnessRank_lt witness, ha⟩

example : witnessRank ![true, false] = 2 := by decide

example : witnessRank ![false, true] = 1 := by decide

example : witnessRank ![false, false] < 1 := by decide

example : ¬ witnessRank ![false, true] < 1 := by decide

end NearCubicGates.Adapters.Compile
