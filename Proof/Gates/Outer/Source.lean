import Proof.Gates.Main.ShortPCP
import Bindings.TuringBridge.Budget

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape NearCubicWires.Bindings.MW20

/-- The import applied to one verifier `V` with time bound `T`: the constructor `A` (an ordinary word function from
`frame x ++ frame (binary T(n))` to the circuit's word), and the four printed properties for `n ≥ 1`. -/
structure MWSourceAlgorithm (V : OrdinaryVerifier) (T : ℕ → ℕ) where
  output : InputRequest → OracleOutput
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  constructionExp : ℕ
  ellExp : ℕ
  sizeExp : ℕ
  /-- "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle circuit C^O_x". -/
  constructor : OrdinaryWordFunction InputRequest
    (fun r => frame (List.ofFn r.2) ++ frame (T r.1).bits) (fun r => (output r).word)
    (fun r => coefficient * (r.1 + natBitLength (T r.1) + 1) ^ constructionExp)
  /-- "ℓ = log₂(T(n)) + O(log log T(n)) inputs" (upper half). -/
  ellBound : ∀ r : InputRequest, 1 ≤ r.1 →
    2 ^ (output r).ell ≤ coefficient * T r.1 * logScale (T r.1) ^ ellExp
  /-- "poly(n, log T(n)) size". -/
  sizeBound : ∀ r : InputRequest, 1 ≤ r.1 →
    (output r).circuit.size ≤ coefficient * (r.1 + natBitLength (T r.1) + 1) ^ sizeExp
  /-- Completeness: some oracle makes `C^O_x` unsatisfiable. -/
  complete : ∀ r : InputRequest, 1 ≤ r.1 → V.language T r.1 r.2 →
    ∃ O : BitInput (output r).ell → Bool, ∀ z, (output r).circuit.eval O z = false

  sound : ∀ r : InputRequest, 1 ≤ r.1 → ¬ V.language T r.1 r.2 →
    ∀ O : BitInput (output r).ell → Bool,
      (2 : ℝ) ^ (output r).ell * (1 - 1 / (r.1 : ℝ)) ≤ ((output r).satCount O : ℝ)

/-- The import for every verifier and time bound. -/
def MWSource : Prop :=
  ∀ (V : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → RunsInTime V T → Nonempty (MWSourceAlgorithm V T)

/-- The constructor's input word has length at most `2 · (n + natBitLength (T n) + 1)`. -/
theorem input_length_le (T : ℕ → ℕ) (x : InputRequest) :
    (frame (List.ofFn x.2) ++ frame (T x.1).bits).length ≤ 2 * (x.1 + natBitLength (T x.1) + 1) ^ 1 := by
  have hbits : (T x.1).bits.length ≤ natBitLength (T x.1) := by
    rw [Nat.size_eq_bits_len]
    unfold natBitLength
    exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) _)
  simp only [List.length_append, RepairOrdinary.frame_length, List.length_ofFn, pow_one]
  omega

/-- The literal (a Mathlib TM2 constructor) gives the ordinary import. -/
theorem mwSource_of_literal (h : MW20_OracleCircuitPCP_TM2) : MWSource := by
  intro V T hT hrun
  obtain ⟨out, ⟨A⟩, ⟨Kl, el, hl⟩, ⟨Ks, es, hs⟩, hc, hsd⟩ := h V T hT hrun
  obtain ⟨Kc, ec, ⟨W⟩⟩ := Bindings.Sim.tm2Poly_ordinary A (fun x => x.1 + natBitLength (T x.1)) 2 1
    (input_length_le T)
  refine ⟨{
    output := out
    coefficient := Kc + Kl + Ks + 1
    coefficientPositive := by omega
    constructionExp := ec
    ellExp := el
    sizeExp := es
    constructor := RepairOrdinary.WordFunction.enlargeBudget W ?_
    ellBound := fun r hr => (hl r hr).trans ?_
    sizeBound := fun r hr => (hs r hr).trans ?_
    complete := fun r hr hy => hc r hr hy
    sound := fun r hr hn O => hsd r hr hn O }⟩
  · intro r
    exact Nat.mul_le_mul_right _ (by omega)
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · exact Nat.mul_le_mul_right _ (by omega)

end NearCubicGates.Close.Outer
