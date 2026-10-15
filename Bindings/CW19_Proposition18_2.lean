import Proof.Foundations.RepresentationSourceContracts
import Proof.Circuits.DecompositionSourceBounds
import StatementSupport

/-!
# Binding: CW19 Proposition 18(2) → `RepairRepresentation.DecompositionSource`

Source PDF: `CW19_Chen_Williams_Stronger_Connections_via_PCPP.pdf`
(CCC 2019, pages numbered 19:1–19:43). The p.14 quotation was checked against the rendered
page image.

* PDF page 14 (printed 19:14), §2.1, verbatim:
  "Proposition 18. The following hold: … 2. THR ⊆ DOR ◦ ETHR [24]. (also see Appendix B) …
  Moreover, all the above have corresponding polynomial-time, deterministic constructions."
* PDF page 13 (printed 19:13), §2.1 "Notations for Circuit Classes", verbatim:
  "Let x ∈ {0, 1}^n. For w ∈ R^n and t ∈ R, we define THR_{w,t}(x) (the threshold function) to be
  the indicator function for the condition w · x ≥ t. Similarly, ETHR_{w,t}(x) (the exact
  threshold function) is the indicator function for the condition w · x = t. … It is known that,
  without loss of generality, the weights and thresholds are integers of absolute value at most
  2^{O(n log n)} [33, 7]." and, continuing onto PDF p.14: "We use DOR_n to denote the disjoint
  OR function, that is, an OR function with the promise that at most one input bit is true over
  all inputs."
* PDF page 14: "For two classes of functions like THR and MAJ, we use THR ◦ MAJ to denote the
  corresponding class of depth-two circuits."
* PDF page 41 (printed 19:41), Appendix B, Lemma 49, verbatim: "Let G be a THR gate on n bits,
  G(x) := [Σ_{i=1}^n w_i · x_i > T], such that all w_i's and T are integers from [−W, W] for some
  W ∈ N. Then G can be written as a DOR of O(n · log W) many ETHR gates, each with weights and
  threshold from [−Θ(W), Θ(W)]."

## Transcription choices

* **What is asserted.** Item 2 with the "Moreover" sentence: ONE deterministic polynomial-time
  algorithm that, given a THR gate `G`, outputs a DOR ◦ ETHR circuit computing the same Boolean
  function as `G`. `CW19_Proposition18_2` says: there is a construction `dor` sending every THR
  gate to a DOR ◦ ETHR circuit that computes it (`Computes`), and `dor` is computed by one fixed
  ordinary program in time polynomial in the length of the gate's description
  (`PolynomialTimeConstruction dor`).
* **Gate descriptions are integral, with the appendix's strict convention.** An algorithm reads a
  finite description, so the input gate has integer weights and threshold, exactly as in the
  cited construction (Appendix B, Lemma 49: `G(x) := [Σ w_i · x_i > T]` with integers). The strict
  `>` is the convention of that construction. §2.1 defines `THR` with `≥` and real parameters;
  for integers, `[w · x ≥ t] = [w · x > t − 1]`, so the class is the same.
  `nonStrict_integral_containment` below proves that the literal also covers every integral `≥`
  gate. The step from real to integral parameters is the "without loss of generality" remark of
  p.13 (CTW26 Lemma 3.2, bound separately in `Bindings.CTW26_Lemma3_2`). The import needs only the
  integral strict form.
* **ETHR gates are integral** (the construction outputs finite descriptions; Appendix B's ETHR
  gates have integer weights and thresholds), indicator of `w · x = t` on `x ∈ {0,1}^n`.
* **DOR ◦ ETHR circuit.** A top DOR gate whose inputs are ETHR gates `E_1, …, E_m` on the same
  `n` input bits, listed in order and with repetitions (a gate list, not a set). It is a legal
  DOR ◦ ETHR circuit when the DOR promise holds: on every `x ∈ {0,1}^n`, at most one `E_j(x)` is
  true. Its value is then the OR of the `E_j(x)`.
* **Every arity `n`, including `n = 0`.** The paper does not exclude `n = 0`. There the gate is a
  constant, and a DOR of zero ETHR gates (constant false) or of the single gate `[0 = 0]`
  (constant true) computes it, so the literal is true there.
* **"polynomial-time", hidden constants.** The weakest faithful reading: there EXIST constants
  `C` and `d` (chosen with the algorithm, uniform over all gates) such that the run on the
  description of `G` halts within `C · (ℓ + 1)^d` steps, where `ℓ` is the description length.
* **Tier 1 machine model.** The algorithmic clause is the separable structure
  `PolynomialTimeConstruction`, stated in the repo's model `RepairOrdinary.WordFunction`
  (`OrdinaryWordFunction`, `Proof/Foundations/OrdinaryMachine.lean`; the machine is
  `Proof/Foundations/LocalBitMultitapeCore.lean`: finite control, Boolean cells, local writes,
  unit head moves, one step per transition, deterministic). Descriptions are the conventional
  explicit binary words: `gateWord G` lists `n`, then `w_1, …, w_n`, then `T`; `circuitWord C`
  lists `m`, then for each ETHR gate its weights and its threshold. A natural number is written
  self-delimited (`natWord`, a unary length then the binary digits) and an integer as its sign bit
  then `natWord` of its absolute value (`intWord`). The input word is framed on tape 0 and the
  output appears on a fresh tape. Tier 2 replaces only this structure.
* **No sharp bounds are asserted.** The literal claims neither the gate count `O(n · log W)` nor
  the weight range `[−Θ(W), Θ(W)]` of Lemma 49, nor the range `[0, 2^{L+1} − 1]` of Lemma 48. The
  import needs only the qualitative polynomial-time construction. The printed sharp appendix
  claims contain errors and must not be imported. Checked against
  PDF pp.40–42:
  1. Lemma 48, p.41: "hence the sequence S is non-decreasing (and begins with 0)". The first term
     of `S` is `w^{(n,L)} · x = 2^{L−1} · w_{n,L} · x_n`, which need not be `0`.
  2. Lemma 48, p.41: "By division, T = 2^{b−1} · T_b + T_r, for some 0 ≤ T_r < 2^{b−1} and
     T_b > 0." The quotient `T_b = ⌊T / 2^{b−1}⌋` is `0` whenever `T < 2^{b−1}`.
  3. Lemma 48's gate `E^{(a,b)}(x) := [(2 · w^{(a,b)} · x) + x_a = 2^b · (T_b + 1) + 1]` has
     threshold up to `2^{L+1} + 1`, outside the printed range `[0, 2^{L+1} − 1]` (e.g. `n = L = 1`,
     `w_1 = T = 1`, `b = 1`: the threshold is `5 > 3`).
  4. Lemma 49, p.41: after negating the negative weights, `T̂ = T − Σ_{i∉S} w_i` can reach
     `(n + 1) · W`, so Lemma 48 applies with `2^L` of order `n · W`. The weights and thresholds are
     then of order `n · W`, not `Θ(W)`, and the count is `O(n · log(n W))`, not `O(n · log W)`
     (which is `0` at `W = 1`).
  None of this affects the qualitative claim: the construction, with these repairs, is a
  deterministic polynomial-time algorithm, and it is the one imported. The manuscript replays the
  quantitative argument locally where it needs sharp bounds.

## The adapter

`cw19_to_import` keeps the SAME program. It checks the conventions of `Proof/Foundations/Semantics.lean`
(`NormalizedThresholdGate.strictEval` is `threshold < Σ`, `ExactThresholdGate.eval` is `Σ = target`,
`ExactDecomposition` = `any` plus at most one accepting child), identifies the words
(`gateWord_eq`, `circuitWord_eq`), and enlarges the budget using the existing
`RepairOrdinary.DecompositionSource.thresholdWord_bound`
(`Proof/Circuits/DecompositionSourceBounds.lean`, `|thresholdWord g| ≤ 8 (n + bits + 1)`).
-/

namespace NearCubicWires.Bindings.CW19

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
open NearCubicWires.ExecutableInterfaces
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The literal -/

/-- TIER 1 ALGORITHMIC CLAUSE (separable). "polynomial-time, deterministic constructions": ONE
ordinary deterministic multitape program which, on the description of every THR gate `G`, halts
within `C · (|gateWord G| + 1)^d` steps with the description of `dor G` on a fresh tape. -/
structure PolynomialTimeConstruction (dor : (n : ℕ) → THRGate n → DORofETHR n) where
  C : ℕ
  d : ℕ
  algorithm : OrdinaryWordFunction ((n : ℕ) × THRGate n)
    (fun G => gateWord G.2) (fun G => circuitWord (dor G.1 G.2))
    (fun G => C * ((gateWord G.2).length + 1) ^ d)

/-- **CW19 Proposition 18(2), PDF page 14, verbatim:** "2. THR ⊆ DOR ◦ ETHR [24]. (also see
Appendix B)" … "Moreover, all the above have corresponding polynomial-time, deterministic
constructions."

Read with the conventions of p.13–14 and of Appendix B, Lemma 49 (p.41), as explained in the
module docstring: one construction `dor` taking every integral THR gate `[Σ w_i x_i > T]` on `n`
bits (every `n`) to a DOR ◦ ETHR circuit computing it, computed in polynomial time (Tier 1). -/
def CW19_Proposition18_2 : Prop :=
  ∃ dor : (n : ℕ) → THRGate n → DORofETHR n,
    (∀ (n : ℕ) (G : THRGate n), (dor n G).Computes G) ∧ Nonempty (PolynomialTimeConstruction dor)

/-! ## Sanity: the §2.1 non-strict convention is covered -/

/-- §2.1 (p.13): "THR_{w,t}(x) … the indicator function for the condition w · x ≥ t", with
integer realizations. -/
def nonStrictEval {n : ℕ} (w : Fin n → ℤ) (t : ℤ) (x : Fin n → ℤ) : Bool :=
  decide (∑ i, w i * x i ≥ t)

/-- The literal covers §2.1's convention: every integral `THR_{w,t}` (`w · x ≥ t`) is computed by
a DOR ◦ ETHR circuit, namely `dor` applied to the strict gate `[w · x > t − 1]`. -/
theorem nonStrict_integral_containment (h : CW19_Proposition18_2) (n : ℕ) (w : Fin n → ℤ)
    (t : ℤ) : ∃ C : DORofETHR n, C.Promise ∧
      ∀ x : Fin n → ℤ, IsBoolVec x → C.eval x = nonStrictEval w t x := by
  obtain ⟨dor, hcomp, _⟩ := h
  obtain ⟨hprom, heval⟩ := hcomp n ⟨w, t - 1⟩
  refine ⟨dor n ⟨w, t - 1⟩, hprom, fun x hx => ?_⟩
  rw [heval x hx]
  unfold THRGate.eval nonStrictEval
  dsimp only
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)

/-! ## Bridges to the import's vocabulary -/

/-- A Boolean input, as the 0-1 vector of `ℤ^n`. -/
def bitVec {n : ℕ} (input : BitInput n) : Fin n → ℤ := fun i => if input i then 1 else 0

theorem isBoolVec_bitVec {n : ℕ} (input : BitInput n) : IsBoolVec (bitVec input) := by
  intro i
  unfold bitVec
  cases input i <;> simp

/-- The import's gate, read as a literal THR gate. -/
def ofNormalized {n : ℕ} (g : NormalizedThresholdGate n) : THRGate n := ⟨g.weight, g.threshold⟩

/-- A literal ETHR gate, as the import's exact gate. -/
def toExact {n : ℕ} (E : ETHRGate n) : ExactThresholdGate n := ⟨E.w, E.t⟩

/-- The import's strict evaluation IS the literal `[Σ w_i x_i > T]`. -/
theorem strictEval_eq {n : ℕ} (g : NormalizedThresholdGate n) (input : BitInput n) :
    g.strictEval input = (ofNormalized g).eval (bitVec input) := rfl

/-- The import's exact evaluation IS the literal `[w · x = t]`. -/
theorem exactEval_eq {n : ℕ} (E : ETHRGate n) (input : BitInput n) :
    (toExact E).eval input = E.eval (bitVec input) := rfl

/-- The literal gate word IS the import's `thresholdWord`. -/
theorem gateWord_eq {n : ℕ} (g : NormalizedThresholdGate n) :
    gateWord (ofNormalized g) = thresholdWord g := rfl

/-- The literal circuit word IS the import's `exactListWord` of the same gate list. -/
theorem circuitWord_eq {n : ℕ} (C : DORofETHR n) :
    circuitWord C = exactListWord (C.gates.map toExact) := by
  unfold circuitWord exactListWord
  rw [List.length_map, List.flatMap_map]
  rfl

/-- The literal's polynomial in the description length is below the import's polynomial in
`n + bits + 1`. -/
theorem budget_le (Cc d : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) :
    Cc * ((gateWord (ofNormalized g)).length + 1) ^ d ≤
      ((Cc + 1) * 9 ^ d) * (n + g.encodingBits + 1) ^ d := by
  rw [gateWord_eq]
  have hb := RepairOrdinary.DecompositionSource.thresholdWord_bound g
  have hle : (thresholdWord g).length + 1 ≤ 9 * (n + g.encodingBits + 1) := by omega
  calc Cc * ((thresholdWord g).length + 1) ^ d
      ≤ (Cc + 1) * (9 * (n + g.encodingBits + 1)) ^ d :=
        Nat.mul_le_mul (Nat.le_succ Cc) (Nat.pow_le_pow_left hle d)
    _ = ((Cc + 1) * 9 ^ d) * (n + g.encodingBits + 1) ^ d := by rw [mul_pow, mul_assoc]

/-! ## The adapter -/

/-- The import's decomposition of one request: the literal circuit's gate list. -/
def outputOf (dor : (n : ℕ) → THRGate n → DORofETHR n)
    (hcomp : ∀ (n : ℕ) (G : THRGate n), (dor n G).Computes G)
    (r : ExactDecompositionRequest) : ExactDecomposition r.gate where
  children := (dor r.arity (ofNormalized r.gate)).gates.map toExact
  equivalent := by
    intro input
    rw [strictEval_eq, ← (hcomp r.arity (ofNormalized r.gate)).2 _ (isBoolVec_bitVec input),
      List.any_map]
    rfl
  disjoint := by
    intro input
    rw [List.filter_map, List.length_map]
    exact (hcomp r.arity (ofNormalized r.gate)).1 _ (isBoolVec_bitVec input)

/-- **Adapter.** The literal CW19 Proposition 18(2) (Tier 1) implies the imported
`RepairRepresentation.DecompositionSource`, with the same program. -/
theorem cw19_to_import : CW19_Proposition18_2 → DecompositionSource := by
  rintro ⟨dor, hcomp, ⟨P⟩⟩
  refine ⟨{
    output := outputOf dor hcomp
    coefficient := (P.C + 1) * 9 ^ P.d
    degree := P.d
    coefficientPositive := Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by norm_num))
    constructor := ⟨P.algorithm.program, ?_⟩ }⟩
  intro r
  obtain ⟨receipt, hrun, hout⟩ := P.algorithm.realizes ⟨r.arity, ofNormalized r.gate⟩
  refine ⟨receipt, ?_, ?_⟩
  · have hmore := RepairOrdinary.run_moreFuel P.algorithm.program.machine _
      ((P.C + 1) * 9 ^ P.d * (r.arity + r.gate.encodingBits + 1) ^ P.d -
        P.C * ((gateWord (ofNormalized r.gate)).length + 1) ^ P.d) _ receipt hrun
    rw [Nat.add_sub_of_le (budget_le P.C P.d r.gate)] at hmore
    simpa only [gateWord_eq] using hmore
  · rw [hout, circuitWord_eq]
    rfl

end NearCubicWires.Bindings.CW19
