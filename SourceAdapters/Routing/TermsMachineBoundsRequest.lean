import SourceAdapters.Routing.TermsMachineBounds
import SourceAdapters.Routing.TermsMachineBoundsLengths
import SourceAdapters.Routing.TermsMachineInput

/-! # Exact terms-request capacity discharge -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Bounds

open NearCubicWires
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Routing.CoordinateMachine

/-- The public request has exactly the parser's input layout. -/
theorem input_eq_headerInput (p : TermsReq) (h : TermsOk p) :
    termsInput p h = headerInput p.f p.l.m (termsCoordWord p h) (globalBank p.l)
      (p.items.flatMap (itemWord (termsMask p h)) ++ RepairRepresentation.natWord 0) := by
  simp only [termsInput, headerInput, List.append_assoc]

theorem coord_length_le (p : TermsReq) (h : TermsOk p) :
    (termsCoordWord p h).length ≤ (termsInput p h).length := by
  have hh := input_length p h
  rw [coord_length]
  omega

theorem mask_bitLength_le (p : TermsReq) (h : TermsOk p) (c : Field2 p.irr) :
    natBitLength (termsMask p h c) ≤ (termsInput p h).length := by
  have hf : 1 ≤ p.f := by have := h.2.2.1; have := h.2.2.2; omega
  exact (NearCubicGates.Adapters.RAMACSP.Gen.natBitLength_le_of_lt hf (mask_lt p h c)).trans
    (request_size p h).1

theorem bank_words (p : TermsReq) (h : TermsOk p) :
    ∀ x ∈ globalBank p.l, x < 2 ^ wordWidth (termsInput p h).length := by
  intro x hx
  have hb := bank_bitLength_le p h hx
  have hx' := NearCubicGates.Close.Cells.lt_natBitLength x
  have hw : natBitLength x ≤ wordWidth (termsInput p h).length := by unfold wordWidth; omega
  exact hx'.trans_le (Nat.pow_le_pow_right (by norm_num : 0 < 2) hw)

/-- All local parser capacity premises, from the actual request alone. -/
theorem prepared_parser_bounds (p : TermsReq) (h : TermsOk p) :
    let rawN := (termsInput p h).length
    let G := globOf (preparedInput (termsInput p h))
    BdOk G rawN ∧ p.l.m * p.l.m ≤ G.cap ∧ 2 ^ (termsCoordWord p h).length ≤ G.cap ∧
      (∀ x ∈ globalBank p.l, x < 2 ^ wordWidth rawN) ∧
      wordWidth rawN * (globalBank p.l).length ≤ G.K := by
  intro rawN G
  have hs := request_size p h
  have hr := raw_le_arithmetic rawN
  have hc : arithmeticBound rawN ≤ G.cap := prepared_arithmetic_cap (termsInput p h)
  refine ⟨prepared_BdOk (termsInput p h), by omega, ?_, bank_words p h,
    prepared_product (termsInput p h) _ hs.2.2.2.1⟩
  apply prepared_pow
  have hl := coord_length_le p h
  unfold wordWidth
  omega

/-- All bank lookup capacity premises, independent of the sought mask. -/
theorem prepared_lookup_bounds (p : TermsReq) (h : TermsOk p) :
    let rawN := (termsInput p h).length
    let G := globOf (preparedInput (termsInput p h))
    (globalBank p.l).length ≤ G.N ∧ (globalBank p.l).length + 1 ≤ G.cap ∧
      (globalBank p.l).length * wordWidth rawN ≤ G.cap ∧ 2 ^ wordWidth rawN ≤ G.cap := by
  intro rawN G
  have hs := (request_size p h).2.2.2.1
  have hr := raw_le_arithmetic rawN
  have hK : arithmeticBound rawN + 3 ≤ G.K ∧ G.K = G.N := prepared_large (termsInput p h)
  have hc := cap_ge G
  have hp := prepared_product (termsInput p h) _ hs
  refine ⟨by omega, by omega, ?_, prepared_pow (termsInput p h) _ le_rfl⟩
  rw [Nat.mul_comm]
  exact hp.trans hc

/-- Every gate or input index needed by the emitted circuit fits an entry. -/
theorem index_lt_width (p : TermsReq) (h : TermsOk p) (v : ℕ)
    (hv : v ≤ 10 * ((termsInput p h).length + 1)) :
    v < 2 ^ wordWidth (termsInput p h).length := by
  have hh := Nat.lt_two_pow_self (n := wordWidth (termsInput p h).length)
  have hw : v ≤ wordWidth (termsInput p h).length := by unfold wordWidth; omega
  exact hw.trans_lt hh

/-- Any stack of at most raw-input-length entries has its exact packed value below the clamp. -/
theorem prepared_stack_bound (p : TermsReq) (h : TermsOk p) (refs : List ℕ)
    (hlen : refs.length ≤ (termsInput p h).length)
    (hwords : ∀ x ∈ refs, x < 2 ^ wordWidth (termsInput p h).length) :
    packW (wordWidth (termsInput p h).length) refs ≤ (globOf (preparedInput (termsInput p h))).cap :=
  prepared_pack (termsInput p h) refs hlen hwords

theorem prepared_stack_indices (p : TermsReq) (h : TermsOk p) (refs : List ℕ)
    (hlen : refs.length ≤ (termsInput p h).length)
    (hindices : ∀ x ∈ refs, x ≤ 10 * ((termsInput p h).length + 1)) :
    packW (wordWidth (termsInput p h).length) refs ≤ (globOf (preparedInput (termsInput p h))).cap :=
  prepared_stack_bound p h refs hlen (fun x hx => index_lt_width p h x (hindices x hx))

/-- A common numeric bound and the bit-width requirements of the raw natural-number emitter. -/
theorem prepared_numeric_bounds (p : TermsReq) (h : TermsOk p) :
    let rawN := (termsInput p h).length
    let G := globOf (preparedInput (termsInput p h))
    arithmeticBound rawN ≤ G.cap ∧
      (∀ v ≤ max (arithmeticBound rawN) (2 ^ p.f), natBitLength v + 2 ≤ G.K) ∧
      (∀ v ≤ max (arithmeticBound rawN) (2 ^ p.f), v ≤ G.cap) ∧ G.K ≤ G.N := by
  intro rawN G
  exact ⟨prepared_arithmetic_cap (termsInput p h),
    fun v hv => prepared_natBitLength (termsInput p h) p.f v (request_size p h).1 hv,
    fun v hv => prepared_value_cap (termsInput p h) p.f v (request_size p h).1 hv,
    (prepared_large (termsInput p h)).2.le⟩

/-- The coordinate prefix, gate count and packed-address arithmetic fit the common bound. -/
theorem request_arithmetic (p : TermsReq) (h : TermsOk p) :
    let rawN := (termsInput p h).length
    let M := arithmeticBound rawN
    p.f ≤ M ∧ p.l.m ≤ M ∧ p.l.m * p.l.m ≤ M ∧ p.l.m * p.l.m * p.f ≤ M ∧
      (globalBank p.l).length + 1 ≤ M ∧ p.items.length ≤ M ∧
      (termsCircuit p h).length + 1 ≤ M ∧ 3 * p.l.m ^ 2 + 2 * p.l.m + 1 ≤ M ∧
      wordWidth rawN * rawN + 3 ≤ M := by
  intro rawN M
  have hs := request_size p h
  have hc := circuit_length_le p h
  have hco := coord_length_le p h
  rw [coord_length] at hco
  have hr := raw_le_arithmetic rawN
  have hp := product_le_arithmetic rawN rawN le_rfl
  have hi : 10 * (rawN + 1) + 1 ≤ M := by dsimp [M, arithmeticBound]; nlinarith
  have hpref : 3 * p.l.m ^ 2 + 2 * p.l.m + 1 ≤ 10 * (rawN + 1) := by
    rw [pow_two]
    omega
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, hp⟩

end NearCubicGates.Adapters.Routing.TermsMachine.Bounds
