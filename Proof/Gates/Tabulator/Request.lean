import Proof.Gates.Tabulator.Print

set_option autoImplicit false

namespace NearCubicGates.Close.Tabulator

open scoped BigOperators
open NearCubicWires NearCubicWires.ThresholdCompiler NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.MatrixScoreBatch

/-! ## eq:print-condition -/

/-- eq:print-condition (lem:print), `k + 2 + D lg(1 + G'' m_T) ≤ m/100` with `m` = `s` rounded up to an even
integer, in the exact integer form `(2^{k+2} (1 + G'' m_T)^D)^{100} ≤ 2^m`. -/
def PrintCondition (k s D V mT : ℕ) : Prop := (2 ^ (k + 2) * (1 + V * mT) ^ D) ^ 100 ≤ 2 ^ (s + s % 2)

/-- The real-valued printing condition `eq:print-condition` implies the integer form. -/
theorem printCondition_of_real (k s D V mT : ℕ)
    (h : (k : ℝ) + 2 + D * Real.logb 2 (1 + V * mT) ≤ ((s + s % 2 : ℕ) : ℝ) / 100) :
    PrintCondition k s D V mT := by
  have hX : (0 : ℝ) < 1 + V * mT := by positivity
  have hkey : ((2 ^ (k + 2) * (1 + V * mT) ^ D : ℕ) : ℝ) =
      (2 : ℝ) ^ ((k : ℝ) + 2 + D * Real.logb 2 (1 + V * mT)) := by
    rw [Real.rpow_add (by norm_num), mul_comm (D : ℝ), Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hX, Real.rpow_natCast]
    have h2 : (2 : ℝ) ^ ((k : ℝ) + 2) = (2 : ℝ) ^ (k + 2) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [h2]
    push_cast
    ring
  have hle : ((2 ^ (k + 2) * (1 + V * mT) ^ D : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((s + s % 2 : ℕ) : ℝ) / 100) := by
    rw [hkey]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  have hpow : ((2 ^ (k + 2) * (1 + V * mT) ^ D : ℕ) : ℝ) ^ 100 ≤ ((2 : ℝ) ^ (((s + s % 2 : ℕ) : ℝ) / 100)) ^ 100 :=
    pow_le_pow_left₀ (by positivity) hle 100
  have he : ((2 : ℝ) ^ (((s + s % 2 : ℕ) : ℝ) / 100)) ^ 100 = (2 : ℝ) ^ (s + s % 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : ((s + s % 2 : ℕ) : ℝ) / 100 * ((100 : ℕ) : ℝ) = ((s + s % 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [he] at hpow
  unfold PrintCondition
  exact_mod_cast hpow

theorem printCondition_s (k s D V mT : ℕ) (h : PrintCondition k s D V mT) : 67 ≤ s := by
  have h1 : 1 ≤ (1 + V * mT) ^ D := Nat.one_le_pow _ _ (by omega)
  have h2 : (2 ^ (k + 2)) ^ 100 ≤ 2 ^ (s + s % 2) := by
    refine le_trans ?_ h
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ h1) 100
  rw [← pow_mul, Nat.pow_le_pow_iff_right (by norm_num)] at h2
  have : s % 2 ≤ 1 := by omega
  omega

theorem printCondition_capacity (k s D V mT E : ℕ) (h : PrintCondition k s D V mT)
    (hE : E ≤ 2 ^ k * (1 + V * mT) ^ D) : E ^ 100 ≤ 2 ^ s := by
  have hs := printCondition_s k s D V mT h
  have hA : (2 ^ k * (1 + V * mT) ^ D) ^ 100 * 2 ^ 200 ≤ 2 ^ s * 2 ^ 200 := by
    have e1 : (2 ^ k * (1 + V * mT) ^ D) ^ 100 * 2 ^ 200 = (2 ^ (k + 2) * (1 + V * mT) ^ D) ^ 100 := by
      rw [pow_add]; ring
    rw [e1, ← pow_add]
    exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact (Nat.pow_le_pow_left hE 100).trans (Nat.le_of_mul_le_mul_right hA (by positivity))

theorem printCondition_gates (k s D V mT E : ℕ) (h : PrintCondition k s D V mT)
    (hE : E ≤ 2 ^ k * (1 + V * mT) ^ D) : (2 * (2 * E)) ^ 100 ≤ 2 ^ (s + s % 2) := by
  refine le_trans (Nat.pow_le_pow_left ?_ 100) h
  calc 2 * (2 * E) ≤ 2 * (2 * (2 ^ k * (1 + V * mT) ^ D)) := by omega
    _ = 2 ^ (k + 2) * (1 + V * mT) ^ D := by rw [pow_add]; ring

/-! ## Coefficient widths -/

theorem stack_bound {C : Type} [Fintype C] (b P : ℕ) (es : List (LabelledEquation C))
    (hes : ∀ e ∈ es, (∀ u, (e.weights u).natAbs ≤ P) ∧ e.target.natAbs ≤ P) :
    (∀ u, ((stackEquations (b : ℤ) es).weights u).natAbs ≤ P * (b + 1) ^ es.length) ∧
      (stackEquations (b : ℤ) es).target.natAbs ≤ P * (b + 1) ^ es.length := by
  induction es with
  | nil => simp [stackEquations]
  | cons e es ih =>
    obtain ⟨ihw, iht⟩ := ih (fun f hf => hes f (by simp [hf]))
    obtain ⟨hew, het⟩ := hes e (by simp)
    have hone : 1 ≤ (b + 1) ^ es.length := Nat.one_le_pow _ _ (by omega)
    have step : ∀ a c : ℤ, a.natAbs ≤ P → c.natAbs ≤ P * (b + 1) ^ es.length →
        (a + (b : ℤ) * c).natAbs ≤ P * (b + 1) ^ (es.length + 1) := by
      intro a c ha hc
      have h1 := Int.natAbs_add_le a ((b : ℤ) * c)
      rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
      have h2 : b * c.natAbs ≤ b * (P * (b + 1) ^ es.length) := Nat.mul_le_mul_left _ hc
      have h3 : P ≤ P * (b + 1) ^ es.length := Nat.le_mul_of_pos_right _ hone
      calc (a + (b : ℤ) * c).natAbs ≤ a.natAbs + b * c.natAbs := h1
        _ ≤ P * (b + 1) ^ es.length + b * (P * (b + 1) ^ es.length) := by omega
        _ = P * (b + 1) ^ (es.length + 1) := by ring
    refine ⟨fun u => ?_, ?_⟩
    · simp only [stackEquations, List.length_cons]
      exact step _ _ (hew u) (ihw u)
    · simp only [stackEquations, List.length_cons]
      exact step _ _ het iht

/-- The parameter envelope of every packed cut: `P_c (β+1)^D` with `P_c` the lem:exact envelope after restriction
and `β = D (s+1) P_c + 1` the packing radix bound. -/
def fieldBound (n s D B : ℕ) : ℕ :=
  childBound s (B + Nat.clog 2 (n + 1)) *
    (D * ((s + 1) * childBound s (B + Nat.clog 2 (n + 1))) + 1 + 1) ^ D

/-- The printer's coefficient width (before its own `+1` for the weak-cut split). -/
def fieldBits (n s D B cbits : ℕ) : ℕ := max (Nat.size (fieldBound n s D B)) cbits

namespace Tabulation

variable {n k s G V : ℕ} (T : Tabulation n k s G V)

/-- The bit bounds of lem:print's data: gate parameters below `2^B`, polynomial coefficients below `2^cbits`,
distinct monomials of degree at most `D`. -/
structure Bounds (B D cbits : ℕ) : Prop where
  gates : ∀ i, GateBits B (T.gates i)
  nodup : (Terms.keys T.Q).Nodup
  degree : ∀ S ∈ Terms.keys T.Q, S.card ≤ D
  coeff : ∀ t ∈ T.Q, t.2.natAbs < 2 ^ cbits

theorem kids_params (B : ℕ) (hB : ∀ i, GateBits B (T.gates i)) (x : Fin k → Bool) (v : Fin V)
    (e : RowBinLift.Equation ((s + 1) / 2) (s / 2)) (he : e ∈ T.kids x v) :
    (∀ u, (e.weights u).natAbs ≤ childBound s (B + Nat.clog 2 (n + 1))) ∧
      e.target.natAbs ≤ childBound s (B + Nat.clog 2 (n + 1)) := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  have h := exactChildren_params _ _ (restrict_bits B _ T.layout _ (hB _)) c hc
  exact ⟨fun u => h.1 _, h.2⟩

theorem magnitude_le (P : ℕ) (e : RowBinLift.Equation ((s + 1) / 2) (s / 2))
    (he : (∀ u, (e.weights u).natAbs ≤ P) ∧ e.target.natAbs ≤ P) :
    SupplierPrime.equationMagnitudeBound e ≤ (s + 1) * P := by
  unfold SupplierPrime.equationMagnitudeBound
  have h1 : (∑ u, (e.weights u).natAbs) ≤ ∑ _u : Fin ((s + 1) / 2) ⊕ Fin (s / 2), P :=
    Finset.sum_le_sum (fun u _ => he.1 u)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    halves_card, smul_eq_mul] at h1
  have := he.2
  rw [add_mul, one_mul]
  omega

/-- Every cut fits the printer's coefficient width `fieldBits`. -/
theorem fits_of_bounds (B D cbits : ℕ) (hb : T.Bounds B D cbits) :
    ∀ c ∈ T.exactCuts, EquationRow.Fits (fieldBits n s D B cbits) c := by
  intro c hc
  unfold exactCuts at hc
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
  split at hi
  case isFalse => simp at hi
  case isTrue =>
  obtain ⟨t, ht, htc⟩ := List.mem_flatMap.mp hi
  obtain ⟨es, hes, rfl⟩ := List.mem_map.mp htc
  set Pc := childBound s (B + Nat.clog 2 (n + 1)) with hPc
  have hesP : ∀ e ∈ es, (∀ u, (e.weights u).natAbs ≤ Pc) ∧ e.target.natAbs ≤ Pc := by
    intro e he
    obtain ⟨L, hL, heL⟩ := mem_tuples_mem _ es hes e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hL
    exact T.kids_params B hb.gates _ v e heL
  have hlen : es.length ≤ D := by
    rw [mem_tuples_length _ es hes, List.length_map, Finset.length_sort]
    exact hb.degree t.1 (List.mem_map_of_mem ht)
  have hbase : (es.map SupplierPrime.equationMagnitudeBound).sum + 1 ≤ D * ((s + 1) * Pc) + 1 := by
    have h := List.sum_le_card_nsmul (es.map SupplierPrime.equationMagnitudeBound) ((s + 1) * Pc) (by
      intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact magnitude_le (s := s) Pc e (hesP e he))
    rw [List.length_map, smul_eq_mul] at h
    have := Nat.mul_le_mul_right ((s + 1) * Pc) hlen
    omega
  have hst := stack_bound ((es.map SupplierPrime.equationMagnitudeBound).sum + 1) Pc es hesP
  have hmono : Pc * ((es.map SupplierPrime.equationMagnitudeBound).sum + 1 + 1) ^ es.length ≤
      fieldBound n s D B := by
    unfold fieldBound
    rw [← hPc]
    apply Nat.mul_le_mul_left
    calc ((es.map SupplierPrime.equationMagnitudeBound).sum + 1 + 1) ^ es.length
        ≤ (D * ((s + 1) * Pc) + 1 + 1) ^ es.length := Nat.pow_le_pow_left (by omega) _
      _ ≤ (D * ((s + 1) * Pc) + 1 + 1) ^ D := Nat.pow_le_pow_right (by omega) hlen
  have hbits : fieldBound n s D B < 2 ^ fieldBits n s D B cbits :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hstack : ∀ z : ℤ, z.natAbs ≤ Pc * ((es.map SupplierPrime.equationMagnitudeBound).sum + 1 + 1) ^ es.length →
      z.natAbs < 2 ^ fieldBits n s D B cbits := fun z hz => (hz.trans hmono).trans_lt hbits
  unfold SupplierEstimator.canonicalEquationStack SupplierEstimator.equationListBase
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simp only [RowBinLift.split, List.mem_append, List.mem_ofFn] at hw
    rcases hw with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact hstack _ (hst.1 _)
    · exact hstack _ (hst.1 _)
  · exact hstack _ hst.2
  · exact (hb.coeff t ht).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- The exact-cut input of the printer: `⌈s/2⌉` row bits, the odd flag when `s` is odd, coefficient width `p`. -/
def input (p : ℕ) (hfits : ∀ c ∈ T.exactCuts, EquationRow.Fits p c) (hs : 67 ≤ s)
    (hcap : T.exactCuts.length ^ 100 ≤ 2 ^ s) : EquationRow.Input where
  d := (s + 1) / 2
  p := p
  odd := decide (s % 2 = 1)
  cuts := T.exactCuts
  lengths := by
    intro c hc
    obtain ⟨hl, hr⟩ := T.exactCuts_lengths c hc
    refine ⟨hl, ?_⟩
    rw [hr]
    by_cases h : s % 2 = 1 <;> simp [h] <;> omega
  fits := hfits
  oddPositive := by intro _; omega
  gateSquare := EquationRow.doubled_gateSquare hs hcap

theorem input_value (p : ℕ) (hfits : ∀ c ∈ T.exactCuts, EquationRow.Fits p c) (hs : 67 ≤ s)
    (hcap : T.exactCuts.length ^ 100 ≤ 2 ^ s)
    (row column : Fin (EquationRow.request (T.input p hfits hs hcap)).U) :
    SupplierPrinter.weightedDominance (leftScore (EquationRow.request (T.input p hfits hs hcap)))
        (rightScore (EquationRow.request (T.input p hfits hs hcap)))
        (weight (EquationRow.request (T.input p hfits hs hcap))) row column =
      T.target (outerPoint s row.val column.val) := by
  rw [EquationRow.request_value]
  exact T.exactCuts_value row.val column.val

/-! ## The end theorem -/

theorem capacity_of_condition (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1)))) : T.exactCuts.length ^ 100 ≤ 2 ^ s :=
  printCondition_capacity k s D V _ _ hc (T.exactCuts_length_le_pow B D hb.gates hb.nodup hb.degree)

/-- **lem:print's Request.** Built from the gates, the inner layout, the filter `H` and the polynomial `Q`, under
the bit bounds and eq:print-condition with `m_T` of lem:exact for the restricted gates (lem:print). -/
def printRequest (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1)))) : Request :=
  EquationRow.request (T.input (fieldBits n s D B cbits) (T.fits_of_bounds B D cbits hb)
    (printCondition_s k s D V _ hc) (T.capacity_of_condition B D cbits hb hc))

/-- **lem:print, value.** The printer's weighted-dominance entry at `(row, column)` is `∑_{x ∈ H} Q(y,x)` for the
outer assignment `y = outerPoint s row column` (row bits first, then column bits). -/
theorem printRequest_value (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1))))
    (row column : Fin (T.printRequest B D cbits hb hc).U) :
    SupplierPrinter.weightedDominance (leftScore (T.printRequest B D cbits hb hc))
        (rightScore (T.printRequest B D cbits hb hc)) (weight (T.printRequest B D cbits hb hc)) row column =
      ∑ x ∈ T.H, Terms.eval (T.value (outerPoint s row.val column.val) x) T.Q :=
  T.input_value _ _ _ _ row column

/-- **lem:print, count.** `(2 · #weak cuts)^{100} ≤ 2^m`: at most `2^{m/100-1}` weak cuts (proof of lem:print). -/
theorem printRequest_gates (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1)))) :
    (2 * (T.printRequest B D cbits hb hc).Gates) ^ 100 ≤ 2 ^ (s + s % 2) := by
  unfold printRequest
  rw [EquationRow.request_gates]
  exact printCondition_gates k s D V _ _ hc (T.exactCuts_length_le_pow B D hb.gates hb.nodup hb.degree)

theorem printRequest_d (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1)))) :
    (T.printRequest B D cbits hb hc).d = (s + 1) / 2 := rfl

theorem printRequest_p (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1)))) :
    (T.printRequest B D cbits hb hc).p = fieldBits n s D B cbits + 1 := rfl

theorem printRequest_cuts (B D cbits : ℕ) (hb : T.Bounds B D cbits)
    (hc : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1)))) :
    (T.printRequest B D cbits hb hc).cuts = EquationRow.doubled (decide (s % 2 = 1)) T.exactCuts := rfl

end Tabulation

/-! ## `Q` expanded from a formula -/

/-- lem:print's data with `Q` the expansion of a formula (lem:print). -/
def formulaTabulation {n k s G V : ℕ} (gates : Fin G → NormalizedThresholdGate n) (layout : Fin n ≃ Fin k ⊕ Fin s)
    (H : Finset (Fin k → Bool)) (role : Fin V → Role G) (F : Formula V) : Tabulation n k s G V :=
  ⟨gates, layout, H, role, F.expand⟩

theorem formulaTabulation_bounds {n k s G V : ℕ} (gates : Fin G → NormalizedThresholdGate n)
    (layout : Fin n ≃ Fin k ⊕ Fin s) (H : Finset (Fin k → Bool)) (role : Fin V → Role G) (F : Formula V)
    (B : ℕ) (hB : ∀ i, GateBits B (gates i)) :
    (formulaTabulation gates layout H role F).Bounds B F.degree (F.weight + 1) where
  gates := hB
  nodup := F.expand_keys_nodup
  degree := F.expand_card_le
  coeff := fun t ht => (F.expand_coeff_le_two_pow t ht).trans_lt (Nat.pow_lt_pow_succ (by norm_num))

/-- lem:print for a formula: the printed entry is `∑_{x ∈ H} F(y,x)`. -/
theorem formulaRequest_value {n k s G V : ℕ} (gates : Fin G → NormalizedThresholdGate n)
    (layout : Fin n ≃ Fin k ⊕ Fin s) (H : Finset (Fin k → Bool)) (role : Fin V → Role G) (F : Formula V)
    (B : ℕ) (hB : ∀ i, GateBits B (gates i))
    (hc : PrintCondition k s F.degree V (mT s (B + Nat.clog 2 (n + 1))))
    (row column : Fin ((formulaTabulation gates layout H role F).printRequest B F.degree (F.weight + 1)
      (formulaTabulation_bounds gates layout H role F B hB) hc).U) :
    SupplierPrinter.weightedDominance
        (leftScore ((formulaTabulation gates layout H role F).printRequest B F.degree (F.weight + 1)
          (formulaTabulation_bounds gates layout H role F B hB) hc))
        (rightScore ((formulaTabulation gates layout H role F).printRequest B F.degree (F.weight + 1)
          (formulaTabulation_bounds gates layout H role F B hB) hc))
        (weight ((formulaTabulation gates layout H role F).printRequest B F.degree (F.weight + 1)
          (formulaTabulation_bounds gates layout H role F B hB) hc)) row column =
      ∑ x ∈ H, F.eval (boolPoint ((formulaTabulation gates layout H role F).value
        (outerPoint s row.val column.val) x)) := by
  rw [Tabulation.printRequest_value]
  apply Finset.sum_congr rfl
  intro x _
  exact F.expand_eval _

/-!
# The counter's two tables through lem:print

`sec:algorithm`: "These operations are legal applications of lem:print, with the residue
polynomials of lem:residue-count ... moments have degree at most `2k ≤ D_max`." This module composes the end
theorem of lem:print (`Tabulator.Request`) with the two instances (`Tabulator.Instances`):

* `residueRequest_count`: the printed entry, reduced modulo `p^e`, is the exact joint residue count
  `#{x ∈ H : L_i(y,x) ≡ ρ_i (mod p) for all i}` (lem:residue-count).
* `momentRequest_value`: the printed entry is `∑_{x ∈ H} (∑_t c_t (g_t(y,x) - g_t(y,0^I)))^{2h}` (table (b) of `sec:algorithm`).
* `printCondition_mono`, `mT_mono`: the printing condition may be supplied with any larger `D`, `G''` or `m_T`,
  in particular with the paper's restriction growth `⌈lg(n+1)⌉ + 1` (`printCondition_paper`, proof of `lem:print`).
-/

open scoped BigOperators
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.MatrixScoreBatch

theorem mT_mono (m : ℕ) {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) : mT m B₁ ≤ mT m B₂ := by
  unfold mT blockBits
  have : (B₁ + Nat.clog 2 (m + 1) + 1) * m * ((m + 1) / 2) ≤ (B₂ + Nat.clog 2 (m + 1) + 1) * m * ((m + 1) / 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  omega

theorem printCondition_mono {k s D₁ D₂ V₁ V₂ m₁ m₂ : ℕ} (hD : D₁ ≤ D₂) (hV : V₁ ≤ V₂) (hm : m₁ ≤ m₂)
    (h : PrintCondition k s D₂ V₂ m₂) : PrintCondition k s D₁ V₁ m₁ := by
  unfold PrintCondition at h ⊢
  refine le_trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ?_) 100) h
  calc (1 + V₁ * m₁) ^ D₁ ≤ (1 + V₂ * m₂) ^ D₁ := Nat.pow_le_pow_left (by nlinarith) _
    _ ≤ (1 + V₂ * m₂) ^ D₂ := Nat.pow_le_pow_right (by omega) hD

/-- The paper states restriction growth `⌈lg(n+1)⌉ + 1` (proof of lem:print); our restriction needs only `⌈lg(n+1)⌉`, so the
paper's printing condition (`eq:print-condition`) implies the one the Request uses. -/
theorem printCondition_paper {n k s D V B : ℕ}
    (h : PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1) + 1))) :
    PrintCondition k s D V (mT s (B + Nat.clog 2 (n + 1))) :=
  printCondition_mono le_rfl le_rfl (mT_mono s (by omega)) h

/-- **Residue table** (lem:residue-count through lem:print): the printed entry at `(row, column)`, reduced modulo
`p^e`, is the number of `x ∈ H` with `L_i(y,x) ≡ ρ_i (mod p)` for all `i`, `y = outerPoint s row column`. -/
theorem residueRequest_count {n k s G V r : ℕ} (gates : Fin G → NormalizedThresholdGate n)
    (layout : Fin n ≃ Fin k ⊕ Fin s) (H : Finset (Fin k → Bool)) (role : Fin V → Role G)
    (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : 1 ≤ e) (L : Fin r → AffineForm V) (ρ : Fin r → ℤ)
    (hH : H.card < p ^ e) (B : ℕ) (hB : ∀ i, GateBits B (gates i))
    (hc : PrintCondition k s (residueFormula p e L ρ).degree V (mT s (B + Nat.clog 2 (n + 1))))
    (row column : Fin ((formulaTabulation gates layout H role (residueFormula p e L ρ)).printRequest B
      (residueFormula p e L ρ).degree ((residueFormula p e L ρ).weight + 1)
      (formulaTabulation_bounds gates layout H role _ B hB) hc).U) :
    (SupplierPrinter.weightedDominance
        (leftScore ((formulaTabulation gates layout H role (residueFormula p e L ρ)).printRequest B
          (residueFormula p e L ρ).degree ((residueFormula p e L ρ).weight + 1)
          (formulaTabulation_bounds gates layout H role _ B hB) hc))
        (rightScore ((formulaTabulation gates layout H role (residueFormula p e L ρ)).printRequest B
          (residueFormula p e L ρ).degree ((residueFormula p e L ρ).weight + 1)
          (formulaTabulation_bounds gates layout H role _ B hB) hc))
        (weight ((formulaTabulation gates layout H role (residueFormula p e L ρ)).printRequest B
          (residueFormula p e L ρ).degree ((residueFormula p e L ρ).weight + 1)
          (formulaTabulation_bounds gates layout H role _ B hB) hc)) row column) % ((p : ℤ) ^ e) =
      ((H.filter fun x => ∀ i, (L i).eval (boolPoint ((formulaTabulation gates layout H role
        (residueFormula p e L ρ)).value (outerPoint s row.val column.val) x)) ≡ ρ i [ZMOD (p : ℤ)]).card : ℤ) := by
  rw [formulaRequest_value gates layout H role _ B hB hc]
  exact residue_count p hp e he L ρ H _ hH

/-- **Moment table** (table (b) of `sec:algorithm`, with `Δ_y H = H(y,x) - H(y,0^I)` of `sec:prelim`): with `a t` the
formal variable of
gate `t` at `(y,x)` and `r t` the one of gate `t` at `(y,0^I)`, the printed entry is
`∑_{x ∈ H} (∑_t c_t (g_t(y,x) - g_t(y,0^I)))^{2h}`. -/
theorem momentRequest_value {n k s G V : ℕ} (gates : Fin G → NormalizedThresholdGate n)
    (layout : Fin n ≃ Fin k ⊕ Fin s) (H : Finset (Fin k → Bool)) (role : Fin V → Role G)
    (c : Fin G → ℤ) (a r : Fin G → Fin V) (ha : ∀ t, role (a t) = ⟨t, false⟩) (hr : ∀ t, role (r t) = ⟨t, true⟩)
    (h : ℕ) (B : ℕ) (hB : ∀ i, GateBits B (gates i))
    (hc : PrintCondition k s (momentFormula c a r h).degree V (mT s (B + Nat.clog 2 (n + 1))))
    (row column : Fin ((formulaTabulation gates layout H role (momentFormula c a r h)).printRequest B
      (momentFormula c a r h).degree ((momentFormula c a r h).weight + 1)
      (formulaTabulation_bounds gates layout H role _ B hB) hc).U) :
    SupplierPrinter.weightedDominance
        (leftScore ((formulaTabulation gates layout H role (momentFormula c a r h)).printRequest B
          (momentFormula c a r h).degree ((momentFormula c a r h).weight + 1)
          (formulaTabulation_bounds gates layout H role _ B hB) hc))
        (rightScore ((formulaTabulation gates layout H role (momentFormula c a r h)).printRequest B
          (momentFormula c a r h).degree ((momentFormula c a r h).weight + 1)
          (formulaTabulation_bounds gates layout H role _ B hB) hc))
        (weight ((formulaTabulation gates layout H role (momentFormula c a r h)).printRequest B
          (momentFormula c a r h).degree ((momentFormula c a r h).weight + 1)
          (formulaTabulation_bounds gates layout H role _ B hB) hc)) row column =
      ∑ x ∈ H, (∑ t, c t *
        ((if (gates t).eval (joinPoint layout (outerPoint s row.val column.val) x) then 1 else 0) -
          (if (gates t).eval (joinPoint layout (outerPoint s row.val column.val) (fun _ => false))
            then 1 else 0))) ^ (2 * h) := by
  rw [formulaRequest_value gates layout H role _ B hB hc]
  apply Finset.sum_congr rfl
  intro x _
  rw [momentFormula_eval]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [boolPoint, Tabulation.value, formulaTabulation, ha, hr, roleInner, Bool.false_eq_true,
    ↓reduceIte]

end NearCubicGates.Close.Tabulator
