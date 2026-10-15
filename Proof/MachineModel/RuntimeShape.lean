import Proof.Supplier.SupplierCapacity
import Proof.Supplier.SupplierEstimator
import Proof.MachineModel.TopDownSelectedRuntime

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RuntimeShape
open SupplierEstimator SupplierCapacity

/-! ## 1. The logarithm facts the table saving uses -/

/-- `Nat.clog 2 (q+2) ≥ Nat.log 2 q + 1`: the live logarithm dominates the consumer's. -/
theorem log_succ_le_logScale (q : ℕ) : Nat.log 2 q + 1 ≤ logScale q := by
  unfold logScale
  have h : Nat.log 2 q < Nat.clog 2 (q+2) := by
    rw [Nat.lt_clog_iff_pow_lt (by decide)]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp
    · have hp := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hq)
      omega
  omega

theorem succ_le_two_pow_logScale (q : ℕ) : q+1 ≤ 2^logScale q := by
  unfold logScale
  have h := Nat.le_pow_clog (by decide : 1 < 2) (q+2)
  omega

theorem succ_pow_le (q h : ℕ) : (q+1)^h ≤ 2^(h*logScale q) := by
  calc (q+1)^h ≤ (2^logScale q)^h := Nat.pow_le_pow_left (succ_le_two_pow_logScale q) h
    _ = 2^(h*logScale q) := by rw [← pow_mul, Nat.mul_comm]

/-- Unsaturated regime: the live count is exactly `L*logScale q`. -/
theorem normalizedLiveCount_eq (q L : ℕ) (h : L*logScale q ≤ q) :
    normalizedLiveCount q L = L*logScale q := by
  unfold normalizedLiveCount
  exact min_eq_right h

/-! ## 2. Absorption of each class into the consumer's allowance -/

/-- **Table class.** `(q+1)^hT*2^(q-K) ≤ 2^(q-(σ+2)(log q+1))` once `L*logScale q ≤ q`,
provided the live scale was chosen after the table exponent: `hT+σ+2 ≤ L`. -/
theorem table_absorb (σ L hT q : ℕ) (horder : hT+σ+2 ≤ L) (hfit : L*logScale q ≤ q) :
    (q+1)^hT*2^(q-normalizedLiveCount q L) ≤ 2^(q-(σ+2)*(Nat.log 2 q+1)) := by
  rw [normalizedLiveCount_eq q L hfit]
  have hl := log_succ_le_logScale q
  have hA : hT*logScale q+(σ+2)*logScale q ≤ L*logScale q := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hD : (σ+2)*(Nat.log 2 q+1) ≤ (σ+2)*logScale q := Nat.mul_le_mul_left _ hl
  calc (q+1)^hT*2^(q-L*logScale q) ≤ 2^(hT*logScale q)*2^(q-L*logScale q) :=
        Nat.mul_le_mul_right _ (succ_pow_le q hT)
    _ = 2^(hT*logScale q+(q-L*logScale q)) := by rw [pow_add]
    _ ≤ 2^(q-(σ+2)*(Nat.log 2 q+1)) := Nat.pow_le_pow_right (by decide) (by omega)

/-- **Small class.** `(q+1)^hS*2^(q/m) ≤ 2^(q-(σ+2)(log q+1))` once
`2*((hS+σ+2)*logScale q) ≤ q`, for every divisor `m ≥ 2`. -/
theorem small_absorb (σ hS m q : ℕ) (hm : 2 ≤ m) (hfit : 2*((hS+σ+2)*logScale q) ≤ q) :
    (q+1)^hS*2^(q/m) ≤ 2^(q-(σ+2)*(Nat.log 2 q+1)) := by
  have hl := log_succ_le_logScale q
  have hD : (σ+2)*(Nat.log 2 q+1) ≤ (σ+2)*logScale q := Nat.mul_le_mul_left _ hl
  have hsplit : (hS+σ+2)*logScale q = hS*logScale q+(σ+2)*logScale q := by ring
  have hdiv : q/m ≤ q/2 := Nat.div_le_div_left hm (by decide)
  have h2 : 2*(q/2) ≤ q := Nat.mul_div_le q 2
  calc (q+1)^hS*2^(q/m) ≤ 2^(hS*logScale q)*2^(q/m) :=
        Nat.mul_le_mul_right _ (succ_pow_le q hS)
    _ = 2^(hS*logScale q+q/m) := by rw [pow_add]
    _ ≤ 2^(q-(σ+2)*(Nat.log 2 q+1)) := Nat.pow_le_pow_right (by decide) (by omega)

theorem eventually_absorbing (σ L hS : ℕ) : ∃ q0, ∀ q, q0 ≤ q →
    L*logScale q ≤ q ∧ 2*((hS+σ+2)*logScale q) ≤ q := by
  obtain ⟨q0, h0⟩ := coefficient_mul_logScale_pow_eventually_le (L+2*(hS+σ+2)) 1
  refine ⟨q0, fun q hq => ?_⟩
  have h := h0 q hq
  rw [pow_one] at h
  have he : (L+2*(hS+σ+2))*logScale q = L*logScale q+2*((hS+σ+2)*logScale q) := by ring
  omega

/-- The chosen width onset (explicit, so the recipe's onset is a function). -/
noncomputable def absorbOnset (σ L hS : ℕ) : ℕ := Classical.choose (eventually_absorbing σ L hS)

theorem absorbOnset_spec (σ L hS q : ℕ) (hq : absorbOnset σ L hS ≤ q) :
    L*logScale q ≤ q ∧ 2*((hS+σ+2)*logScale q) ≤ q :=
  Classical.choose_spec (eventually_absorbing σ L hS) q hq

/-- Past the onset every natural subtraction in the target is untruncated: the live count is
unsaturated (`K = L*logScale q ≤ q`) and the consumer exponent `(σ+2)(log q+1) ≤ q`. -/
theorem untruncated_at_onset (σ L hT hS q : ℕ) (horder : hT+σ+2 ≤ L)
    (hq : absorbOnset σ L hS ≤ q) :
    normalizedLiveCount q L = L*logScale q ∧ L*logScale q ≤ q ∧
      (σ+2)*(Nat.log 2 q+1) ≤ q := by
  obtain ⟨hfit, _⟩ := absorbOnset_spec σ L hS q hq
  have hl := log_succ_le_logScale q
  have hD : (σ+2)*(Nat.log 2 q+1) ≤ (σ+2)*logScale q := Nat.mul_le_mul_left _ hl
  have hA : (σ+2)*logScale q ≤ L*logScale q := Nat.mul_le_mul_right _ (by omega)
  exact ⟨normalizedLiveCount_eq q L hfit, hfit, by omega⟩

/-! ## 3. The shape theorem, generic in the width function -/

/-- Pointwise form with explicit witnesses: coefficient `cP+3`, table coefficient `cT+cS`,
onset `max n0 N`, where `N` forces the width past `absorbOnset`. -/
theorem runtime_shape_at (σ L hT hS m dP cP cT cS n0 N : ℕ) (q F : ℕ → ℕ)
    (hm : 2 ≤ m) (horder : hT+σ+2 ≤ L)
    (hN : ∀ n, N ≤ n → absorbOnset σ L hS ≤ q n)
    (hF : ∀ n, n0 ≤ n → F n ≤ cP*(n+1)^dP+
      cT*((q n+1)^hT*2^(q n-normalizedLiveCount (q n) L))+cS*((q n+1)^hS*2^(q n/m))) :
    ∀ n, max n0 N ≤ n →
      F n+3 ≤ (cP+3)*(n+1)^dP+(cT+cS)*(2^(q n-(σ+0+2)*(Nat.log 2 (q n)+1))*(q n+1)^0) := by
  intro n hn
  have hn0 : n0 ≤ n := le_of_max_le_left hn
  obtain ⟨hfit, hfit'⟩ := absorbOnset_spec σ L hS (q n) (hN n (le_of_max_le_right hn))
  have ht := Nat.mul_le_mul_left cT (table_absorb σ L hT (q n) horder hfit)
  have hs := Nat.mul_le_mul_left cS (small_absorb σ hS m (q n) hm hfit')
  have hf := hF n hn0
  have hpos : 1 ≤ (n+1)^dP := Nat.one_le_pow _ _ (Nat.succ_pos n)
  change F n+3 ≤ (cP+3)*(n+1)^dP+(cT+cS)*(2^(q n-(σ+2)*(Nat.log 2 (q n)+1))*1)
  have e1 : (cP+3)*(n+1)^dP = cP*(n+1)^dP+3*(n+1)^dP := by ring
  have e2 : (cT+cS)*(2^(q n-(σ+2)*(Nat.log 2 (q n)+1))*1) =
      cT*2^(q n-(σ+2)*(Nat.log 2 (q n)+1))+cS*2^(q n-(σ+2)*(Nat.log 2 (q n)+1)) := by ring
  omega

/-- **The shape theorem.** Any fuel eventually in the three classes, with the live scale
chosen after the table exponent, meets the consumer's inequality with the same source degree
and `tableDegree = 0`, for any width tending to infinity. -/
theorem runtime_shape (σ L hT hS m dP cP cT cS n0 : ℕ) (q F : ℕ → ℕ)
    (hm : 2 ≤ m) (horder : hT+σ+2 ≤ L)
    (hgrow : ∀ T, ∃ N, ∀ n, N ≤ n → T ≤ q n)
    (hF : ∀ n, n0 ≤ n → F n ≤ cP*(n+1)^dP+
      cT*((q n+1)^hT*2^(q n-normalizedLiveCount (q n) L))+cS*((q n+1)^hS*2^(q n/m))) :
    ∃ coefficient onset tableCoefficient : ℕ, ∀ n, onset ≤ n →
      F n+3 ≤ coefficient*(n+1)^dP+
        tableCoefficient*(2^(q n-(σ+0+2)*(Nat.log 2 (q n)+1))*(q n+1)^0) := by
  obtain ⟨N, hN⟩ := hgrow (absorbOnset σ L hS)
  exact ⟨cP+3, max n0 N, cT+cS,
    runtime_shape_at σ L hT hS m dP cP cT cS n0 N q F hm horder hN hF⟩

/-! ## 4. At the consumer's own width, logarithm and sigma -/

open P1TopDown

/-- `SelectedRuntime.width C` passes any fixed threshold once `2^T ≤ n`
(`C10LedgerAssembly.nativeWidth_ge`); no growth hypothesis is left to the caller. -/
theorem width_grows {sources : RepairSource.EightSources} {gamma : ℝ}
    {p : RepairSource.CloseoutFinal.Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (T n : ℕ) (hn : 2^T ≤ n) :
    T ≤ SelectedRuntime.width C n :=
  RepairSource.CloseoutFinal.C10LedgerAssembly.nativeWidth_ge sources C.k C.clock T n hn

structure Split (σ : ℕ) (q : ℕ → ℕ) (sourceDegree : ℕ) (F : ℕ → ℕ) where
  liveScale : ℕ
  tableExponent : ℕ
  smallExponent : ℕ
  smallDivisor : ℕ
  sourceCoefficient : ℕ
  tableCoefficient : ℕ
  smallCoefficient : ℕ
  onset : ℕ
  two_le_divisor : 2 ≤ smallDivisor
  /-- `paper.tex:2307`: the live scale is chosen after the table exponent. -/
  order : tableExponent+σ+2 ≤ liveScale
  bound : ∀ n, onset ≤ n → F n ≤ sourceCoefficient*(n+1)^sourceDegree+
    tableCoefficient*((q n+1)^tableExponent*2^(q n-normalizedLiveCount (q n) liveScale))+
    smallCoefficient*((q n+1)^smallExponent*2^(q n/smallDivisor))

/-- Explicit consumer witnesses produced by a split at the selected width. -/
def Split.remainingCoefficient {σ dP : ℕ} {q F : ℕ → ℕ} (s : Split σ q dP F) : ℕ :=
  s.sourceCoefficient+3
def Split.remainingTable {σ dP : ℕ} {q F : ℕ → ℕ} (s : Split σ q dP F) : ℕ :=
  s.tableCoefficient+s.smallCoefficient
noncomputable def Split.remainingOnset {σ dP : ℕ} {q F : ℕ → ℕ} (s : Split σ q dP F) : ℕ :=
  max s.onset (2^absorbOnset σ s.liveScale s.smallExponent)

/-- **The runtime contract at the consumer.** For every continuation `C` and every fuel that
splits at `SelectedRuntime.width C` with `σ = SelectedRuntime.sigma sources`, the final
`MaskedRecipe` inequality holds literally, at `tableDegree = 0`. -/
theorem Split.runtime {sources : RepairSource.EightSources} {gamma : ℝ}
    {p : RepairSource.CloseoutFinal.Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) {dP : ℕ} {F : ℕ → ℕ}
    (s : Split (SelectedRuntime.sigma sources) (SelectedRuntime.width C) dP F) :
    ∀ n, s.remainingOnset ≤ n → F n+3 ≤ s.remainingCoefficient*(n+1)^dP+
      s.remainingTable*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+0+2)*
        SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^0) :=
  runtime_shape_at (SelectedRuntime.sigma sources) s.liveScale s.tableExponent s.smallExponent
    s.smallDivisor dP s.sourceCoefficient s.tableCoefficient s.smallCoefficient s.onset
    (2^absorbOnset (SelectedRuntime.sigma sources) s.liveScale s.smallExponent)
    (SelectedRuntime.width C) F s.two_le_divisor s.order
    (fun n hn => width_grows C _ n hn) s.bound

/-- Existential form, exactly the shape of `SelectedRuntime.of_paper_body_bound`'s `hbody`
consumers and of the recipe conjunct. -/
theorem selected_runtime_shape {sources : RepairSource.EightSources} {gamma : ℝ}
    {p : RepairSource.CloseoutFinal.Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (F : ℕ → ℕ) (dP : ℕ)
    (s : Split (SelectedRuntime.sigma sources) (SelectedRuntime.width C) dP F) :
    ∃ coefficient onset tableCoefficient : ℕ, ∀ n, onset ≤ n →
      F n+3 ≤ coefficient*(n+1)^dP+
        tableCoefficient*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+0+2)*
          SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^0) :=
  ⟨s.remainingCoefficient, s.remainingOnset, s.remainingTable, s.runtime C⟩

end NearCubicWires.RuntimeShape
