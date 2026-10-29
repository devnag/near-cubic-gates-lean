import SourceAdapters.ShortPCP.RAMBH
import SourceAdapters.ShortPCP.ClockParams

/-!
# `lem:tm-ram`'s constants for the clock parameters (P02, discharge of `MnFits`)

Paper anchor: `lem:tm-ram` (`lem:tm-ram` and its proof) fixes `w_n`, `x̄` and `T_n`; its proof, "Constants" (`lem:tm-ram` and its proof):
"A suitable constant `c_V ≥ 16` ensures three things. The simulation and the recording of the verdict end within
`T_n − 16` steps. `|x̄| ≤ 2(n+1) + 2w_n ≤ T_n`. `2^{w_n} ≥ 2^{c_V} T(n)` is larger than `T_n` and every address."

Here `T(n)` is the supplied clock `t` (`cor:short-pcp-clock`), `w_n = wordWidth c t`, `T_n = 2^{timeExp c t}`, and
`x̄ = x 1 0^j` of length `inputPadLength c n t`. The constant is `clockConst V`; every `c ≥ clockConst V` works.

- `mnFits_clock`: the side conditions `MnFits` of `mn_bhram_iff` (the three bullets above, in the exact form the
  RAM simulation uses: code length, register addresses, head addresses, the step budget, the witness words);
- `padInput`, `padInput_facts`: `x̄` and the facts `mn_bhram_iff` needs about it;
- `mn_bhram_clock`: `mn_bhram_iff` at these parameters.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-- **`c_V`** (`lem:tm-ram` and its proof): a constant depending only on `V`. -/
def clockConst (V : Verifier) : ℕ := 64 + codeLen V + 8 * V.tapeCount + simLen V + accLen V

/-- `c(4c² + 14c + 2) ≤ 2^c` for `c ≥ 16`. -/
theorem cubic_le_two_pow (c : ℕ) (hc : 16 ≤ c) : c * (4 * c ^ 2 + 14 * c + 2) ≤ 2 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
    have h : (c + 1) * (4 * (c + 1) ^ 2 + 14 * (c + 1) + 2) ≤ 2 * (c * (4 * c ^ 2 + 14 * c + 2)) := by
      have h1 : 16 * c ^ 2 ≤ c ^ 3 := by
        rw [pow_succ c 2, Nat.mul_comm (c ^ 2) c]; exact Nat.mul_le_mul_right _ hc
      have h2 : 16 * c ≤ c ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hc
      ring_nf
      omega
    calc (c + 1) * (4 * (c + 1) ^ 2 + 14 * (c + 1) + 2) ≤ 2 * (c * (4 * c ^ 2 + 14 * c + 2)) := h
      _ ≤ 2 * 2 ^ c := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (c + 1) := by rw [pow_succ, Nat.mul_comm]

theorem clockConst_facts (V : Verifier) (c : ℕ) (hc : clockConst V ≤ c) :
    16 ≤ c ∧ codeLen V ≤ c ∧ stride V ≤ c ∧ V.tapeCount ≤ stride V ∧ 1 ≤ stride V ∧
      48 + simLen V ≤ c ∧ 8 * V.tapeCount + 56 + accLen V ≤ c := by
  have h2 := V.twoTapes
  unfold clockConst at hc
  unfold stride
  omega

/-- "`2^{w_n} ≥ 2^{c_V} T(n)` is larger than … every address": `stride·(4c² + 14c + 2)·t ≤ 2^{w_n}`. -/
theorem stride_poly_le (V : Verifier) (c t : ℕ) (hc : clockConst V ≤ c) (ht : 1 ≤ t) :
    stride V * (4 * c ^ 2 + 14 * c + 2) * t ≤ 2 ^ wordWidth c t := by
  obtain ⟨h16, -, hS, -⟩ := clockConst_facts V c hc
  have h1 := cubic_le_two_pow c h16
  have h2 : stride V * (4 * c ^ 2 + 14 * c + 2) ≤ 2 ^ c :=
    (Nat.mul_le_mul_right _ hS).trans h1
  exact (Nat.mul_le_mul_right t h2).trans (two_pow_wordWidth c t h16 ht).1

/-- **The side conditions of `mn_bhram_iff`** at `w = w_n`, `τ = log T_n` (`lem:tm-ram` and its proof). -/
theorem mnFits_clock (V : Verifier) (c n t : ℕ) (hc : clockConst V ≤ c) (hnt : n ≤ t) (ht : 1 ≤ t) :
    MnFits V (wordWidth c t) n t (timeExp c t) := by
  obtain ⟨h16, hcl, hS, hkS, hS1, hsim, hacc⟩ := clockConst_facts V c hc
  have hw := wordWidth_ge c t
  have hpw := two_pow_wordWidth c t h16 ht
  have hsp := stride_poly_le V c t hc ht
  have hshape := padTime_shape c t h16 ht
  have hTge := padTime_ge c t
  have hTle := padTime_le_linear c t (by omega) ht
  have hcpow : c < 2 ^ c := Nat.lt_two_pow_self
  have hct : 2 ^ c ≤ 2 ^ c * t := Nat.le_mul_of_pos_right _ ht
  have hcode : codeLen V < 2 ^ wordWidth c t := by omega
  have hadd : stride V * (2 * t) + 1 < 2 ^ wordWidth c t := by
    have h1 : 2 ≤ stride V * (4 * c ^ 2 + 14 * c) := by nlinarith
    have h2 : 2 * t ≤ stride V * (4 * c ^ 2 + 14 * c) * t := Nat.mul_le_mul_right _ h1
    have h3 : stride V * (4 * c ^ 2 + 14 * c + 2) * t =
        stride V * (4 * c ^ 2 + 14 * c) * t + stride V * (2 * t) := by ring
    omega
  have htw : t < 2 ^ wordWidth c t := by
    have : t < 2 ^ c * t := by nlinarith
    omega
  have hA : stride V * (2 * n) + 0 < 2 ^ wordWidth c t := by
    have : stride V * (2 * n) ≤ stride V * (2 * t) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨by omega, hcode, ⟨by omega, hcode, by omega, htw, hA, hadd⟩, by omega,
    by unfold padTime at hshape; exact hshape.1, by unfold padTime at hshape; exact hshape.2.1,
    by have := hpw.2; unfold padTime at this; exact this, ?_, ?_, ?_⟩
  · -- heads: `stride (T_n + 1) + k ≤ stride·(4c²+14c+2)·t ≤ 2^{w_n}`
    have hT : 2 ^ timeExp c t ≤ (4 * c ^ 2 + 14 * c) * t := by
      have : 2 * c * (7 + 2 * c) = 4 * c ^ 2 + 14 * c := by ring
      unfold padTime at hTle; rw [this] at hTle; exact hTle
    have h1 : stride V * (2 ^ timeExp c t + 1) ≤ stride V * ((4 * c ^ 2 + 14 * c) * t) + stride V :=
      by rw [Nat.mul_add, Nat.mul_one]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hT) _
    have h2 : stride V + V.tapeCount ≤ stride V * 2 * t := by
      have : stride V * 2 ≤ stride V * 2 * t := Nat.le_mul_of_pos_right _ ht
      omega
    have h3 : stride V * (4 * c ^ 2 + 14 * c + 2) * t =
        stride V * ((4 * c ^ 2 + 14 * c) * t) + stride V * 2 * t := by ring
    omega
  · -- the step budget: `initLen + t·simLen + accLen + 16 ≤ c(t + w_n) ≤ T_n`
    have hcw : c * t + c ≤ c * (t + wordWidth c t) := by
      rw [Nat.mul_add]; exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _
    have hct' : (48 + simLen V) * t ≤ c * t := Nat.mul_le_mul_right _ hsim
    have e : (48 + simLen V) * t = 48 * t + t * simLen V := by ring
    unfold initLen
    unfold padTime at hTge
    omega
  · -- the witness words: `⌈t/w⌉·w ≤ t + w ≤ T_n`
    have h1 : (t + wordWidth c t - 1) / wordWidth c t * wordWidth c t ≤ t + wordWidth c t - 1 :=
      Nat.div_mul_le_self _ _
    have h2 : t + wordWidth c t ≤ c * (t + wordWidth c t) := Nat.le_mul_of_pos_left _ (by omega)
    unfold padTime at hTge
    omega

/-! ## The padded input `x̄` -/

/-- **`x̄ = x 1 0^j`** of length `2^{⌈lg max(n+1, w_n)⌉}` (`lem:tm-ram`, `lem:tm-ram` and its proof). -/
def padInput (c t : ℕ) {n : ℕ} (x : BitInput n) : List Bool :=
  List.ofFn x ++ true :: List.replicate (inputPadLength c n t - n - 1) false

theorem padInput_length (c t : ℕ) {n : ℕ} (x : BitInput n) (h : n + 1 ≤ inputPadLength c n t) :
    (padInput c t x).length = inputPadLength c n t := by
  simp [padInput]; omega

theorem padInput_getD (c t : ℕ) {n : ℕ} (x : BitInput n) (p : ℕ) (hp : p < n) :
    (padInput c t x).getD p false = x ⟨p, hp⟩ := by
  rw [padInput, List.getD_append _ _ _ _ (by simpa using hp), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hp]

/-- The facts about `x̄` used by `mn_bhram_iff`: room for the `⌈n/w_n⌉` words `M_n` reads,
`|x̄| < T_n` (strictly: `|x̄| < 2·max(n+1, w_n) ≤ 2(n+1) + 2w_n ≤ T_n`), `2 ≤ |x̄|`, and `|x̄| = 2^m`. -/
theorem padInput_facts (V : Verifier) (c n t : ℕ) (hc : clockConst V ≤ c) (hn : 1 ≤ n) (hnt : n ≤ t)
    (x : BitInput n) :
    (n + wordWidth c t - 1) / wordWidth c t * wordWidth c t ≤ (padInput c t x).length ∧
      (padInput c t x).length < 2 ^ timeExp c t ∧ 2 ≤ (padInput c t x).length ∧
      (padInput c t x).length = 2 ^ Nat.log 2 (padInput c t x).length := by
  obtain ⟨h16, -⟩ := clockConst_facts V c hc
  obtain ⟨h1, hdvd, h3, h4⟩ := inputPad_facts c n t h16 hn hnt
  have hlt := two_pow_clog_lt (max (n + 1) (wordWidth c t)) (by omega)
  have hlen := padInput_length c t x h1
  obtain ⟨-, h2, -, h5⟩ := instance_side_conditions c n t h16 hn hnt
  have hw : 0 < wordWidth c t := by have := wordWidth_ge c t; omega
  refine ⟨?_, ?_, by omega, by rw [hlen]; exact h5⟩
  · rw [hlen]
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, Nat.mul_comm (wordWidth c t) q]
    apply Nat.mul_le_mul_right
    have hnq : n ≤ wordWidth c t * q := by rw [← hq]; omega
    have : (n + wordWidth c t - 1) / wordWidth c t < q + 1 := by
      rw [Nat.div_lt_iff_lt_mul hw, Nat.add_mul, one_mul, Nat.mul_comm q]
      omega
    omega
  · rw [hlen]
    have : inputPadLength c n t < 2 * max (n + 1) (wordWidth c t) := hlt
    unfold padTime at h4
    have : 2 * max (n + 1) (wordWidth c t) ≤ 2 * (n + 1) + 2 * wordWidth c t := by omega
    omega

theorem clock_fit (V : Verifier) (c t : ℕ) (hc : clockConst V ≤ c) (ht : 1 ≤ t) :
    codeLen V ≤ 2 ^ wordWidth c t :=
  (mnFits_clock V c 0 t hc (by omega) ht).code.le

/-- **`lem:tm-ram` + Step 1 of `thm:short-pcp-ours` at the clock parameters** (`lem:tm-ram` and its proof): for `c ≥ c_V`, `1 ≤ n ≤ t`, under the promise that `V` halts within `t` steps on every witness, `V`
accepts `x` with some `t`-bit witness iff `(x̄, 1^{log T_n}, 1^{log T_n}) ∈ BH_RAM(M_n)`. -/
theorem mn_bhram_clock (V : Verifier) (c n t : ℕ) (hc : clockConst V ≤ c) (hn : 1 ≤ n) (hnt : n ≤ t)
    (x : BitInput n)
    (hrun : ∀ y : List Bool, ∃ receipt, run V.machine t (V.inputTapes (List.ofFn x) y) = some receipt) :
    (∃ y : BitInput t, V.accepts (List.ofFn x) (List.ofFn y)) ↔
      (mnRam V (wordWidth c t) n t (2 ^ timeExp c t) (clock_fit V c t hc (by omega))).BHRAM
        (padInput c t x) (timeExp c t) (timeExp c t) := by
  obtain ⟨hxlen, hxT, -, -⟩ := padInput_facts V c n t hc hn hnt x
  exact mn_bhram_iff V (wordWidth c t) n t (timeExp c t) _ (mnFits_clock V c n t hc hnt (by omega)) x
    (padInput c t x) (padInput_getD c t x) hxlen hxT.le hrun

end NearCubicGates.Adapters.ShortPCP
