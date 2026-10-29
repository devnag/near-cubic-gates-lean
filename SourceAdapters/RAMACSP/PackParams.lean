import SourceAdapters.ShortPCP.ClockFits

/-!
# The parameters of the affine constraint instance (route B)

Paper context and implementation details:, `app:event-trace` Setting (the RAM `M_n` of `lem:tm-ram`, the
word width `w = 2^ω`, the time exponent `τ`, `T = 2^τ`, `N = 2T`, `k_N = τ + 1`), `app:affine-embedding` Complete field catalog
(`Ftags = 32 + 3K + 2L`, `d = ⌈log₂ Ftags⌉`, `C = 2^d·w`, `q = d + ω`, `ℓ = ⌈lg 2k_N⌉`,
`mH = k_N + ℓ + ω + d + 4`), `lem:acsp-degree` Choice of `f` (`f := mH + ⌈log₂(4(mH + 4))⌉`, so `4·dB ≤ 2^f` with
`dB = (mH + 4)·2^{mH}`, `mH + 2 ≤ f` and `2^f < 8(mH + 4)·2^{mH}`), and `lem:generator` (G1)–(G2) (the generator computes exactly
these numbers from `(x, t)`).

Every number is a total function of the verifier `V` (through its constants `c_V = clockConst V`, `K = regCount V`,
`L = codeLen V`) and of the clock request; nothing here depends on the promise.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.ShortPCP
open NearCubicWires NearCubicWires.RepairOrdinary

variable (V : Verifier)

/-! ## `app:event-trace`: the RAM parameters -/

/-- `ω` with `w = 2^ω` (`app:event-trace` Setting; `wordWidth c t = 2^{⌈lg(⌈lg t⌉ + c)⌉}`). -/
def wordExp (t : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 t + clockConst V)

/-- `w = w_n` (`app:event-trace`). -/
def wordW (t : ℕ) : ℕ := wordWidth (clockConst V) t

/-- `τ` with `T = T_n = 2^τ` (`app:event-trace`). -/
def tau (t : ℕ) : ℕ := timeExp (clockConst V) t

/-- `k_N = τ + 1`, the lane exponent: `N = 2T = 2^{k_N}` lanes (`app:event-trace`, `app:affine-embedding`). -/
def laneExp (t : ℕ) : ℕ := tau V t + 1

/-- `ℓ = ⌈lg 2k_N⌉`, the stage-tag exponent: `S = 2^ℓ ≥ 2k_N` (`app:affine-embedding`). -/
def stageExp (t : ℕ) : ℕ := Nat.clog 2 (2 * laneExp V t)

/-- `Ftags = 32 + 3K + 2L` field/template tags (`app:affine-embedding` Complete field catalog; `K` registers, `L` code length). -/
def ftags : ℕ := 32 + 3 * regCount V + 2 * codeLen V

/-- `d = ⌈log₂ Ftags⌉` (`app:affine-embedding`). -/
def tagExp : ℕ := Nat.clog 2 (ftags V)

/-- `q = d + ω`, the column exponent: `C = 2^q = 2^d·w` columns (`app:affine-embedding`). -/
def colExp (t : ℕ) : ℕ := tagExp V + wordExp V t

/-- `mH = k_N + ℓ + q + 4` = `k_N + ℓ + ω + d + 4` (`app:affine-embedding`; three role bits and one area bit). -/
def domExp (t : ℕ) : ℕ := laneExp V t + stageExp V t + colExp V t + 4

/-- **`f := mH + ⌈log₂(4(mH + 4))⌉`** (`lem:acsp-degree` Choice of `f`). -/
def fieldExp (t : ℕ) : ℕ := domExp V t + Nat.clog 2 (4 * (domExp V t + 4))

/-! ## Facts -/

theorem wordW_eq (t : ℕ) : wordW V t = 2 ^ wordExp V t := rfl

/-- The code of `M_n` fits for every `t` (`L ≤ 2^w`, `app:event-trace`; total version of `clock_fit`). -/
theorem codeLen_le_two_pow_wordW (t : ℕ) : codeLen V ≤ 2 ^ wordW V t := by
  obtain ⟨-, hcl, -⟩ := clockConst_facts V (clockConst V) le_rfl
  have h1 := wordWidth_ge (clockConst V) t
  have h2 : wordWidth (clockConst V) t < 2 ^ wordWidth (clockConst V) t := Nat.lt_two_pow_self
  unfold wordW
  omega

/-- `16 ≤ c_V` (P02). -/
theorem sixteen_le_clockConst : 16 ≤ clockConst V := (clockConst_facts V (clockConst V) le_rfl).1

/-- `T < 2^w`, i.e. `τ < w` (`app:event-trace` Throughout: `T < 2^w`; P02 `two_pow_wordWidth`). -/
theorem tau_lt_wordW (t : ℕ) (ht : 1 ≤ t) : tau V t < wordW V t := by
  have h := (two_pow_wordWidth (clockConst V) t (sixteen_le_clockConst V) ht).2
  unfold padTime at h
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h

/-- `ω ≤ τ` (`app:event-trace` Throughout): `w ≤ c(t + w) ≤ T`. -/
theorem wordExp_le_tau (t : ℕ) : wordExp V t ≤ tau V t := by
  have h1 := padTime_ge (clockConst V) t
  have h16 := sixteen_le_clockConst V
  have h2 : wordWidth (clockConst V) t ≤ clockConst V * (t + wordWidth (clockConst V) t) := by
    nlinarith
  have h3 : 2 ^ wordExp V t ≤ 2 ^ tau V t := by
    have e1 : 2 ^ wordExp V t = wordWidth (clockConst V) t := rfl
    have e2 : 2 ^ tau V t = padTime (clockConst V) t := rfl
    rw [e1, e2]; exact h2.trans h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

/-- `2k_N ≤ 2^ℓ` (`app:affine-embedding`: `S ≥ 2k_N`). -/
theorem two_laneExp_le (t : ℕ) : 2 * laneExp V t ≤ 2 ^ stageExp V t := Nat.le_pow_clog (by norm_num) _

/-- `1 ≤ Ftags ≤ 2^d`. -/
theorem ftags_le : ftags V ≤ 2 ^ tagExp V := Nat.le_pow_clog (by norm_num) _

/-- The concrete layout satisfies `τ < k_N < mH`, so in particular `τ < mH`
(the layout in `app:affine-embedding`). -/
theorem tau_lt_domExp (t : ℕ) : tau V t < domExp V t := by
  unfold domExp laneExp; omega

/-- **C5 [J2, M1]** (`lem:acsp-degree`, `def:acsp`): `mH + 2 ≤ f` (indeed `f ≥ mH + 4`). -/
theorem domExp_add_two_le_fieldExp (t : ℕ) : domExp V t + 2 ≤ fieldExp V t := by
  unfold fieldExp
  have : 1 < Nat.clog 2 (4 * (domExp V t + 4)) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by rw [pow_one]; omega)
  omega

/-- The degree budget `dB = (mH + 4)·2^{mH}` of `lem:acsp-degree` (`wdeg P ≤ mH·|H|/2 + 2(|H| − 1) ≤ dB`). -/
def degreeBudget (t : ℕ) : ℕ := (domExp V t + 4) * 2 ^ domExp V t

/-- **`4·dB ≤ 2^f`** (`lem:acsp-degree`: Valid's degree constraint and J4 with this `dB`). -/
theorem four_degreeBudget_le (t : ℕ) : 4 * degreeBudget V t ≤ 2 ^ fieldExp V t := by
  unfold degreeBudget fieldExp
  rw [pow_add]
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (4 * (domExp V t + 4))
  calc 4 * ((domExp V t + 4) * 2 ^ domExp V t) = 2 ^ domExp V t * (4 * (domExp V t + 4)) := by ring
    _ ≤ 2 ^ domExp V t * 2 ^ Nat.clog 2 (4 * (domExp V t + 4)) := Nat.mul_le_mul_left _ h

/-- **`2^f < 8(mH + 4)·2^{mH}`** (`lem:acsp-degree` Choice of `f`). -/
theorem two_pow_fieldExp_lt (t : ℕ) : 2 ^ fieldExp V t < 8 * (domExp V t + 4) * 2 ^ domExp V t := by
  unfold fieldExp
  rw [pow_add]
  have h := two_pow_clog_lt (4 * (domExp V t + 4)) (by omega)
  have hp : 0 < 2 ^ domExp V t := Nat.two_pow_pos _
  calc 2 ^ domExp V t * 2 ^ Nat.clog 2 (4 * (domExp V t + 4))
      < 2 ^ domExp V t * (2 * (4 * (domExp V t + 4))) := Nat.mul_lt_mul_of_pos_left h hp
    _ = 8 * (domExp V t + 4) * 2 ^ domExp V t := by ring

end NearCubicGates.Adapters.RAMACSP
