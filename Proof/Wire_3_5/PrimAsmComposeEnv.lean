import Proof.Wire_3_5.PrimAsmCompose
import Proof.Wire_3_5.PrimAsmCallSize

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.Compose
open NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule

/-! ## The request word below `C_w·2^{⌊n/2⌋}` -/

theorem sq_bound_half {x n : ℕ} (h : x ^ 2 ≤ 2 ^ n) : x ≤ 2 * 2 ^ (n / 2) := by
  by_contra hc'
  have hc : 2 * 2 ^ (n / 2) < x := Nat.lt_of_not_le hc'
  have h1 : (2 * 2 ^ (n / 2)) ^ 2 < x ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
  have h2 : 2 ^ n ≤ (2 * 2 ^ (n / 2)) ^ 2 := by
    rw [mul_pow, ← pow_mul]
    calc 2 ^ n ≤ 2 ^ (n / 2 * 2 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 2 * 2 ^ (n / 2 * 2) := by rw [pow_add, Nat.mul_comm]
  omega

theorem exists_wordConst : ∃ C : ℕ, ∀ n, CallSize.wordBound 26 26 2 n ≤ C * 2 ^ (n / 2) := by
  have hpb := polynomiallyBounded_pow CallSize.wordBound_poly 2
  obtain ⟨onset, hon⟩ := polynomiallyBounded_eventually_le_sixteenth_exponential hpb
  set M := (Finset.range onset).sup (fun n => CallSize.wordBound 26 26 2 n) with hM
  refine ⟨M + 2, fun n => ?_⟩
  have hp : 1 ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  by_cases hn : onset ≤ n
  · have h := hon n hn
    have h16 : 2 ^ (n + 1) / 16 ≤ 2 ^ n := by
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [this]; omega
    have hb := sq_bound_half (le_trans h h16)
    nlinarith
  · have hmem : n ∈ Finset.range onset := Finset.mem_range.mpr (by omega)
    have hle : CallSize.wordBound 26 26 2 n ≤ M := Finset.le_sup (f := fun n => CallSize.wordBound 26 26 2 n) hmem
    nlinarith

/-- The word constant `C_w`. -/
noncomputable def wordConst : ℕ := Classical.choose exists_wordConst

theorem wordConst_spec (n : ℕ) : CallSize.wordBound 26 26 2 n ≤ wordConst * 2 ^ (n / 2) :=
  Classical.choose_spec exists_wordConst n

/-! ## The classes are monotone in the exponents -/

theorem classBound_mono {E E' : Envelope} (h : ClassLE E E') (c : BudgetClass) (q k psi : ℕ) (hq : 1 ≤ q)
    (hc : c ≠ .sourcePoly) : classBound E c q k psi ≤ classBound E' c q k psi := by
  cases c with
  | sourcePoly => exact absurd rfl hc
  | selection =>
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by have := Nat.mul_le_mul_right k h.csel; omega))
      (Nat.pow_le_pow_right hq h.Asel)
  | preprocessing =>
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right psi h.cpsi))
      (Nat.pow_le_pow_right hq h.Apre)
  | table => exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right hq h.Atable)
  | mainPass => exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right hq h.Amain)

/-- The four classes of an envelope at `(q, k, Ψ)`. -/
def classSum (E : Envelope) (q k psi : ℕ) : ℕ :=
  classBound E .selection q k psi + classBound E .preprocessing q k psi + classBound E .table q k psi +
    classBound E .mainPass q k psi

theorem seedClasses_le {E₄ E : Envelope} (h : ClassLE E₄ E) (q k psi : ℕ) (hq : 1 ≤ q) :
    seedClasses E₄ q k psi ≤ 2 * classSum E q k psi := by
  have h1 := classBound_mono h .selection q k psi hq (by decide)
  have h2 := classBound_mono h .preprocessing q k psi hq (by decide)
  have h3 := classBound_mono h .table q k psi hq (by decide)
  unfold seedClasses classSum; omega

theorem finalClasses_le {E₅ E : Envelope} (h : ClassLE E₅ E) (q k psi : ℕ) (hq : 1 ≤ q) :
    finalClasses E₅ q k psi ≤ classSum E q k psi := by
  have h2 := classBound_mono h .preprocessing q k psi hq (by decide)
  have h4 := classBound_mono h .mainPass q k psi hq (by decide)
  unfold finalClasses classSum; omega

theorem half_le_classSum (E : Envelope) (q k psi : ℕ) (hq : 1 ≤ q) : 2 ^ (q / 2) ≤ classSum E q k psi := by
  have h1 : 2 ^ (q / 2) ≤ classBound E .selection q k psi := by
    show 2 ^ (q / 2) ≤ 2 ^ (q / 2 + E.csel * k) * q ^ E.Asel
    have a := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show q / 2 ≤ q / 2 + E.csel * k by omega)
    have b : 0 < q ^ E.Asel := Nat.pow_pos hq
    exact le_trans a (Nat.le_mul_of_pos_right _ b)
  unfold classSum; omega

/-! ## The budget -/

/-- The coefficient rule: `cg c₄ c₅ = glueK·(C_w + 2c₄ + c₅ + 1)`. -/
noncomputable def cgRule (c₄ c₅ : ℕ) : ℕ := glueK * (wordConst + 2 * c₄ + c₅ + 1)

theorem callBudget_eq (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) :
    ((gate0 l F).budget kclk coef A a ha).callBudget n =
      coef * classSum F.E n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n) := by
  show coef * _ + coef * _ + coef * _ + coef * _ = _
  unfold classSum; rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]; rfl

theorem envFor : EnvFor cgRule := by
  intro l F E₄ E₅ c₄ c₅ h4 h5 kclk coef A a ha hc r
  set n := r.1.n with hnd
  set k := ((gate0 l F).budget kclk coef A a ha).kOf n with hkd
  set psi := ((gate0 l F).budget kclk coef A a ha).psiOf n with hpd
  have hq : 1 ≤ n := by
    have h1 : 2 ≤ ((gate0 l F).budget kclk coef A a ha).rOf n := r.2.2.2.2.2.2.1.2.1
    have h2 : 4 * ((gate0 l F).budget kclk coef A a ha).rOf n ≤ n := r.2.2.2.2.2.2.1.2.2.1
    omega
  have hw : r.1.word.length ≤ wordConst * classSum F.E n k psi := by
    have h1 := CallSize.gate_word_length_le l F kclk coef A a ha r.1 r.2
    have h2 := wordConst_spec n
    have h3 := half_le_classSum F.E n k psi hq
    calc r.1.word.length ≤ CallSize.wordBound 26 26 2 n := h1
      _ ≤ wordConst * 2 ^ (n / 2) := h2
      _ ≤ wordConst * classSum F.E n k psi := Nat.mul_le_mul_left _ h3
  have hs4 := seedClasses_le h4 n k psi hq
  have hs5 := finalClasses_le h5 n k psi hq
  have hS : 1 ≤ classSum F.E n k psi := le_trans Nat.one_le_two_pow (half_le_classSum F.E n k psi hq)
  rw [callBudget_eq]
  have hb4 : c₄ * seedClasses E₄ n k psi ≤ 2 * c₄ * classSum F.E n k psi := by
    have := Nat.mul_le_mul_left c₄ hs4; nlinarith
  have hb5 : c₅ * finalClasses E₅ n k psi ≤ c₅ * classSum F.E n k psi := Nat.mul_le_mul_left c₅ hs5
  have hcoef : cgRule c₄ c₅ * classSum F.E n k psi ≤ coef * classSum F.E n k psi := Nat.mul_le_mul_right _ hc
  unfold cgRule at hcoef
  nlinarith

/-- **The residual `EnvPack`** of the compose plan. -/
noncomputable def envPack : EnvPack := ⟨cgRule, envFor⟩

end NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv
