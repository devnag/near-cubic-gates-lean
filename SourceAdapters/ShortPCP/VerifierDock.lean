import SourceAdapters.Joins.AmplifiedVerifier
import SourceAdapters.Joins.SingleRunTime
import SourceAdapters.Joins.AffineConstraint
import SourceAdapters.ACSP.AffineDegree

/-!
# The single-run verifier on an affine constraint instance: the facts of `Good`, and its two neighbors

For an instance `(c, x̄)` satisfying `SingleRun.Good` (the instances of Step 1 of the proof of
`thm:short-pcp-ours`):
- the derived facts the verifier uses: the field has `2^f` elements (`modOk`), `irr` is irreducible, `c_N ≥ 1`, the
  neighbors `a_ν X + b_ν` have `a_ν ≠ 0`, `m_H < f`, `2 ≤ f`, and the bound on every composition `B_A` by `d_H`
  (the paragraph after `def:acsp` through `Instance.degB_of_isValid`, with Step 2: "it bounds the degree `d_B` …,
  since `4 d_B ≤ 2^f`");
- the reduction of Step 1 (`Joins.AffineConstraintReduction`) gives `Good` on every request with `2 ≤ n ≤ t`
  (`good_of_reduction`);
- the request is valid for the time join `Joins.SingleRunTime` (`Good.valid_request`), and its program outputs
  exactly `V0` (masks `[[]]`) and `V1` (masks `S` of Step 3) as the two verifier joins define them
  (`time_runs_v0`, `time_runs_v1`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Verifier

open Polynomial NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairSource
open NearCubicWires.LocalBitMultitape
open NearCubicGates.Adapters.ACSP.Affine NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.Joins.SingleRun NearCubicGates.Adapters.Joins.SingleRun.Amplified

variable {Kc : ℕ} {c : Instance} {xs : List Bool}

namespace Good

variable (hG : SingleRun.Good Kc c xs)
include hG

/-- "`F = F₂[X]/(irr)`, the field with `2^f` elements": the modulus has degree exactly `f`. -/
theorem modOk : GF.ModulusOk c.irr c.f := ⟨hG.wellFormed.1, hG.wellFormed.2.1⟩

/-- `def:acsp`: "an irreducible `irr` of degree `f`". -/
theorem irr : Irreducible c.irrPoly := hG.valid.1.1

/-- `def:acsp`: "for `1 ≤ ν ≤ c_N` and some `c_N ≥ 1`". -/
theorem cN_pos : 1 ≤ c.cN := hG.valid.2.2.1.1

/-- `def:acsp`: "neighbors `N_ν(X) = a_ν X + b_ν` with `a_ν ≠ 0`", read at every index below `c_N`. -/
theorem slope_ne (ν : ℕ) (hν : ν < c.cN) : c.slope ν ≠ 0 := by
  have hmem : c.nbr.getD ν (0, 0) ∈ c.nbr := by
    rw [List.getD_eq_getElem _ _ hν]; exact List.getElem_mem hν
  exact hG.valid.2.2.1.2 _ hmem

theorem mH_lt : c.mH < c.f := by have := hG.mH_two_le; omega

theorem two_le_f : 2 ≤ c.f := by have := hG.mH_two_le; have := hG.one_le_m; have := hG.m_lt; omega

/-- The paragraph after `def:acsp` (`Instance.degB_of_isValid`): one `d_B` with `4 d_B ≤ 2^f` bounds every
composition `B_A` with `deg A < 2^{m_H}`. -/
theorem degB : ∃ dB : ℕ, dB * 4 ≤ 2 ^ c.f ∧ ∀ A : c.Fld[X], A.degree < ((2 ^ c.mH : ℕ) : WithBot ℕ) →
    (c.composed A).natDegree ≤ dB :=
  c.degB_of_isValid hG.valid

/-- Step 2: "The test of `p_1` uses the degree bound `d_H = 2^{f−2}` …; it bounds the degree `d_B` …, since
`4 d_B ≤ 2^f`." -/
theorem composed_le_dH (A : c.Fld[X]) (hA : A.degree < ((2 ^ c.mH : ℕ) : WithBot ℕ)) :
    (c.composed A).natDegree ≤ dH c := by
  obtain ⟨dB, h4, hB⟩ := degB hG
  have hf := two_le_f hG
  have hpow : 2 ^ c.f = 4 * 2 ^ (c.f - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  exact (hB A hA).trans (by unfold dH; omega)

/-- `d_H < 2^f` and `2 d_H ≤ 2^f` (Step 2: "and it is less than `2^f`"). -/
theorem dH_lt : dH c < 2 ^ c.f ∧ 2 * dH c ≤ 2 ^ c.f := by
  have hf := two_le_f hG
  have hpow : 2 ^ c.f = 4 * 2 ^ (c.f - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ (c.f - 2) := Nat.one_le_two_pow
  unfold dH; omega

/-- "it must be that `d ≥ |H|`" for the test of `p_1` (`2^{m_H} ≤ d_H`, from `m_H + 2 ≤ f`). -/
theorem two_pow_mH_le_dH : 2 ^ c.mH ≤ dH c := Nat.pow_le_pow_right (by norm_num) (by have := hG.mH_two_le; omega)

/-- The request is valid for the time join (`Request.Valid`). -/
theorem valid_request (S : List (List Bool)) : (request c xs S).Valid :=
  ⟨hG.wellFormed, hG.valid, hG.xbar_len, hG.one_le_m⟩

end Good

/-! ## Step 1 gives `Good` -/

/-- **From the reduction of Step 1**: on every request with `2 ≤ n ≤ t`, the instance and padded input of
`Joins.AffineConstraintReduction` satisfy `Good` with its constant `K`, and the equivalence of Step 1 holds. -/
theorem good_of_reduction (V : OrdinaryVerifier) (hS : AffineConstraintReduction V) :
    ∃ (inst : ClockRequest → Instance) (xbar : ClockRequest → List Bool) (K : ℕ),
      ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
        SingleRun.Good K (inst r) (xbar r) ∧
        (RunsWithin V r.1.2 r.2 →
          ((∃ y : BitInput r.2, V.accepts (List.ofFn r.1.2) (List.ofFn y)) ↔ (inst r).Accepts (xbar r))) := by
  obtain ⟨inst, xbar, K, e, hr, -⟩ := hS
  refine ⟨inst, xbar, K, fun r h2 hnt => ?_⟩
  obtain ⟨hEq, hV, hW, -, hlen, h1m, hmlt, hmH, -, -, hcN, -⟩ := hr r h2 hnt
  exact ⟨⟨hW, hV, hlen, h1m, hmlt, hmH, hcN⟩, hEq⟩

/-! ## The time join computes `V0` and `V1` -/

theorem accepts_eq (hG : SingleRun.Good Kc c xs) (π : ℕ → Bool) (R : List Bool) :
    haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
    letI : DecidableEq c.Fld := Classical.decEq _
    SingleRun.accepts c xs π R =
      (request c xs [[]]).runVerdict (RingHom.id c.Fld) ((request c xs [[]]).decode (RingHom.id c.Fld) π)
        (fun i => R.getD i false) := by
  rw [SingleRun.accepts, dif_pos (Good.irr hG)]

theorem amplified_eq (hG : SingleRun.Good Kc c xs) (n K1 b1 : ℕ) (π : ℕ → Bool) (R : List Bool) :
    haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
    letI : DecidableEq c.Fld := Classical.decEq _
    Amplified.accepts c xs n K1 b1 π R =
      (request c xs (masks c n K1 b1)).patchedVerdict (RingHom.id c.Fld)
        ((request c xs (masks c n K1 b1)).decode (RingHom.id c.Fld) π) R := by
  rw [Amplified.accepts, dif_pos (Good.irr hG)]

/-- The patched verdict with the single empty mask is `V0`. -/
theorem patched_single (hG : SingleRun.Good Kc c xs) (π : ℕ → Bool) (R : List Bool) :
    haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
    letI : DecidableEq c.Fld := Classical.decEq _
    (request c xs [[]]).patchedVerdict (RingHom.id c.Fld) ((request c xs [[]]).decode (RingHom.id c.Fld) π) R =
      SingleRun.accepts c xs π R := by
  rw [accepts_eq hG]
  unfold Request.patchedVerdict
  show ([[]] : List (List Bool)).all (fun σ => _) = _
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  congr 1
  funext i
  simp [Request.maskedCoins]

/-- **The time join runs `V1`** (and `V0`): on every instance satisfying `Good`, the program of
`Joins.SingleRunTime` on the request with the masks `S` of Step 3 outputs `[V1(π, R)]` within its fuel, and
every halting run outputs that verdict. -/
theorem time_runs_v1 (hT : SingleRunTime) :
    ∃ (prog : OrdinaryOracleProgram) (K e : ℕ), ∀ (Kc : ℕ) (c : Instance) (xs : List Bool),
      SingleRun.Good Kc c xs → ∀ (n K1 b1 : ℕ) (o : ℕ → Bool) (R : List Bool),
        OrdinaryOracleRuns o prog ((request c xs (masks c n K1 b1)).input R) [Amplified.accepts c xs n K1 b1 o R]
          (K * ((request c xs (masks c n K1 b1)).data.length + R.length + 1) ^ e) ∧
        ∀ (out : List Bool) (budget : ℕ), OrdinaryOracleRuns o prog ((request c xs (masks c n K1 b1)).input R) out
          budget → out = [Amplified.accepts c xs n K1 b1 o R] := by
  obtain ⟨prog, K, e, ht⟩ := hT
  refine ⟨prog, K, e, fun Kc c xs hG n K1 b1 o R => ?_⟩
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  rw [amplified_eq hG]
  exact ht _ (Good.valid_request hG _) c.Fld (RingHom.id c.Fld) Function.bijective_id o R

theorem time_runs_v0 (hT : SingleRunTime) :
    ∃ (prog : OrdinaryOracleProgram) (K e : ℕ), ∀ (Kc : ℕ) (c : Instance) (xs : List Bool),
      SingleRun.Good Kc c xs → ∀ (o : ℕ → Bool) (R : List Bool),
        OrdinaryOracleRuns o prog ((request c xs [[]]).input R) [SingleRun.accepts c xs o R]
          (K * ((request c xs [[]]).data.length + R.length + 1) ^ e) ∧
        ∀ (out : List Bool) (budget : ℕ), OrdinaryOracleRuns o prog ((request c xs [[]]).input R) out budget →
          out = [SingleRun.accepts c xs o R] := by
  obtain ⟨prog, K, e, ht⟩ := hT
  refine ⟨prog, K, e, fun Kc c xs hG o R => ?_⟩
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  rw [← patched_single hG]
  exact ht _ (Good.valid_request hG _) c.Fld (RingHom.id c.Fld) Function.bijective_id o R

end NearCubicGates.Adapters.ShortPCP.Verifier
