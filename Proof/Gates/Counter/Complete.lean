import Proof.Gates.Counter.Sound
import Proof.Gates.Counter.Window
import Proof.Gates.Counter.Pure
import Proof.Gates.Counter.SamplingBernstein
import Proof.Foundations.ThresholdDAGCompilation

/-!
# Counter module 8/9 — prop:complete: the bridge to the sampling supply and the completeness theorem
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires
open NearCubicGates.Close.Counter.Sampling.WitnessContract

/-! ## Normalized circuits as weighted symmetric circuits -/

/-- A well-formed normalized circuit as a circuit of the class `𝒲` (bottom gates indexed by coefficient position). -/
noncomputable def toWSC {n : ℕ} (C : NCircuit n) (h : C.gates.length = C.coeffs.length)
    (hnz : ∀ a ∈ C.coeffs, a ≠ 0) : Target.WeightedSymmetricCircuit n where
  bottomCount := C.coeffs.length
  bottom i := ThresholdDAGSimulation.normalizedAsRealGate (C.gates[i.val]'(by rw [h]; exact i.isLt))
  coefficient i := C.coeffs[i.val]
  coefficient_ne_zero i := hnz _ (List.getElem_mem _)
  lookup := topLookup C

theorem linForm_eq_sum {n : ℕ} (gates : List (NormalizedThresholdGate n)) (a : List ℤ)
    (h : gates.length = a.length) (z : BitInput n) :
    linForm gates a z = ∑ i : Fin a.length, a[i.val] *
      (if (gates[i.val]'(by rw [h]; exact i.isLt)).eval z then 1 else 0) := by
  rw [← List.sum_ofFn]
  unfold linForm
  congr 1
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]

theorem toWSC_score {n : ℕ} (C : NCircuit n) (h : C.gates.length = C.coeffs.length)
    (hnz : ∀ a ∈ C.coeffs, a ≠ 0) (z : BitInput n) : (toWSC C h hnz).score z = C.score z := by
  rw [score_eq_linForm, linForm_eq_sum C.gates C.coeffs h]
  unfold Target.WeightedSymmetricCircuit.score toWSC
  simp only [ThresholdDAGSimulation.normalizedAsRealGate_eval]

theorem sum_fin_natAbs (a : List ℤ) : (∑ i : Fin a.length, (a[i.val]).natAbs) = (a.map Int.natAbs).sum := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]

theorem toWSC_topWeight {n : ℕ} (C : NCircuit n) (h : C.gates.length = C.coeffs.length)
    (hnz : ∀ a ∈ C.coeffs, a ≠ 0) : (toWSC C h hnz).topWeight = C.topWeight := by
  unfold Target.WeightedSymmetricCircuit.topWeight toWSC NCircuit.topWeight
  exact sum_fin_natAbs C.coeffs

theorem toWSC_bottom_eval {n : ℕ} (C : NCircuit n) (h : C.gates.length = C.coeffs.length)
    (hnz : ∀ a ∈ C.coeffs, a ≠ 0) (i : Fin (toWSC C h hnz).bottomCount) (z : BitInput n) :
    ((toWSC C h hnz).bottom i).eval z = (C.gates[i.val]'(by rw [h]; exact i.isLt)).eval z :=
  ThresholdDAGSimulation.normalizedAsRealGate_eval _ z

section Call

variable {B1 B2 : ℕ} (c : Call) (hadm : c.Admitted B1 B2)

/-- The two roles of a call as circuits of `𝒲`; the second is empty unless the call is a pair call. -/
noncomputable def circuitsOf : Fin 2 → Target.WeightedSymmetricCircuit c.n :=
  ![toWSC c.first hadm.2.1.1 hadm.2.1.2.1, toWSC c.second hadm.2.2.1.1 hadm.2.2.1.2.1]

theorem circuitsOf_zero : circuitsOf c hadm 0 = toWSC c.first hadm.2.1.1 hadm.2.1.2.1 := rfl
theorem circuitsOf_one : circuitsOf c hadm 1 = toWSC c.second hadm.2.2.1.1 hadm.2.2.1.2.1 := rfl

theorem totalWeight_circuitsOf : totalWeight (circuitsOf c hadm) = c.W := by
  simp only [totalWeight, Fin.sum_univ_two, circuitsOf_zero, circuitsOf_one, toWSC_topWeight, Call.W]

/-- The role `r` of `circuitsOf` is `circ c r` for `r ∈ {0, 1}`. -/
theorem circuitsOf_score (r : Fin 2) (z : BitInput c.n) :
    (circuitsOf c hadm r).score z = (circ c r.val).score z := by
  fin_cases r
  · simp [circuitsOf_zero, toWSC_score, circ]
  · simp [circuitsOf_one, toWSC_score, circ]

theorem circuitsOf_bottomCount (r : Fin 2) : (circuitsOf c hadm r).bottomCount = (circ c r.val).coeffs.length := by
  fin_cases r <;> rfl

end Call

/-! ## The public record -/

/-- The Sampling public record of a call with selected parameters (`Jlean = J − 1`). -/
def publicData (c : Call) (p : Params) (B1 cT : ℕ) : PublicData c.n :=
  { beta := c.radius, precisionExponent := B1, cT := cT, T := p.T, P := p.P, Lw := p.Lw, Jlean := p.J - 1 }

section PD

variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (hadm : c.Admitted B1 B2) (hs : Spec cT (header c) p)
include hs

theorem pd_k : (publicData c p B1 cT).k = p.k := by
  rw [hs.k_eq]; simp [PublicData.k, PublicData.Jmax, publicData, inner, Jmax, header]

theorem pd_hE : (publicData c p B1 cT).hE = p.hE := by
  rw [hs.hE_eq]; rfl

theorem pd_h : (publicData c p B1 cT).h = p.h := by
  rw [hs.h_eq, PublicData.h, pd_hE c p hs]

theorem pd_R0 : (publicData c p B1 cT).R0 = p.R0 := by
  rw [hs.R0_eq, PublicData.R0, pd_k c p hs]; rfl

theorem pd_s : (publicData c p B1 cT).s = p.J := by
  have := hs.J_pos
  simp only [PublicData.s, publicData]
  omega

theorem pd_ell0 : (publicData c p B1 cT).ell0 (circuitsOf c hadm) = p.ell0 := by
  rw [hs.ell0_eq, PublicData.ell0, totalWeight_circuitsOf, pd_k c p hs, pd_R0 c p hs]
  rfl

theorem pd_cap : (publicData c p B1 cT).cap (circuitsOf c hadm) = (ellBar p.ell0 p.h p.T : ℝ) := by
  rw [ellBar_cast, PublicData.cap, pd_ell0 c p hadm hs, pd_h c p hs]
  rfl

theorem pd_M : (publicData c p B1 cT).M (circuitsOf c hadm) = p.M1 := by
  rw [hs.M1_eq, firstDen_cast, PublicData.M, pd_ell0 c p hadm hs, pd_h c p hs]
  rfl

theorem pd_x0 : (publicData c p B1 cT).x0 (circuitsOf c hadm) = (firstRatio p.ell0 p.h p.T : ℝ) := by
  rw [firstRatio_cast, PublicData.x0, pd_ell0 c p hadm hs, pd_h c p hs]
  rfl

theorem pd_rateRatio (j : ℕ) : NestedRateChain.rateRatio ((publicData c p B1 cT).x0 (circuitsOf c hadm)) j =
    (RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) j : ℝ) := by
  rw [pd_x0 c p hadm hs, RationalRateChain.ratio_cast _ (firstRatio_pos hs)]

theorem pd_factor (j : ℕ) (hj : j < p.J - 1) :
    (publicData c p B1 cT).factor (circuitsOf c hadm) j = rateOf p j := by
  obtain ⟨h1, h2⟩ := active_ratio hs j hj
  rw [PublicData.factor, pd_rateRatio c p hadm hs, ← RationalRateChain.factorRat_eq _ h1 h2]
  unfold rateOf
  have hlen := factors_length hs
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [hs.factors_eq, chainFactors, List.getElem_map, List.getElem_range]

theorem pd_product (j : ℕ) (hj : j ≤ p.J - 1) :
    NestedRateChain.product ((publicData c p B1 cT).x0 (circuitsOf c hadm)) j =
      ((List.range j).map fun i => RationalRateChain.factorRat
        (RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i)).prod := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨h1, h2⟩ := active_ratio hs j (by omega)
    have h2r : NestedRateChain.rateRatio ((publicData c p B1 cT).x0 (circuitsOf c hadm)) j < 1 / 256 := by
      rw [pd_rateRatio c p hadm hs]
      have := (Rat.cast_lt (K := ℝ)).mpr h2
      simpa using this
    rw [NestedRateChain.product, ih (by omega), List.range_succ, List.map_append, List.prod_append,
      NestedRateChain.multiplier, if_pos h2r, pd_rateRatio c p hadm hs, ← RationalRateChain.factorRat_eq _ h1 h2]
    simp [mul_comm]

theorem pd_A : (publicData c p B1 cT).A (circuitsOf c hadm) = p.A := by
  rw [PublicData.A, PublicData.cutoff, pd_product c p hadm hs _ (by simp [publicData]), hs.A_eq, hs.factors_eq]
  simp [publicData, chainFactors]

theorem pd_Lambda : (publicData c p B1 cT).Lambda (circuitsOf c hadm) = p.Lambda := by
  rw [PublicData.Lambda, pd_A c p hadm hs, hs.Lambda_eq]
  rfl

end PD

/-! ## The public guards -/

theorem publicGuards {B1 B2 cT : ℕ} (c : Call) (p : Params) (hadm : c.Admitted B1 B2) (hs : Spec cT (header c) p)
    (hW : c.W ≠ 0) (hB1 : 0 < B1) (hcT : 0 < cT)
    (hwin : 244 * (p.T : ℚ) * ellBar p.ell0 p.h p.T < (p.h : ℚ) * ((p.Lw : ℚ) - 1)) :
    PublicGuards (publicData c p B1 cT) (circuitsOf c hadm) := by
  have hn : 4 ≤ c.n := hadm.1
  have hβ1 : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.1
  have hβ16 : c.radius ≤ 1 / 16 := hadm.2.2.2.2.2.2.2.2.1
  have hnB : (0 : ℚ) < (c.n : ℚ) ^ B1 := by positivity
  have hβ : 0 < c.radius := by
    by_contra hneg
    have : c.radius * (c.n : ℚ) ^ B1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hnB.le
    linarith
  have hk := pd_k c p hs (B1 := B1)
  have Tpos : 0 < p.T := hs.T_pos hβ16
  have hJmax : (publicData c p B1 cT).Jmax = Jmax c.n := rfl
  have hstop := leastUpTo_spec _ _ _ hs.J_eq
  have hhpos : 0 < p.h := by have := hs.height; omega
  have hellbar : 0 ≤ ellBar p.ell0 p.h p.T := by
    unfold ellBar
    exact le_trans (by positivity) (le_max_right _ _)
  refine
    { nLarge := hn
      weightPositive := by rw [totalWeight_circuitsOf]; omega
      normalizedWeight := by rw [totalWeight_circuitsOf]; exact hadm.2.2.2.2.2.2.1
      precisionPositive := hB1
      betaPositive := hβ
      betaLower := by
        show 1 / (c.n : ℚ) ^ B1 ≤ c.radius
        rw [div_le_iff₀ hnB]; exact hβ1
      betaUpper := hβ16
      cTPositive := hcT
      kPositive := by rw [hk]; exact k_pos_of hs (by simp [header]; omega)
      kBelowN := by rw [hk]; exact hs.k_lt
      TPositive := Tpos
      TGuard := by
        have h := hs.T_pass
        unfold TPass at h
        rw [hk, hJmax]
        have h' : (((4 * Jmax c.n * 2 ^ p.k : ℕ) : ℚ) : ℝ) ≤ ((2 ^ p.T * c.radius : ℚ) : ℝ) :=
          Rat.cast_le.mpr h
        push_cast at h' ⊢
        exact h'
      TMinimal := by
        intro t ht
        have h := hs.T_least t ht
        unfold TPass at h
        rw [hk, hJmax]
        have h' : ((2 ^ t * c.radius : ℚ) : ℝ) < (((4 * Jmax c.n * 2 ^ p.k : ℕ) : ℚ) : ℝ) :=
          Rat.cast_lt.mpr (not_le.mp h)
        push_cast at h' ⊢
        exact h'
      PMinimum := hs.P_large
      PBelowN := by
        show p.P ≤ c.n
        rw [hs.P_eq]; exact (Nat.findGreatest_le _).trans (Nat.min_le_left _ _)
      height := by rw [pd_h c p hs]; exact hs.height
      stageCap := by
        rw [pd_s c p hs, hJmax]
        have h1 : p.J - 1 ≤ Jmax c.n - 1 := hstop.2.1
        have := hs.J_pos
        unfold Jmax at h1 ⊢
        omega
      stopped := by
        show (1 : ℝ) / 256 ≤ NestedRateChain.rateRatio _ (p.J - 1)
        rw [pd_rateRatio c p hadm hs, show (1 : ℝ) / 256 = ((1 / 256 : ℚ) : ℝ) by norm_num]
        exact Rat.cast_le.mpr hstop.1
      active := by
        intro j hj
        rw [pd_rateRatio c p hadm hs, show (1 : ℝ) / 256 = ((1 / 256 : ℚ) : ℝ) by norm_num]
        exact Rat.cast_lt.mpr (active_ratio hs j hj).2
      windowSize := by
        have hT0 : (0 : ℚ) ≤ 244 * (p.T : ℚ) * ellBar p.ell0 p.h p.T := by positivity
        have hpos : (0 : ℚ) < (p.h : ℚ) * ((p.Lw : ℚ) - 1) := lt_of_le_of_lt hT0 hwin
        have hh : (0 : ℚ) < p.h := by exact_mod_cast hhpos
        have hLw : (1 : ℚ) < p.Lw := by
          by_contra hle
          have : (p.h : ℚ) * ((p.Lw : ℚ) - 1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hh.le (by linarith [not_lt.mp hle])
          linarith
        have : 1 < p.Lw := by exact_mod_cast hLw
        show 2 ≤ p.Lw
        omega
      usefulWindow := by
        rw [pd_cap c p hadm hs, pd_h c p hs]
        have hh : (0 : ℝ) < p.h := by exact_mod_cast hhpos
        have h' := (Rat.cast_lt (K := ℝ)).mpr hwin
        push_cast at h'
        show 244 * (p.T : ℝ) * (ellBar p.ell0 p.h p.T : ℝ) / (p.h : ℝ) < (p.Lw : ℝ) - 1
        rw [div_lt_iff₀ hh]
        linarith }

end NearCubicGates.Close.Counter

/-!
# prop:complete and the completeness clause of thm:pair-uniform (paper v2 lines 1769–1811, 1905–1947)

From the sampling supply (lem:live + lem:bernstein + lem:sampled + global averaging, `Sampling`), the asymptotic
parameter facts (`eventual_selection`, `useful_window`) and the cell layer of prop:sound (`certain_of_tests`):
for every admitted call at large `n` under the caps, the encoded sampled proposal is a witness of length at most
`witnessBound n` whose returned radius is at most `β`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires
open NearCubicGates.Close.Counter.Sampling.WitnessContract

/-! ## The sampled proposal as witness data -/

/-- Role index in `Fin 2` (`0` for role 0, `1` otherwise). -/
def role2 (r : ℕ) : Fin 2 := if r = 0 then 0 else 1

theorem circ_role2 (c : Call) (r : ℕ) : circ c (role2 r).val = circ c r := by
  unfold role2 circ
  split_ifs <;> simp_all

/-- The sampled coefficient lists (stage `s`, role `r`). -/
noncomputable def sampledCoefs {n : ℕ} (pd : PublicData n) (C : Fin 2 → Target.WeightedSymmetricCircuit n)
    (draw : Samples C (pd.M C)) (s r : ℕ) : List ℤ :=
  List.ofFn fun i : Fin (C (role2 r)).bottomCount => coefficient pd C draw (role2 r) s i

theorem linForm_ofFn {n m : ℕ} (gates : List (NormalizedThresholdGate n)) (h : gates.length = m) (f : Fin m → ℤ)
    (z : BitInput n) :
    linForm gates (List.ofFn f) z = ∑ i : Fin m, f i * (if (gates[i.val]'(by rw [h]; exact i.isLt)).eval z then 1 else 0) := by
  rw [← List.sum_ofFn]
  unfold linForm
  congr 1
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]

section Moments

variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (hadm : c.Admitted B1 B2) (hs : Spec cT (header c) p)

include hadm in
theorem coeffs_length_role (r : ℕ) : (circ c r).gates.length = (circ c r).coeffs.length := by
  unfold circ
  split_ifs
  · exact hadm.2.1.1
  · exact hadm.2.2.1.1

theorem sampledCoefs_range2 (draw : Samples (circuitsOf c hadm) ((publicData c p B1 cT).M (circuitsOf c hadm)))
    (s : ℕ) (r2 : Fin 2) :
    List.Forall₂ (fun x y => |y| ≤ |x|) (circ c r2.val).coeffs
      (List.ofFn fun i : Fin (circuitsOf c hadm r2).bottomCount =>
        coefficient (publicData c p B1 cT) (circuitsOf c hadm) draw r2 s i) := by
  rw [List.forall₂_iff_get]
  have hcount : (circuitsOf c hadm r2).bottomCount = (circ c r2.val).coeffs.length := circuitsOf_bottomCount c hadm r2
  refine ⟨by simp [hcount], ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  have hb := GlobalSamplingWitness.sampledCoefficient_witness_range (circuitsOf c hadm r2)
    (GlobalSamplingWitness.nestedKeep (circuitsOf c hadm r2) (fun u => draw ⟨r2, u⟩)
      ((publicData c p B1 cT).cutoff (circuitsOf c hadm) s)) ⟨i, by rw [hcount]; exact h1⟩
  have hcoef : ((circuitsOf c hadm r2).coefficient ⟨i, by rw [hcount]; exact h1⟩) = (circ c r2.val).coeffs[i] := by
    fin_cases r2 <;> rfl
  rw [hcoef] at hb
  rw [abs_le, Int.abs_eq_natAbs]
  exact ⟨by simpa [coefficient] using hb.1, by simpa [coefficient] using hb.2⟩

theorem sampledCoefs_range (draw : Samples (circuitsOf c hadm) ((publicData c p B1 cT).M (circuitsOf c hadm)))
    (s r : ℕ) :
    List.Forall₂ (fun x y => |y| ≤ |x|) (circ c r).coeffs
      (sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw s r) := by
  rw [← circ_role2 c r]
  exact sampledCoefs_range2 c p hadm draw s (role2 r)

include hadm in
theorem linForm_circuitsOf (r2 : Fin 2) (f : Fin (circuitsOf c hadm r2).bottomCount → ℤ) (z : BitInput c.n) :
    linForm (circ c r2.val).gates (List.ofFn f) z =
      ∑ i, f i * (if ((circuitsOf c hadm r2).bottom i).eval z then 1 else 0) := by
  fin_cases r2
  · rw [linForm_ofFn (circ c 0).gates (by simp [circ]; exact hadm.2.1.1)]
    apply Finset.sum_congr rfl
    intro i _
    change _ = f i * (if ((toWSC c.first hadm.2.1.1 hadm.2.1.2.1).bottom i).eval z then 1 else 0)
    rw [toWSC_bottom_eval]
    rfl
  · rw [linForm_ofFn (circ c 1).gates (by simp [circ]; exact hadm.2.2.1.1)]
    apply Finset.sum_congr rfl
    intro i _
    change _ = f i * (if ((toWSC c.second hadm.2.2.1.1 hadm.2.2.1.2.1).bottom i).eval z then 1 else 0)
    rw [toWSC_bottom_eval]
    rfl

theorem proposedDigit_congr (rate rate' value value' : ℕ → ℤ) (j : ℕ)
    (hr : ∀ i, i < j → rate i = rate' i) (hv : ∀ i, i ≤ j → value i = value' i) :
    CountingCore.proposedDigit rate value j = CountingCore.proposedDigit rate' value' j := by
  cases j with
  | zero => simp only [CountingCore.proposedDigit]; exact hv 0 le_rfl
  | succ j =>
    simp only [CountingCore.proposedDigit]
    rw [hv (j + 1) le_rfl, hv j (by omega), hr j (by omega)]

variable (I : Coordinates c.n (publicData c p B1 cT).k)
  (draw : Samples (circuitsOf c hadm) ((publicData c p B1 cT).M (circuitsOf c hadm)))
  (wcoef : ℕ → ℕ → List ℤ)

theorem stageForm_sampled
    (hcoef : ∀ s r, s < p.J → r < roleCount c.kind →
      wcoef s r = sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw s r)
    (r : Role c) (s : ℕ) (hsJ : s < p.J) (z : BitInput c.n) :
    stageForm c ⟨I.val, wcoef⟩ r.val s z =
      sampledScore (publicData c p B1 cT) (circuitsOf c hadm) draw (role2 r.val) s z := by
  unfold stageForm
  simp only
  rw [hcoef s r.val hsJ r.isLt, ← circ_role2 c r.val, sampledCoefs, linForm_circuitsOf c hadm]
  rfl

include hs in
theorem digit_sampled
    (hcoef : ∀ s r, s < p.J → r < roleCount c.kind →
      wcoef s r = sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw s r)
    (r : Role c) (j : ℕ) (hj : j < p.J) (z : BitInput c.n) :
    digit c p ⟨I.val, wcoef⟩ r.val j z =
      CountingCore.proposedDigit ((publicData c p B1 cT).factor (circuitsOf c hadm))
        (fun s => sampledScore (publicData c p B1 cT) (circuitsOf c hadm) draw (role2 r.val) s z) j := by
  unfold digit
  apply proposedDigit_congr
  · intro i hi
    exact (pd_factor c p hadm hs i (by omega)).symm
  · intro i hi
    exact stageForm_sampled c p hadm I draw wcoef hcoef r i (by omega) z

include hs in
theorem tests_of_passes
    (hcoef : ∀ s r, s < p.J → r < roleCount c.kind →
      wcoef s r = sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw s r)
    (y : Cells I.val) (hpass : passesLiteralMoments (publicData c p B1 cT) (circuitsOf c hadm) I draw y = true) :
    CellTests c p ⟨I.val, wcoef⟩ y := by
  simp only [passesLiteralMoments, decide_eq_true_eq] at hpass
  obtain ⟨hdig, hphi⟩ := hpass
  have hr2 : ∀ r : Role c, (role2 r.val).val = r.val := by
    intro r
    have := r.isLt
    unfold role2
    have hle : roleCount c.kind ≤ 2 := by cases c.kind <;> decide
    split_ifs with h <;> simp <;> omega
  have hk : (publicData c p B1 cT).k = p.k := pd_k c p hs
  constructor
  · intro r j
    have h := hdig (role2 r.val) ⟨j.val, by rw [pd_s c p hs]; exact j.isLt⟩
    have heq : Counter.digitMoment c p ⟨I.val, wcoef⟩ r.val j.val y =
        Sampling.WitnessContract.digitMoment (publicData c p B1 cT) (circuitsOf c hadm) I draw (role2 r.val) y
          ⟨j.val, by rw [pd_s c p hs]; exact j.isLt⟩ := by
      unfold Counter.digitMoment Sampling.WitnessContract.digitMoment
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      · rw [digit_sampled c p hadm hs I draw wcoef hcoef r j.val j.isLt,
          digit_sampled c p hadm hs I draw wcoef hcoef r j.val j.isLt]
        rfl
      · rw [hk]
    calc Counter.digitMoment c p ⟨I.val, wcoef⟩ r.val j.val y = _ := heq
      _ < _ := h
      _ = (p.hE : ℤ) ^ (2 * p.k) := by rw [pd_hE c p hs, hk]
  · intro r
    have h := hphi (role2 r.val)
    have hJl : (publicData c p B1 cT).Jlean = p.J - 1 := rfl
    have hJ := hs.J_pos
    have heq : Counter.phiMoment c p ⟨I.val, wcoef⟩ r.val y =
        Sampling.WitnessContract.phiMoment (publicData c p B1 cT) (circuitsOf c hadm) I draw (role2 r.val) y := by
      unfold Counter.phiMoment Sampling.WitnessContract.phiMoment
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      · simp only [Counter.phi, CertifiedScoreSupport.phi, Sampling.WitnessContract.values,
          Sampling.WitnessContract.score, hJl, pd_M c p hadm hs, pd_A c p hadm hs]
        rw [stageForm_sampled c p hadm I draw wcoef hcoef r (p.J - 1) (by omega),
          stageForm_sampled c p hadm I draw wcoef hcoef r (p.J - 1) (by omega)]
        simp only [scoreForm, circuitsOf_score, circ_role2]
        rfl
      · rw [hk]
    calc Counter.phiMoment c p ⟨I.val, wcoef⟩ r.val y = _ := heq
      _ < _ := h
      _ = (p.Lambda : ℤ) ^ (2 * p.k) := by rw [pd_Lambda c p hadm hs, hk]

end Moments

/-! ## The caps of thm:pair-uniform in the paper's real form -/

theorem lambda_ge_two (n : ℕ) (hn : 4 ≤ n) : 2 ≤ Target.lambda n := by
  have h := Nat.clog_mono_right 2 hn
  have h4 : Nat.clog 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.clog_pow 2 2 (by decide)]
  unfold Target.lambda
  omega

theorem mu_pos (n : ℕ) (hn : 4 ≤ n) : 0 < Target.mu n :=
  Nat.clog_pos (by decide) (by have := lambda_ge_two n hn; omega)

theorem pairCapQ_of_real (K : ℕ) (hK : 0 < K) (hd : Header) (hn : 4 ≤ hd.n) (hβ : 0 < hd.beta)
    (h : (hd.W : ℝ) ≤ (1 / (K : ℝ)) * (hd.beta : ℝ) * A3 hd.n) : PairCapQ K hd := by
  unfold PairCapQ
  have hL : (0 : ℝ) < ((Target.lambda hd.n : ℕ) : ℝ) := by
    have := lambda_ge_two hd.n hn; exact_mod_cast (by omega : 0 < Target.lambda hd.n)
  have hM : (0 : ℝ) < ((Target.mu hd.n : ℕ) : ℝ) := by exact_mod_cast mu_pos hd.n hn
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hβr : (0 : ℝ) < (hd.beta : ℝ) := by exact_mod_cast hβ
  have hLr : 0 < ((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) := Real.rpow_pos_of_pos hL _
  have hden : 0 < ((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) * ((Target.mu hd.n : ℕ) : ℝ) ^ 7 := by positivity
  have h1 : (K : ℝ) * hd.W * (((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) * ((Target.mu hd.n : ℕ) : ℝ) ^ 7) ≤
      (hd.beta : ℝ) * (hd.n : ℝ) ^ 3 := by
    unfold A3 at h
    rw [show (1 / (K : ℝ)) * (hd.beta : ℝ) * ((hd.n : ℝ) ^ 3 / (((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) *
      ((Target.mu hd.n : ℕ) : ℝ) ^ 7)) = ((hd.beta : ℝ) * (hd.n : ℝ) ^ 3) / ((K : ℝ) *
        (((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) * ((Target.mu hd.n : ℕ) : ℝ) ^ 7)) by field_simp] at h
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4)) ^ 4 = ((Target.lambda hd.n : ℕ) : ℝ) ^ 21 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have goalR : ((((K * hd.W * (Target.mu hd.n) ^ 7 : ℕ) : ℚ) ^ 4 * ((Target.lambda hd.n : ℕ) : ℚ) ^ 21 : ℚ) : ℝ) ≤
      (((hd.n : ℚ) ^ 12 * hd.beta ^ 4 : ℚ) : ℝ) := by
    push_cast
    calc ((K : ℝ) * hd.W * ((Target.mu hd.n : ℕ) : ℝ) ^ 7) ^ 4 * ((Target.lambda hd.n : ℕ) : ℝ) ^ 21
        = ((K : ℝ) * hd.W * (((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) * ((Target.mu hd.n : ℕ) : ℝ) ^ 7)) ^ 4 := by
          rw [mul_pow (_ * _ : ℝ) (_ * _ : ℝ) 4, mul_pow (((Target.lambda hd.n : ℕ) : ℝ) ^ ((21 : ℝ) / 4)) _ 4, h3]; ring
      _ ≤ ((hd.beta : ℝ) * (hd.n : ℝ) ^ 3) ^ 4 := h2
      _ = (hd.n : ℝ) ^ 12 * (hd.beta : ℝ) ^ 4 := by ring
  exact_mod_cast goalR

theorem scalarCapQ_of_real (K : ℕ) (hK : 0 < K) (hd : Header) (hn : 4 ≤ hd.n) (hβ : 0 < hd.beta)
    (h : (hd.W : ℝ) ≤ (1 / (K : ℝ)) * (hd.beta : ℝ) * A1 hd.n) : ScalarCapQ K hd := by
  unfold ScalarCapQ
  have hL : (0 : ℝ) < ((Target.lambda hd.n : ℕ) : ℝ) := by
    have := lambda_ge_two hd.n hn; exact_mod_cast (by omega : 0 < Target.lambda hd.n)
  have hM : (0 : ℝ) < ((Target.mu hd.n : ℕ) : ℝ) := by exact_mod_cast mu_pos hd.n hn
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hnr : (0 : ℝ) < hd.n := by exact_mod_cast (by omega : 0 < hd.n)
  have h1 : (K : ℝ) * hd.W * (((Target.lambda hd.n : ℕ) : ℝ) ^ 6 * ((Target.mu hd.n : ℕ) : ℝ) ^ 8) ≤
      (hd.beta : ℝ) * (hd.n : ℝ) ^ ((7 : ℝ) / 2) := by
    unfold A1 at h
    rw [show (1 / (K : ℝ)) * (hd.beta : ℝ) * ((hd.n : ℝ) ^ ((7 : ℝ) / 2) / (((Target.lambda hd.n : ℕ) : ℝ) ^ 6 *
      ((Target.mu hd.n : ℕ) : ℝ) ^ 8)) = ((hd.beta : ℝ) * (hd.n : ℝ) ^ ((7 : ℝ) / 2)) / ((K : ℝ) *
        (((Target.lambda hd.n : ℕ) : ℝ) ^ 6 * ((Target.mu hd.n : ℕ) : ℝ) ^ 8)) by field_simp] at h
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : ((hd.n : ℝ) ^ ((7 : ℝ) / 2)) ^ 2 = (hd.n : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnr.le]
    norm_num
  have goalR : ((((K * hd.W * (Target.lambda hd.n) ^ 6 * (Target.mu hd.n) ^ 8 : ℕ) : ℚ) ^ 2 : ℚ) : ℝ) ≤
      (((hd.n : ℚ) ^ 7 * hd.beta ^ 2 : ℚ) : ℝ) := by
    push_cast
    calc ((K : ℝ) * hd.W * ((Target.lambda hd.n : ℕ) : ℝ) ^ 6 * ((Target.mu hd.n : ℕ) : ℝ) ^ 8) ^ 2
        = ((K : ℝ) * hd.W * (((Target.lambda hd.n : ℕ) : ℝ) ^ 6 * ((Target.mu hd.n : ℕ) : ℝ) ^ 8)) ^ 2 := by ring
      _ ≤ ((hd.beta : ℝ) * (hd.n : ℝ) ^ ((7 : ℝ) / 2)) ^ 2 := h2
      _ = (hd.n : ℝ) ^ 7 * (hd.beta : ℝ) ^ 2 := by rw [mul_pow, h3]; ring
  exact_mod_cast goalR

/-! ## The witness length -/

/-- A fixed polynomial bound on the witness prefix (line 1651: "Only this polynomial-length prefix is read"). -/
def witnessBound (n : ℕ) : ℕ := 7 * (n + 1) ^ 5

theorem coefWidth_le (a : ℤ) (ha : a ≠ 0) : coefWidth a ≤ 3 * a.natAbs := by
  unfold coefWidth
  have h1 := clog_le_self (2 * a.natAbs + 1)
  have h2 : 1 ≤ a.natAbs := Int.natAbs_pos.mpr ha
  omega

theorem coefWidth_sum_le (l : List ℤ) (hl : ∀ a ∈ l, a ≠ 0) : (l.map coefWidth).sum ≤ 3 * (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := coefWidth_le a (hl a (by simp))
    have h2 := ih (fun b hb => hl b (by simp [hb]))
    omega

theorem prefixLength_le {B1 B2 cT : ℕ} (c : Call) (p : Params) (hadm : c.Admitted B1 B2)
    (hs : Spec cT (header c) p) : prefixLength c p ≤ witnessBound c.n := by
  have hn : 4 ≤ c.n := hadm.1
  have hk : p.k < c.n := hs.k_lt
  have hl : Target.lambda c.n ≤ c.n := clog_le_self c.n
  have hJ : p.J ≤ c.n + 1 := by
    have h1 := (leastUpTo_spec _ _ _ hs.J_eq).2.1
    have h2 := hs.J_pos
    have h3 : Target.mu c.n ≤ c.n := (clog_le_self _).trans hl
    simp only [header, Jmax] at h1
    omega
  have h0 := coefWidth_sum_le c.first.coeffs hadm.2.1.2.1
  have h1 := coefWidth_sum_le c.second.coeffs hadm.2.2.1.2.1
  have hW : c.W ≤ 2 * c.n ^ 4 := hadm.2.2.2.2.2.2.1
  have hS : ((List.range (roleCount c.kind)).map fun r => ((circ c r).coeffs.map coefWidth).sum).sum ≤
      3 * c.W := by
    unfold Call.W NCircuit.topWeight at hW ⊢
    rcases kind_cases c with hk' | hk' | hk' <;>
      simp only [hk', roleCount, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, circ, if_pos, add_zero, one_ne_zero, if_false,
        List.singleton_append] <;> omega
  unfold prefixLength witnessBound
  have hkl : p.k * Target.lambda c.n ≤ c.n * c.n := Nat.mul_le_mul hk.le hl
  have hJS : p.J * ((List.range (roleCount c.kind)).map fun r => ((circ c r).coeffs.map coefWidth).sum).sum ≤
      (c.n + 1) * (6 * c.n ^ 4) := Nat.mul_le_mul hJ (by omega)
  have hpow : c.n * c.n + (c.n + 1) * (6 * c.n ^ 4) ≤ 7 * (c.n + 1) ^ 5 := by
    have : c.n ≤ c.n + 1 := by omega
    nlinarith [Nat.pow_le_pow_left this 4, Nat.zero_le c.n]
  omega

/-! ## prop:complete -/

theorem card_cells {n k : ℕ} (I : Coordinates n k) : Fintype.card (Cells I.val) = 2 ^ (n - k) := by
  simp only [Cells, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe]
  rw [I.property]

open Classical in
theorem mean_failure_eq {n k : ℕ} (I : Coordinates n k) (b : Cells I.val → Bool) :
    FiniteAverages.mean (fun y => GlobalSamplingWitness.failure (b y)) =
      (((Finset.univ : Finset (Cells I.val)).filter fun y => b y = false).card : ℝ) / 2 ^ (n - k) := by
  unfold FiniteAverages.mean
  rw [card_cells I, Finset.card_filter]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  cases b y <;> simp [GlobalSamplingWitness.failure]

theorem zeroWeightValue_radius (c : Call) : (zeroWeightValue c).2 = 0 := by
  unfold zeroWeightValue
  split
  · rfl
  · rfl
  · split <;> rfl

open Classical in
/-- prop:complete and the completeness clause of thm:pair-uniform: under the caps, at every large `n`, some
witness of length at most `witnessBound n` gives radius at most `β`. Published inputs: lem:live (input 2),
lem:bernstein (input 3), the prime number theorem (input 4). -/
theorem counter_complete
    (hR : PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction)
    (hB : PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (hP : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem)
    (B1 B2 cT : ℕ) (hB1 : 0 < B1) (hcT : 0 < cT) :
    ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 →
      (c.kind = .pair → (c.W : ℝ) ≤ a * (c.radius : ℝ) * A3 c.n) →
      (c.kind ≠ .pair → (c.W : ℝ) ≤ a * (c.radius : ℝ) * A1 c.n) →
      ∃ w : List Bool, w.length ≤ witnessBound c.n ∧ (counterOnCall B1 B2 cT c w).2 ≤ c.radius := by
  obtain ⟨o1, hsel⟩ := eventual_selection hP B1 cT
  obtain ⟨o2, hwin⟩ := useful_window hP B1 cT
  have hKp : 0 < pairConstant B1 cT := by unfold pairConstant pairWindowConstant; omega
  have hKs : 0 < scalarConstant B1 cT := by unfold scalarConstant scalarWindowConstant; omega
  obtain ⟨K, hKpK, hKsK⟩ : ∃ K : ℕ, pairConstant B1 cT ≤ K ∧ scalarConstant B1 cT ≤ K :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hK : 0 < K := lt_of_lt_of_le hKp hKpK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨1 / K, one_div_pos.mpr hKr, max o1 o2, ?_⟩
  intro c hn hadm hpairCap hscalarCap
  have hok : HeaderOK B1 (header c) :=
    ⟨hadm.1, hadm.2.2.2.2.2.2.1, hadm.2.2.2.2.2.2.2.1, hadm.2.2.2.2.2.2.2.2.1⟩
  have hβ : 0 < c.radius := hok.beta_pos
  have hβr : (0 : ℝ) < (c.radius : ℝ) := by exact_mod_cast hβ
  by_cases hW : c.W = 0
  · refine ⟨[], by simp, ?_⟩
    simp only [counterOnCall, if_pos hadm, if_pos hW, zeroWeightValue_radius]
    exact hβ.le
  have hn1 : o1 ≤ (header c).n := (le_max_left _ _).trans hn
  obtain ⟨p, hp⟩ := hsel (header c) hok hn1
  have hs := selectParams_spec cT (header c) p hp
  have hcap : if (header c).pair then PairCapQ (pairConstant B1 cT) (header c)
      else ScalarCapQ (scalarConstant B1 cT) (header c) := by
    by_cases hk : c.kind = .pair
    · have hpair : (header c).pair = true := by simp [header, hk]
      rw [if_pos hpair]
      apply pairCapQ_of_real _ hKp (header c) hadm.1 hβ
      have hA : 0 ≤ A3 c.n := by unfold A3; positivity
      have hle : 1 / (K : ℝ) ≤ 1 / (pairConstant B1 cT : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hKp) (by exact_mod_cast hKpK)
      calc ((header c).W : ℝ) = c.W := rfl
        _ ≤ 1 / K * c.radius * A3 c.n := hpairCap hk
        _ ≤ 1 / (pairConstant B1 cT) * c.radius * A3 c.n := by gcongr
    · have hpair : (header c).pair = false := by simp [header, hk]
      rw [if_neg (by simp [hpair])]
      apply scalarCapQ_of_real _ hKs (header c) hadm.1 hβ
      have hA : 0 ≤ A1 c.n := by unfold A1; positivity
      have hle : 1 / (K : ℝ) ≤ 1 / (scalarConstant B1 cT : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hKs) (by exact_mod_cast hKsK)
      calc ((header c).W : ℝ) = c.W := rfl
        _ ≤ 1 / K * c.radius * A1 c.n := hscalarCap hk
        _ ≤ 1 / (scalarConstant B1 cT) * c.radius * A1 c.n := by gcongr
  have hw := hwin (header c) p hok ((le_max_right _ _).trans hn) hp hcap
  have hG := publicGuards c p hadm hs hW hB1 hcT hw
  obtain ⟨I, draw, _, _, _, hmean⟩ :=
    Sampling.StandaloneSupply.samplingSupply hR hB c.n (publicData c p B1 cT) (circuitsOf c hadm) hG
  have hIk : I.val.card = p.k := by rw [I.property, pd_k c p hs]
  obtain ⟨wt, hdec, hwI, hwcoef⟩ := decode_encode c p I.val hIk
    (sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw) (sampledCoefs_range c p hadm draw)
  refine ⟨encodeWitness c p I.val (sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw), ?_, ?_⟩
  · rw [encodeWitness_length c p I.val hIk _ (sampledCoefs_range c p hadm draw)]
    exact prefixLength_le c p hadm hs
  · have hval : counterOnCall B1 B2 cT c
        (encodeWitness c p I.val (sampledCoefs (publicData c p B1 cT) (circuitsOf c hadm) draw)) =
        outputOf c p wt := by
      simp only [counterOnCall, if_pos hadm, if_neg hW, hp, hdec]
    rw [hval]
    obtain ⟨WI, wcoef⟩ := wt
    simp only at hwI hwcoef
    subst hwI
    have hk1 : 1 ≤ p.k := k_pos_of hs (by simp [header]; have := hadm.1; omega)
    have hrad := outputOf_radius_le c p ⟨I.val, wcoef⟩ hs hIk hk1 hs.k_lt.le
    have hsub : ((Finset.univ : Finset (Cells I.val)).filter fun y => ¬ CellTests c p ⟨I.val, wcoef⟩ y) ⊆
        (Finset.univ : Finset (Cells I.val)).filter fun y =>
          passesLiteralMoments (publicData c p B1 cT) (circuitsOf c hadm) I draw y = false := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      by_contra hpass
      exact hy (tests_of_passes c p hadm hs I draw wcoef hwcoef y (by simpa using hpass))
    have hcard := Finset.card_le_card hsub
    have hmean' := mean_failure_eq I (fun y => passesLiteralMoments (publicData c p B1 cT) (circuitsOf c hadm) I draw y)
    rw [hmean'] at hmean
    have hnk : c.n - (publicData c p B1 cT).k = c.n - p.k := by rw [pd_k c p hs]
    rw [hnk] at hmean
    have hpowpos : (0 : ℝ) < 2 ^ (c.n - p.k) := by positivity
    have hfinal : (((outputOf c p ⟨I.val, wcoef⟩).2 : ℚ) : ℝ) ≤ (c.radius : ℝ) := by
      have h1 : (((outputOf c p ⟨I.val, wcoef⟩).2 : ℚ) : ℝ) ≤
          ((((Finset.univ : Finset (Cells I.val)).filter fun y => ¬ CellTests c p ⟨I.val, wcoef⟩ y).card : ℚ) /
            2 ^ (c.n - p.k) / 2 : ℚ) := Rat.cast_le.mpr hrad
      push_cast at h1
      have h2 : ((((Finset.univ : Finset (Cells I.val)).filter fun y => ¬ CellTests c p ⟨I.val, wcoef⟩ y).card : ℝ)) ≤
          (((Finset.univ : Finset (Cells I.val)).filter fun y =>
            passesLiteralMoments (publicData c p B1 cT) (circuitsOf c hadm) I draw y = false).card : ℝ) := by
        exact_mod_cast hcard
      have h3 := div_le_div_of_nonneg_right h2 hpowpos.le
      have h4 := div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 2)
      calc _ ≤ _ := h1
        _ ≤ _ := h4
        _ ≤ (c.radius : ℝ) := hmean
    exact_mod_cast hfinal

end NearCubicGates.Close.Counter
