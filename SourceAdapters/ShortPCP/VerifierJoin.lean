import SourceAdapters.ShortPCP.VerifierInstance
import SourceAdapters.ShortPCP.VerifierBounds
import SourceAdapters.ShortPCP.VerifierSize

/-!
# The single-run verifier on an affine constraint instance, from BCGT13 Theorem 11.1

`singleRunVerifier : BCGT13_Theorem11_1 → Joins.SingleRunVerifier` (proof of `thm:short-pcp-ours`,
Step 2).

For an instance `(c, x̄)` satisfying `Good`: the sub-verifiers of `V0` are the leaf's `V_RS`, `V_VRS` on the domain
`S = F` (`monoBasis`, a basis spanning `F`), packaged as `SubVerifiers` of the request's `ACSPInstance`
(`ShortPCP/Verifier.lean`); `V0 = Request.runVerdict` is `SubVerifiers.acceptsAt` on the decoded tables
(`runVerdict_eq`); completeness and the four-case soundness come from `completeAt` and `soundAt` with
`mem_iff_accepts`, and the uniform constant from `uniform_rejection` (`K1 = 120·max(Kc, 1)`, `b1 = 37`). Step 2 (a)
gives `r0` and `L_π` (`K = 64`, `b = 4`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Verifier

open Finset Polynomial NearCubicWires.WireExponent3_5 NearCubicWires.CanonicalBinary
open NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP
open NearCubicGates.Adapters.ACSP.Affine NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun

variable {Kc : ℕ} {c : Instance} {xs : List Bool}

theorem tuple0_valid : tuple0.Valid := by
  show Equation6 2 4 0 1; decide

/-- The fixed tuple lies in the domain of the printed soundness constant. -/
theorem tuple0_positive_exponents : tuple0.PositiveExponents := by
  have hfloor : floorHalf 6 = 3 := by decide
  have hceil : ceilHalf 5 = 3 := by decide
  have h1 : 0 < Real.logb 2 (6 / 5 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have h2 : 0 < Real.logb 2 (5 / 3 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  convert And.intro h1 h2 using 1
  norm_num [Tuple.PositiveExponents, tuple0, sThree_four, sOne_four, hfloor, hceil]

theorem card_fld (hG : SingleRun.Good Kc c xs) [Fintype c.Fld] : Fintype.card c.Fld = 2 ^ c.f := by
  rw [← Nat.card_eq_fintype_card]; exact GF.natCard_ref c.irr c.f (Good.modOk hG)

/-! ## The facts `ACSPInstance.Good` of the request -/

section Inst

variable (hG : SingleRun.Good Kc c xs) (S : List (List Bool)) [Fact (Irreducible c.irrPoly)]
  [Fintype c.Fld] [DecidableEq c.Fld]
include hG

/-- The facts `ACSPInstance.Good` of the request's instance (Step 2, "Completeness" and "Base soundness"). -/
theorem good_instance : ((request c xs S).acsp (RingHom.id c.Fld)).Good := by
  have hcard := card_fld hG
  have hmH := hG.mH_two_le
  have hf2 := Good.two_le_f hG
  have hpow : 2 ^ c.mH * 4 ≤ 2 ^ c.f := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hmH
  have hH1 : 1 ≤ 2 ^ c.mH := Nat.one_le_two_pow
  refine ⟨Good.cN_pos hG, ?_, ?_, ?_, ?_, ?_⟩
  · intro i α β hαβ
    have hs := Good.slope_ne hG i.val i.isLt
    change c.slope i.val * α + c.shift i.val = c.slope i.val * β + c.shift i.val at hαβ
    exact mul_left_cancel₀ hs (add_right_cancel hαβ)
  · exact px_low hG S
  · intro A hA
    refine ⟨c.composed A, Good.composed_le_dH hG A ((natDegree_le_pred_iff A _ Nat.one_le_two_pow).mp hA),
      fun α => ?_⟩
    rw [composed_eval, acsp_P']
    rfl
  · rw [hcard]; show 4 * (2 ^ c.mH - 1) < 3 * 2 ^ c.f; omega
  · rw [hcard]; exact (Good.dH_lt hG).2

end Inst

/-! ## The main per-instance theorem -/

theorem getD_ofFn {r : ℕ} (R : Fin r → Bool) (i : Fin r) : (List.ofFn R).getD i.val false = R i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- **`V0` on one instance**: completeness and base soundness with the uniform constant (proof of
`thm:short-pcp-ours`, Step 2, (c) and (d), and Step 3). -/
theorem singleRun_core (h11 : BCGT13_Theorem11_1) (hG : SingleRun.Good Kc c xs) :
    (c.Accepts xs → ∃ π : ℕ → Bool, ∀ R : List Bool, SingleRun.accepts c xs π R = true) ∧
    (¬ c.Accepts xs → ∀ π : ℕ → Bool,
      acceptFrac (fun R : Fin (r0 c) → Bool => SingleRun.accepts c xs π (List.ofFn R)) ≤
        1 - 1 / (((120 * max Kc 1 : ℕ) : ℝ) * (c.f : ℝ) ^ 37)) := by
  have hp := Good.modOk hG
  have hirr := Good.irr hG
  haveI : Fact (Irreducible c.irrPoly) := ⟨hirr⟩
  letI : Fintype c.Fld := Fintype.ofEquiv _ (GF.encEquiv c.irr c.f hp)
  letI : DecidableEq c.Fld := Classical.decEq _
  haveI : CharP c.Fld 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) c.Fld).injective 2
  have hcard := card_fld hG
  have hspan := span_mono_univ c hp
  have hB : IsBasis (monoBasis c) 0 := isBasis_mono c hp
  have hBH : IsBasis (c.hBasis.map c.elt) (c.elt c.hOffset) := isBasis_map c _ _ (indep_H hG)
  have hBI : IsBasis (c.iBasis.map c.elt) (c.elt c.iOffset) := isBasis_map c _ _ (indep_I hG)
  have hlenB : (monoBasis c).length = c.f := length_monoBasis c
  have hlenH : (c.hBasis.map c.elt).length = c.mH := List.length_map _
  have hlenI : (c.iBasis.map c.elt).length = c.m := List.length_map _
  have hmH := hG.mH_two_le
  have hmI := hG.m_lt
  have h1m := hG.one_le_m
  have hf2 := Good.two_le_f hG
  have hpowH : 2 ^ c.mH < 2 ^ c.f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpowI : 2 ^ c.m < 2 ^ c.mH := Nat.pow_lt_pow_right (by norm_num) hmI
  have hH1 : 2 ≤ 2 ^ c.mH := by
    have : 2 ^ 1 ≤ 2 ^ c.mH := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hdA : 2 ^ c.mH - 1 < 2 ^ (monoBasis c).length := by rw [hlenB]; omega
  have hdA1 : 1 ≤ 2 ^ c.mH - 1 := by omega
  have hHd : 2 ^ (c.hBasis.map c.elt).length ≤ dH c := by rw [hlenH]; exact Good.two_pow_mH_le_dH hG
  have hdH : dH c < 2 ^ (monoBasis c).length := by rw [hlenB]; exact (Good.dH_lt hG).1
  have hId : 2 ^ (c.iBasis.map c.elt).length ≤ 2 ^ c.mH - 1 := by rw [hlenI]; omega
  have hsub : ∀ S : Finset c.Fld, S ⊆ span (monoBasis c) 0 := fun S => hspan ▸ Finset.subset_univ S
  have hbij : Function.Bijective (fun b : Fin c.f → Bool => getRandElt (monoBasis c) 0 (List.ofFn b)) := by
    have := elt_maskOfBits_bijective c hp
    convert this using 1
    funext b
    exact getRandElt_mono c b
  let D := (request c xs [[]]).acsp (RingHom.id c.Fld)
  let K : ℝ := soundTerm tuple0.η tuple0.κ0 tuple0.γ tuple0.μ (monoBasis c).length
  let W : SubVerifiers D (1 / (1 + K)) (1 / (2 + K)) (1 / (2 + K)) :=
    { f := c.f
      elem := Equiv.ofBijective _ hbij
      VR := strongCongr hspan (by rw [hspan]; try rfl)
        (rsOfLeaf h11 tuple0 tuple0_valid tuple0_positive_exponents c.f hcard (monoBasis c) 0 hB (2 ^ c.mH - 1) hdA1 hdA)
      VH := strongCongr hspan (by rw [hspan]; try rfl)
        (vrsOfLeaf h11 tuple0 tuple0_valid tuple0_positive_exponents c.f hcard (monoBasis c) 0 hB (c.hBasis.map c.elt) (c.elt c.hOffset)
          hBH (hsub _) (dH c) hHd hdH)
      VI := strongCongr hspan (by rw [hspan]; try rfl)
        (vrsOfLeaf h11 tuple0 tuple0_valid tuple0_positive_exponents c.f hcard (monoBasis c) 0 hB (c.iBasis.map c.elt) (c.elt c.iOffset)
          hBI (hsub _) (2 ^ c.mH - 1) hId hdA) }
  have hR : W.VR.rand ≤ r0 c := by
    show (vRS tuple0 (monoBasis c) 0 (2 ^ c.mH - 1)).rand ≤ r0 c
    rw [vRS_rand_eq, hlenB]; unfold r0; omega
  have hH : W.VH.rand ≤ r0 c := by
    show (vVRS tuple0 (monoBasis c) 0 (c.hBasis.map c.elt) (c.elt c.hOffset) (dH c)).rand ≤ r0 c
    rw [vVRS_rand_eq, hlenB, hlenH]; unfold r0; omega
  have hf : W.f ≤ r0 c := by show c.f ≤ r0 c; unfold r0; omega
  have hI : W.VI.rand ≤ r0 c := by
    show (vVRS tuple0 (monoBasis c) 0 (c.iBasis.map c.elt) (c.elt c.iOffset) (2 ^ c.mH - 1)).rand ≤ r0 c
    rw [vVRS_rand_eq, hlenB, hlenI]; unfold r0; omega
  let dec : (ℕ → Bool) → ProofTable W := fun π =>
    { p0 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).p0
      π0 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).π0
      p1 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).p1
      π1 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).π1
      πc := ((request c xs [[]]).decode (RingHom.id c.Fld) π).πc }
  have hpt : ∀ ρ : ℕ → Bool, (request c xs [[]]).consistPoint (RingHom.id c.Fld) ρ =
      W.elem (pre W.f hf fun i : Fin (r0 c) => ρ i.val) := by
    intro ρ
    show c.elt (bitsValue ((List.range c.f).map ρ)) =
      getRandElt (monoBasis c) 0 (List.ofFn fun i : Fin c.f => ρ i.val)
    rw [getRandElt_mono, bitsValue_range_map]
  have hacc : ∀ (π : ℕ → Bool) (ρ : ℕ → Bool),
      (request c xs [[]]).runVerdict (RingHom.id c.Fld) ((request c xs [[]]).decode (RingHom.id c.Fld) π) ρ =
        W.acceptsAt (r0 c) hR hH hf hI (dec π) (fun i => ρ i.val) := by
    intro π ρ
    unfold Request.runVerdict SubVerifiers.acceptsAt
    rw [hpt]
    rfl
  have hnot : ¬ c.Accepts xs → ¬ D.Mem := fun h hm => h ((mem_iff_accepts hG [[]]).mp hm)
  refine ⟨?_, ?_⟩
  · -- completeness: encode the complete table of `completeAt` in bits
    intro ha
    obtain ⟨pf, hpf⟩ := W.completeAt (good_instance hG [[]]) ((mem_iff_accepts hG [[]]).mpr ha)
    let L0 := W.VR.length
    let L1 := W.VH.length
    let LC := W.VI.length
    let target : ℕ → c.Fld := fun k =>
      if k < 2 ^ c.f then pf.p0 (c.elt k)
      else if h1 : k - 2 ^ c.f < L0 then pf.π0 ⟨k - 2 ^ c.f, h1⟩
      else if k - 2 ^ c.f - L0 < 2 ^ c.f then pf.p1 (c.elt (k - 2 ^ c.f - L0))
      else if h3 : k - 2 ^ c.f - L0 - 2 ^ c.f < L1 then pf.π1 ⟨k - 2 ^ c.f - L0 - 2 ^ c.f, h3⟩
      else if h4 : k - 2 ^ c.f - L0 - 2 ^ c.f - L1 < LC then pf.πc ⟨k - 2 ^ c.f - L0 - 2 ^ c.f - L1, h4⟩
      else 0
    let w : ℕ → ℕ := fun k => (request c xs [[]]).wordOf (RingHom.id c.Fld) (target k)
    let π : ℕ → Bool := fun a => (w (a / c.f)).testBit (a % c.f)
    have hf0 : 0 < c.f := by omega
    have hword : ∀ k, (request c xs [[]]).wordAt π k = w k := by
      intro k
      unfold Request.wordAt
      rw [bitsValue_range_map]
      have hb : (fun j : Fin (request c xs [[]]).code.f => π (k * (request c xs [[]]).code.f + j.val)) =
          bitsOf c.f (w k) := by
        funext j
        have hj : j.val < c.f := j.isLt
        have h1 : (k * c.f + j.val) / c.f = k := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hf0, Nat.div_eq_of_lt hj, zero_add]
        have h2 : (k * c.f + j.val) % c.f = j.val := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
        simp only [π, bitsOf]
        show (w ((k * c.f + j.val) / c.f)).testBit ((k * c.f + j.val) % c.f) = _
        rw [h1, h2]
      rw [hb]
      exact maskOfBits_bitsOf c.f _ (wordOf_lt c xs [[]] _)
    have helt : ∀ k, (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π k) = target k := by
      intro k
      rw [hword]
      exact elt_wordOf c xs [[]] hp _
    have hwo : ∀ a : c.Fld, (request c xs [[]]).wordOf (RingHom.id c.Fld) a < 2 ^ c.f := wordOf_lt c xs [[]]
    have hew : ∀ a : c.Fld, c.elt ((request c xs [[]]).wordOf (RingHom.id c.Fld) a) = a := elt_wordOf c xs [[]] hp
    have hL0 : L0 = ((request c xs [[]]).vR (RingHom.id c.Fld)).length := rfl
    have hL1 : L1 = ((request c xs [[]]).vH (RingHom.id c.Fld)).length := rfl
    have hLC : LC = ((request c xs [[]]).vI (RingHom.id c.Fld)).length := rfl
    have hdec : dec π = pf := by
      obtain ⟨p0, π0, p1, π1, πc⟩ := pf
      simp only [dec]
      congr 1
      · funext α
        have h0 := hwo α
        show (request c xs [[]]).elt (RingHom.id c.Fld)
          ((request c xs [[]]).wordAt π ((request c xs [[]]).wordOf (RingHom.id c.Fld) α)) = p0 α
        rw [helt]
        simp only [target]
        split_ifs
        · exact congrArg p0 (hew α)
      · funext t
        have ht := t.isLt
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π (2 ^ c.f + t.val)) = π0 t
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp only; omega)
      · funext α
        have h0 := hwo α
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π
          (2 ^ c.f + L0 + (request c xs [[]]).wordOf (RingHom.id c.Fld) α)) = p1 α
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | skip
        rw [show 2 ^ c.f + L0 + (request c xs [[]]).wordOf (RingHom.id c.Fld) α - 2 ^ c.f - L0 =
          (request c xs [[]]).wordOf (RingHom.id c.Fld) α by omega]
        exact congrArg p1 (hew α)
      · funext t
        have ht := t.isLt
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π
          (2 * 2 ^ c.f + L0 + t.val)) = π1 t
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp only; omega)
      · funext t
        have ht := t.isLt
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π
          (2 * 2 ^ c.f + L0 + L1 + t.val)) = πc t
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp only; omega)
    refine ⟨π, fun R => ?_⟩
    rw [accepts_eq hG, hacc, hdec]
    exact hpf _ _ _ _ _ _
  · -- soundness
    intro hna π
    have hfun : (fun R : Fin (r0 c) → Bool => SingleRun.accepts c xs π (List.ofFn R)) =
        W.acceptsAt (r0 c) hR hH hf hI (dec π) := by
      funext R
      rw [accepts_eq hG, hacc]
      congr 1
      funext i
      exact getD_ofFn R i
    rw [hfun]
    refine (W.soundAt (r0 c) hR hH hf hI (good_instance hG [[]]) (hnot hna) (dec π)).trans ?_
    have hu := uniform_rejection c.f D.cN (max Kc 1) (by omega) (Good.cN_pos hG) (le_max_right _ _)
      (hG.cN_le.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
    have hK : K = soundTerm 2 4 0 1 c.f := by
      show soundTerm tuple0.η tuple0.κ0 tuple0.γ tuple0.μ (monoBasis c).length = _
      rw [hlenB]; rfl
    rw [hK]
    linarith

/-! ## The lengths of the three proximity proofs and `L_π` -/

section Lengths

variable (c : Instance) (xs : List Bool) (S : List (List Bool)) [Fact (Irreducible c.irrPoly)] [DecidableEq c.Fld]

theorem vR_length : ((request c xs S).vR (RingHom.id c.Fld)).length = len0 c := by
  show (vRS tuple0 (monoBasis c) 0 (2 ^ c.mH - 1)).length = _
  rw [vRS_length_eq, length_monoBasis]; rfl

theorem vH_length : ((request c xs S).vH (RingHom.id c.Fld)).length = len1 c := by
  show (vVRS tuple0 (monoBasis c) 0 (c.hBasis.map c.elt) (c.elt c.hOffset) (dH c)).length = _
  rw [vVRS_length_eq, length_monoBasis, List.length_map]; rfl

theorem vI_length : ((request c xs S).vI (RingHom.id c.Fld)).length = lenC c := by
  show (vVRS tuple0 (monoBasis c) 0 (c.iBasis.map c.elt) (c.elt c.iOffset) (2 ^ c.mH - 1)).length = _
  rw [vVRS_length_eq, length_monoBasis, List.length_map]; rfl

/-- The number `L_π` of the join is `Request.proofBits` of `Joins/SingleRun.lean` at `φ = id`. -/
theorem proofBits_eq : (request c xs S).proofBits (RingHom.id c.Fld) = proofBits c := by
  unfold Request.proofBits proofBits
  rw [vR_length, vH_length, vI_length]
  rfl

theorem vR_rand : ((request c xs S).vR (RingHom.id c.Fld)).rand ≤ r0 c := by
  show (vRS tuple0 (monoBasis c) 0 (2 ^ c.mH - 1)).rand ≤ r0 c
  rw [vRS_rand_eq, length_monoBasis]; unfold r0; omega

theorem vH_rand : ((request c xs S).vH (RingHom.id c.Fld)).rand ≤ r0 c := by
  show (vVRS tuple0 (monoBasis c) 0 (c.hBasis.map c.elt) (c.elt c.hOffset) (dH c)).rand ≤ r0 c
  rw [vVRS_rand_eq, length_monoBasis, List.length_map, show c.hBasis.length = c.mH from rfl]; unfold r0; omega

theorem vI_rand : ((request c xs S).vI (RingHom.id c.Fld)).rand ≤ r0 c := by
  show (vVRS tuple0 (monoBasis c) 0 (c.iBasis.map c.elt) (c.elt c.iOffset) (2 ^ c.mH - 1)).rand ≤ r0 c
  rw [vVRS_rand_eq, length_monoBasis, List.length_map, show c.iBasis.length = c.m from rfl]; unfold r0; omega

/-- **`V0` reads only the first `r_0` random bits** (Step 2: "All steps read prefixes of one random string"). -/
theorem runVerdict_coins (pf : (request c xs S).Table (RingHom.id c.Fld)) (ρ ρ' : ℕ → Bool)
    (h : ∀ i < r0 c, ρ i = ρ' i) :
    (request c xs S).runVerdict (RingHom.id c.Fld) pf ρ = (request c xs S).runVerdict (RingHom.id c.Fld) pf ρ' := by
  have e1 : (fun i : Fin ((request c xs S).vR (RingHom.id c.Fld)).rand => ρ i.val) = fun i => ρ' i.val :=
    funext fun i => h _ (lt_of_lt_of_le i.isLt (vR_rand c xs S))
  have e2 : (fun i : Fin ((request c xs S).vH (RingHom.id c.Fld)).rand => ρ i.val) = fun i => ρ' i.val :=
    funext fun i => h _ (lt_of_lt_of_le i.isLt (vH_rand c xs S))
  have e3 : (fun i : Fin ((request c xs S).vI (RingHom.id c.Fld)).rand => ρ i.val) = fun i => ρ' i.val :=
    funext fun i => h _ (lt_of_lt_of_le i.isLt (vI_rand c xs S))
  have hf : c.f ≤ r0 c := by unfold r0; omega
  have e4 : (request c xs S).consistPoint (RingHom.id c.Fld) ρ = (request c xs S).consistPoint (RingHom.id c.Fld) ρ' := by
    unfold Request.consistPoint
    congr 2
    apply List.map_congr_left
    intro b hb
    exact h b (lt_of_lt_of_le (List.mem_range.mp hb) hf)
  unfold Request.runVerdict
  rw [e1, e2, e3, e4]

end Lengths

/-! ## Step 2 (a): randomness and proof length at `κ = f` -/

theorem two_rpow_le (f : ℕ) (hf : 1 ≤ f) :
    2 ^ max (randEq tuple0 f) f ≤ 8 * f ^ 3 * 2 ^ f := by
  have h : ((max (randEq tuple0 f) f : ℕ) : ℝ) ≤ f + 3 * Real.logb 2 (2 * f) := rand_le_of_C1 f hf
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have h2f : (0 : ℝ) < 2 * f := by positivity
  have key : (2 : ℝ) ^ ((max (randEq tuple0 f) f : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((f : ℝ) + 3 * Real.logb 2 (2 * f)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast, mul_comm (3 : ℝ),
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) h2f] at key
  have : ((2 ^ max (randEq tuple0 f) f : ℕ) : ℝ) ≤ ((8 * f ^ 3 * 2 ^ f : ℕ) : ℝ) := by
    push_cast
    have : (2 * (f : ℝ)) ^ (3 : ℝ) = 8 * (f : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [this] at key
    linarith
  exact_mod_cast this

/-- **Step 2 (a) at `κ = f`**: `f ≤ r_0 ≤ f + 3 log₂(2f)`, `2^{r_0} ≤ 64·2^f·f^4`, `L_π ≤ 64·2^f·f^4`. -/
theorem singleRun_resources (hG : SingleRun.Good Kc c xs) :
    1 ≤ c.f ∧ c.f ≤ r0 c ∧ (r0 c : ℝ) ≤ c.f + 3 * Real.logb 2 (2 * c.f) ∧
      2 ^ r0 c ≤ 64 * 2 ^ c.f * c.f ^ 4 ∧ proofBits c ≤ 64 * 2 ^ c.f * c.f ^ 4 := by
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  have hf2 := Good.two_le_f hG
  have hmH := hG.mH_two_le
  have hmI := hG.m_lt
  have hlenB : (monoBasis c).length = c.f := length_monoBasis c
  have hrRS : ∀ d, randRS tuple0 c.f d ≤ max (randEq tuple0 c.f) c.f := by
    intro d
    have := vRS_rand_le tuple0 (monoBasis c) 0 d
    rwa [vRS_rand_eq, hlenB] at this
  have hrVRS : ∀ h d, randVRS tuple0 c.f h d ≤ max (randEq tuple0 c.f) c.f := by
    intro h d; unfold randVRS; have := hrRS (d - 2 ^ h); omega
  have hr0 : r0 c ≤ max (randEq tuple0 c.f) c.f := by
    unfold r0
    have := hrRS (2 ^ c.mH - 1); have := hrVRS c.mH (dH c); have := hrVRS c.m (2 ^ c.mH - 1)
    omega
  have hfr0 : c.f ≤ r0 c := by unfold r0; omega
  have hreal : ((max (randEq tuple0 c.f) c.f : ℕ) : ℝ) ≤ c.f + 3 * Real.logb 2 (2 * c.f) :=
    rand_le_of_C1 c.f (by omega)
  have h2 := two_rpow_le c.f (by omega)
  have hC : 2 ^ c.f + (4 + 1) * (2 ^ c.f + 2 * lengthEq tuple0 c.f) ≤ (3 * 4 + 4) * (2 ^ c.f * c.f ^ 3) :=
    length_le_of_C1 c.f (by omega)
  have hη : 2 ^ tuple0.η = 4 := by decide
  have hlRS : ∀ d, d < 2 ^ c.f → lenRS tuple0 c.f d ≤ (4 + 1) * (2 ^ c.f + 2 * lengthEq tuple0 c.f) := by
    intro d hd
    have := vRS_length_le tuple0 (monoBasis c) 0 d (by rwa [hlenB])
    rwa [vRS_length_eq, hlenB, hη] at this
  have hpowH : 2 ^ c.mH < 2 ^ c.f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hH1 : 1 ≤ 2 ^ c.mH := Nat.one_le_two_pow
  have hdH := (Good.dH_lt hG).1
  have hl0 : len0 c ≤ 16 * (2 ^ c.f * c.f ^ 3) := by
    have := hlRS (2 ^ c.mH - 1) (by omega); unfold len0; omega
  have hl1 : len1 c ≤ 16 * (2 ^ c.f * c.f ^ 3) := by
    have := hlRS (dH c - 2 ^ c.mH) (by omega); unfold len1 lenVRS; omega
  have hlC : lenC c ≤ 16 * (2 ^ c.f * c.f ^ 3) := by
    have hlt : 2 ^ c.mH - 1 - 2 ^ c.m < 2 ^ c.f := lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
    have := hlRS (2 ^ c.mH - 1 - 2 ^ c.m) hlt; unfold lenC lenVRS; omega
  have hf3 : 1 ≤ c.f ^ 3 := Nat.one_le_pow _ _ (by omega)
  refine ⟨by omega, hfr0, le_trans (by exact_mod_cast hr0) hreal, ?_, ?_⟩
  · calc 2 ^ r0 c ≤ 2 ^ max (randEq tuple0 c.f) c.f := Nat.pow_le_pow_right (by norm_num) hr0
      _ ≤ 8 * c.f ^ 3 * 2 ^ c.f := h2
      _ ≤ 64 * 2 ^ c.f * c.f ^ 4 := by
        have : c.f ^ 3 ≤ c.f ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
        nlinarith [Nat.one_le_two_pow (n := c.f)]
  · unfold proofBits
    have hP : 2 ^ c.f ≤ 2 ^ c.f * c.f ^ 3 := Nat.le_mul_of_pos_right _ hf3
    have : c.f * (2 ^ c.f * c.f ^ 3) = 2 ^ c.f * c.f ^ 4 := by ring
    nlinarith

/-! ## `V0` reads only the `L_π` proof bits and the first `r_0` random bits -/

theorem decode_local (hG : SingleRun.Good Kc c xs) (S : List (List Bool)) [Fact (Irreducible c.irrPoly)]
    [DecidableEq c.Fld] (π π' : ℕ → Bool) (hπ : ∀ a < proofBits c, π a = π' a) :
    (request c xs S).decode (RingHom.id c.Fld) π = (request c xs S).decode (RingHom.id c.Fld) π' := by
  have hf2 := Good.two_le_f hG
  have hk : ∀ k < 2 * 2 ^ c.f + len0 c + len1 c + lenC c,
      (request c xs S).wordAt π k = (request c xs S).wordAt π' k := by
    intro k hk
    unfold Request.wordAt
    congr 1
    apply List.map_congr_left
    intro b hb
    have hb' : b < c.f := List.mem_range.mp hb
    apply hπ
    unfold proofBits
    calc k * c.f + b < (k + 1) * c.f := by rw [Nat.succ_mul]; omega
      _ ≤ (2 * 2 ^ c.f + len0 c + len1 c + lenC c) * c.f := Nat.mul_le_mul_right _ hk
  have hwo := wordOf_lt c xs S
  have hpw : 2 ^ (request c xs S).code.f = 2 ^ c.f := rfl
  have h0 := vR_length c xs S
  have h1 := vH_length c xs S
  unfold Request.decode
  congr 1
  · funext a; have := hwo a; rw [hk _ (by omega)]
  · funext t; have := t.isLt; rw [hk _ (by omega)]
  · funext a; have := hwo a; rw [hk _ (by omega)]
  · funext t; have := t.isLt; rw [hk _ (by omega)]
  · funext t; have := t.isLt; have := vI_length c xs S; rw [hk _ (by omega)]

theorem accepts_local (hG : SingleRun.Good Kc c xs) (π π' : ℕ → Bool) (hπ : ∀ a < proofBits c, π a = π' a)
    (R : List Bool) : SingleRun.accepts c xs π R = SingleRun.accepts c xs π' R := by
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  rw [accepts_eq hG, accepts_eq hG, decode_local hG [[]] π π' hπ]

theorem accepts_coins (hG : SingleRun.Good Kc c xs) (π : ℕ → Bool) (R R' : List Bool)
    (h : ∀ i < r0 c, R.getD i false = R'.getD i false) :
    SingleRun.accepts c xs π R = SingleRun.accepts c xs π R' := by
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  rw [accepts_eq hG, accepts_eq hG]
  exact runVerdict_coins c xs [[]] _ _ _ h

/-! ## The join -/

/-- **`Joins.SingleRunVerifier` from BCGT13 Theorem 11.1** (proof of `thm:short-pcp-ours`, Step 2):
`K1 = 120·max(Kc, 1)`, `b1 = 37`, `K = 64`, `b = 4`. -/
theorem singleRunVerifier (h11 : BCGT13_Theorem11_1) : SingleRunVerifier := by
  intro Kc
  refine ⟨120 * max Kc 1, 37, 64, 4, by omega, fun c xs hG => ?_⟩
  obtain ⟨hc, hs⟩ := singleRun_core h11 hG
  obtain ⟨h1, h2, h3, h4, h5⟩ := singleRun_resources hG
  exact ⟨hc, hs, accepts_coins hG, accepts_local hG, h1, h2, h3, h4, h5⟩

end NearCubicGates.Adapters.ShortPCP.Verifier
