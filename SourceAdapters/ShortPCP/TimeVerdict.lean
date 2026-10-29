import SourceAdapters.ShortPCP.TimeVerifiers
import SourceAdapters.Joins.SingleRunTime
import Proof.Wire_3_5.GFBits

/-!
# Single-run time, reference layer 6: the verdict of the join in poly-time form

`Joins/SingleRunTime.lean` specifies the program's output as `Request.runVerdict` (`thm:short-pcp-ours`, Step 2: the three
single runs and the consistency test of Construction 8.5, on the proof table `decode o`). Here it is rewritten
(`runVerdict_eq`) as `runVerdictN`, which uses only:
* the poly-time sub-verifiers `vRSF`, `vVRSF` (`TimeVerifiers.lean`), on the domain basis `x^0, …, x^{f−1}` and the
  bases of `H` and `I` — all independent under `Request.Valid` (`indep_domBasis`, `indep_hB`, `indep_iB`);
* oracle words for the proof (`wordAt`), with the five-table layout of the join;
* `lagEval` for the low-degree extension `p_x` (`thm:short-pcp-ours`, Step 2, "The instance");
* the circuit values and the consistency point of the join (already straight-line computations).
This is the field-operation-level algorithm the machine layer implements.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Time

open Finset Polynomial NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun NearCubicWires.WireExponent3_5

/-! ## Flat verifiers with a non-dependent proof and coin function -/

section Flat

variable {F : Type} [Field F] [DecidableEq F]

/-- `FlatVerifier.answers` with the proof given on all indices (only `t < length` is read). -/
def answersN (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (πN : ℕ → F) (rl : List Bool) (i : ℕ) : F :=
  match V.Q rl i with
  | none => 0
  | some j =>
    if 1 ≤ j ∧ j ≤ 2 ^ B.length then p (eltWithIndex B O j)
    else if j - 2 ^ B.length - 1 < V.length ∧ 2 ^ B.length < j then πN (j - 2 ^ B.length - 1)
    else 0

/-- `FlatVerifier.accepts` on the coins `c 0, …, c (rand − 1)`. -/
def acceptsN (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (πN : ℕ → F) (c : ℕ → Bool) : Bool :=
  V.D ((List.range V.rand).map c) (answersN V B O p πN ((List.range V.rand).map c))

theorem ofFn_eq_range_map (n : ℕ) (c : ℕ → Bool) : List.ofFn (fun i : Fin n => c i.val) = (List.range n).map c := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

omit [DecidableEq F] in
theorem accepts_eq_acceptsN (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (πN : ℕ → F) (hπ : ∀ t (h : t < V.length), π ⟨t, h⟩ = πN t) (c : ℕ → Bool) :
    V.accepts B O p π (fun i => c i.val) = acceptsN V B O p πN c := by
  unfold FlatVerifier.accepts acceptsN
  rw [ofFn_eq_range_map]
  congr 1
  funext i
  unfold FlatVerifier.answers answersN
  cases V.Q ((List.range V.rand).map c) i with
  | none => rfl
  | some j =>
    simp only
    split_ifs with h1 h2 <;> first | rfl | exact hπ _ h2.1

end Flat

/-! ## The bases of `Request.Valid` are independent -/

section Bases

variable (q : Request) {F : Type} [Field F]
  (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)

include φ in
theorem charP_two : CharP F 2 := by
  refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
  have h2 : (2 : AdjoinRoot (GF.toPoly q.code.irr)) = 0 := by
    have e : (AdjoinRoot.of (GF.toPoly q.code.irr)) (2 : ZMod 2) = 2 := map_ofNat _ 2
    rw [← e, show (2 : ZMod 2) = 0 from rfl, map_zero]
  have := congrArg φ h2
  rwa [map_ofNat, map_zero] at this

theorem elt_eq (a : ℕ) : q.elt φ a = φ (AdjoinRoot.mk (GF.toPoly q.code.irr) (GF.toPoly a)) := rfl

theorem sel_map_elt (l : List ℕ) (v : ℕ) :
    sel (l.map (q.elt φ)) v =
      φ (∑ j : Fin l.length, if v.testBit j.val then AdjoinRoot.mk (GF.toPoly q.code.irr)
        (GF.toPoly (l.getD j.val 0)) else 0) := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, sel_cons, ih, List.length_cons, Fin.sum_univ_succ, map_add]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero, List.getD_cons_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, elt_eq]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Nat.testBit_div_two]

theorem sel_domList (hφ : Function.Bijective φ) :
    ∀ n v : ℕ, sel ((List.range n).map fun j => q.elt φ (2 ^ j)) v = q.elt φ (v % 2 ^ n)
  | 0, v => by simp [elt_eq, Nat.mod_one]
  | n + 1, v => by
    rw [List.range_succ, List.map_append, sel_append, sel_domList hφ n, List.length_map, List.length_range,
      List.map_singleton, sel_cons, sel_nil, add_zero, elt_eq, elt_eq, elt_eq, GF.toPoly_mod_two_pow_succ, map_add,
      map_add, GF.toPoly_two_pow]
    congr 1
    rw [Nat.testBit_eq_decide_div_mod_eq]
    split_ifs with h1 h2 h2 <;> simp_all

theorem eq_zero_of_testBit (v κ : ℕ) (hv : v < 2 ^ κ) (h : ∀ j < κ, v.testBit j = false) : v = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  rcases Nat.lt_or_ge j κ with hj | hj
  · exact h j hj
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))

theorem indep_domBasis (hv : q.Valid) (hφ : Function.Bijective φ) : Indep (q.domBasis φ) := by
  intro v hlt h0
  have hmod : GF.ModulusOk q.code.irr q.code.f := ⟨hv.1.1, hv.1.2.1⟩
  unfold Request.domBasis at h0 hlt
  rw [List.length_map, List.length_range] at hlt
  rw [sel_domList q φ hφ, Nat.mod_eq_of_lt hlt] at h0
  have h1 : q.elt φ v = q.elt φ 0 := by rw [h0, elt_eq]; simp
  exact GF.rep_injOn q.code.irr q.code.f v 0 hmod hlt (by positivity) (hφ.1 h1)

/-- An affinely independent word basis, as `Instance.IsValid` states it, gives an
independent list of field elements. -/
theorem indep_of_affine (hφ : Function.Bijective φ) (l : List ℕ) (o : ℕ)
    (h : NearCubicGates.Adapters.ACSP.AffineIndependent (GF.toPoly q.code.irr) l.length
      (fun j => GF.toPoly (l.getD j 0)) (GF.toPoly o)) : Indep (l.map (q.elt φ)) := by
  intro v hlt h0
  rw [List.length_map] at hlt
  rw [sel_map_elt] at h0
  have hz : (∑ j : Fin l.length, if v.testBit j.val then AdjoinRoot.mk (GF.toPoly q.code.irr)
      (GF.toPoly (l.getD j.val 0)) else 0) = 0 := hφ.1 (by rw [h0, map_zero])
  have hc := @h (fun j => v.testBit j.val) (fun _ => false) (by
    unfold NearCubicGates.Adapters.ACSP.affineElt NearCubicGates.Adapters.ACSP.elt
    rw [hz]; simp)
  apply eq_zero_of_testBit v l.length hlt
  intro j hj
  exact congrFun hc ⟨j, hj⟩

theorem indep_hB (hv : q.Valid) (hφ : Function.Bijective φ) : Indep (q.hB φ) := by
  have h := hv.2.1.2.1
  exact indep_of_affine q φ hφ q.code.hBasis q.code.hOffset h

theorem mI_eq (hv : q.Valid) : q.mI = q.code.m := by
  unfold Request.mI
  rw [hv.2.2.1, Nat.log_pow (by norm_num)]

theorem indep_iB (hv : q.Valid) (hφ : Function.Bijective φ) : Indep (q.iB φ) := by
  exact indep_of_affine q φ hφ q.code.iBasis q.code.iOffset hv.2.1.2.2.2.1.1

end Bases

/-! ## The verdict -/

section Verdict

variable (q : Request) {F : Type} [Field F] [DecidableEq F]
  (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)

/-- The low-degree extension of `x̄` over `I`, by Lagrange's formula. -/
def pxN (α : F) : F :=
  lagEval q.xbar.length (fun i => eltWithIndex (q.iB φ) (q.iO φ) (i + 1))
    (fun i => if q.xbar.getD i false then 1 else 0) α

/-- **`V0` on the proof the oracle encodes, in poly-time form** (field-operation level). -/
def runVerdictN (o : ℕ → Bool) (c : ℕ → Bool) : Bool :=
  let dom := q.domBasis φ
  let e := q.elt φ
  let nF := 2 ^ q.code.f
  let VR := vRSF dom 0 q.dA
  let VH := vVRSF dom 0 (q.hB φ) (q.hO φ) q.dB
  let VI := vVRSF dom 0 (q.iB φ) (q.iO φ) q.dA
  let p0 : F → F := fun a => e (q.wordAt o (q.wordOf φ a))
  let p1 : F → F := fun a => e (q.wordAt o (nF + VR.length + q.wordOf φ a))
  acceptsN VR dom 0 p0 (fun t => e (q.wordAt o (nF + t))) c &&
  acceptsN VH dom 0 p1 (fun t => e (q.wordAt o (2 * nF + VR.length + t))) c &&
  consist (q.acsp φ) p0 p1 (q.consistPoint φ c) &&
  acceptsN VI dom 0 (fun a => p0 a - pxN q φ a) (fun t => e (q.wordAt o (2 * nF + VR.length + VH.length + t))) c

theorem vR_eq (hv : q.Valid) (hφ : Function.Bijective φ) : q.vR φ = vRSF (q.domBasis φ) 0 q.dA := by
  haveI := charP_two q φ
  exact vRS_eq (indep_domBasis q φ hv hφ) 0 q.dA

theorem vH_eq (hv : q.Valid) (hφ : Function.Bijective φ) :
    q.vH φ = vVRSF (q.domBasis φ) 0 (q.hB φ) (q.hO φ) q.dB := by
  haveI := charP_two q φ
  exact vVRS_eq (indep_domBasis q φ hv hφ) 0 (indep_hB q φ hv hφ) _ _

theorem vI_eq (hv : q.Valid) (hφ : Function.Bijective φ) :
    q.vI φ = vVRSF (q.domBasis φ) 0 (q.iB φ) (q.iO φ) q.dA := by
  haveI := charP_two q φ
  exact vVRS_eq (indep_domBasis q φ hv hφ) 0 (indep_iB q φ hv hφ) _ _

/-- **The join's verdict is the poly-time verdict** (`thm:short-pcp-ours`, Step 2). -/
theorem runVerdict_eq (hv : q.Valid) (hφ : Function.Bijective φ) (o : ℕ → Bool) (c : ℕ → Bool) :
    q.runVerdict φ (q.decode φ o) c = runVerdictN q φ o c := by
  unfold Request.runVerdict runVerdictN
  rw [accepts_eq_acceptsN (q.vR φ) _ _ _ _ (fun t => q.elt φ (q.wordAt o (2 ^ q.code.f + t))) (fun _ _ => rfl),
    accepts_eq_acceptsN (q.vH φ) _ _ _ _
      (fun t => q.elt φ (q.wordAt o (2 * 2 ^ q.code.f + (q.vR φ).length + t))) (fun _ _ => rfl),
    accepts_eq_acceptsN (q.vI φ) _ _ _ _
      (fun t => q.elt φ (q.wordAt o (2 * 2 ^ q.code.f + (q.vR φ).length + (q.vH φ).length + t)))
      (fun _ _ => rfl)]
  have hpx : (q.acsp φ).px = pxN q φ := by
    funext α
    simp only [Request.acsp, Request.px, pxN, lagEval_eq]
  simp only [Request.decode, hpx, vR_eq q φ hv hφ, vH_eq q φ hv hφ, vI_eq q φ hv hφ]

end Verdict

end NearCubicGates.Adapters.ShortPCP.Time
