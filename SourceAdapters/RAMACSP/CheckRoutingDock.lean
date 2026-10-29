import SourceAdapters.RAMACSP.PackInstance
import NineInputs

/-!
# Consumer dock of the `AffineRouting` join (assembly side)

Paper: `thm:embedding` and `app:affine-embedding`, Input subspace.
A satisfying table gives one permutation of whole records; conversely the
permutation can be routed while preserving every non-routing point, then
interpolated by one polynomial of degree less than `2^mH`. The input subspace
puts the bits of x̄ in the value slots of the input records.

This file specializes the join's generic characteristic-two field to the instance's `Field2 irr` (Shoup's modulus),
its layout to `app:affine-embedding`'s numbers (`PackInstance.ownLayout`) and its basis to the instance's `H` basis (`e_b = α^b`), and
states each use the assembly makes of the contract, with proofs from the contract fields:
- `monoBasis_independent`: `app:affine-embedding` These monomials are `F₂`-independent (input of every field lemma);
- `hElt_eq_cubeEval`: the instance's `H` (masks `2^b`, offset `0`) is the join's cube;
- `dock_soundness`: routing restriction of `P` vanishing on `H` ⟹ one permutation of whole `C`-column records;
- `dock_completion`: endpoint records related by a permutation ⟹ a routed table preserving every non-routing point,
  and one interpolating polynomial of degree `< 2^{mH}`;
- `dock_input`: the instance's `i`-th element of `I_m` is the `va` slot `i mod w` of input record `⌊i/w⌋`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters
open NearCubicWires NearCubicWires.RepairOrdinary Polynomial

/-! ## The field `Field2 irr` as a characteristic-two field -/

section Field

/-- A field `F₂[x]/(p)` has characteristic two. -/
instance charP_adjoinRoot (p : (ZMod 2)[X]) [Fact (Irreducible p)] : CharP (AdjoinRoot p) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot p)).injective 2

variable (irr : (ZMod 2)[X]) [Fact (Irreducible irr)]

/-- The monomial basis `e_b = α^b` (`app:affine-embedding`), `α` the root of `irr`. -/
def monoBasis (m : ℕ) : Fin m → Field2 irr := fun b => AdjoinRoot.root irr ^ b.val

theorem elt_two_pow (b : ℕ) : elt irr (WireExponent3_5.GF.toPoly (2 ^ b)) = AdjoinRoot.root irr ^ b := by
  rw [elt, WireExponent3_5.GF.toPoly_two_pow, map_pow, AdjoinRoot.mk_X]

/-- The polynomial `Σ_{b : v_b} X^b` of a Boolean coefficient vector. -/
def cubePoly (m : ℕ) (v : Fin m → Bool) : (ZMod 2)[X] :=
  ∑ b : Fin m, Polynomial.C (if v b then (1 : ZMod 2) else 0) * X ^ (b : ℕ)

theorem cubeEval_eq_mk (m : ℕ) (v : Fin m → Bool) :
    Routing.cubeEval m (monoBasis irr m) v = AdjoinRoot.mk irr (cubePoly m v) := by
  unfold Routing.cubeEval cubePoly monoBasis
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [AdjoinRoot.mk_X]

theorem cubePoly_coeff (m : ℕ) (v : Fin m → Bool) (b : Fin m) :
    (cubePoly m v).coeff b = if v b then 1 else 0 := by
  unfold cubePoly
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single b]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro c _ hcb
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h; exact hcb (Fin.ext h.symm)
  · simp

/-- **`H` is independent** (`app:affine-embedding`; the instance conditions of `def:acsp`): for `m ≤ deg irr`, distinct coefficient vectors give distinct
elements. -/
theorem monoBasis_independent (m : ℕ) (hm : m ≤ irr.natDegree) :
    Routing.Independent m (monoBasis irr m) := by
  intro v w h
  rw [cubeEval_eq_mk, cubeEval_eq_mk, AdjoinRoot.mk_eq_mk] at h
  have hv : (cubePoly m v).degree < m := Polynomial.degree_sum_fin_lt _
  have hw : (cubePoly m w).degree < m := Polynomial.degree_sum_fin_lt _
  have hirr : irr ≠ 0 := (Fact.out : Irreducible irr).ne_zero
  have hdeg : (cubePoly m v - cubePoly m w).degree < irr.degree := by
    rw [Polynomial.degree_eq_natDegree hirr]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (hv.trans_le (by exact_mod_cast hm)) (hw.trans_le (by exact_mod_cast hm)))
  have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt h hdeg
  funext b
  have hc := congrArg (fun p => Polynomial.coeff p b) (sub_eq_zero.mp h0)
  simp only [cubePoly_coeff] at hc
  cases hvb : v b <;> cases hwb : w b <;> simp_all

end Field

/-! ## The specialization used by the assembly -/

section Dock

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate) (r : ClockRequest)

/-- The instance's modulus as a polynomial. -/
abbrev ownIrr : (ZMod 2)[X] := (ownInst V irrPoly cons r).irrPoly

theorem ownInst_irrPoly : (ownInst V irrPoly cons r).irrPoly =
    WireExponent3_5.GF.toPoly (modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2)) := by
  rfl

theorem ownIrr_eq (hdeg : (irrPoly (fieldExp V r.2)).natDegree = fieldExp V r.2) :
    ownIrr V irrPoly cons r = irrPoly (fieldExp V r.2) := by
  rw [ownIrr, ownInst_irrPoly]
  apply WireExponent3_5.GF.toPoly_ofPoly
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by rw [hdeg]; exact_mod_cast Nat.lt_succ_self _)

/-- The Shoup choice makes the instance's modulus irreducible of degree `f` (`lem:generator` (irreducible-polynomial generation); the instance conditions of `def:acsp`). -/
theorem ownIrr_irreducible (hI : Published.Shoup.IrreducibleChoice irrPoly) :
    Irreducible (ownIrr V irrPoly cons r) ∧ (ownIrr V irrPoly cons r).natDegree = fieldExp V r.2 := by
  have hf : 1 ≤ fieldExp V r.2 := by have := domExp_add_two_le_fieldExp V r.2; omega
  obtain ⟨h1, h2⟩ := hI _ hf
  rw [ownIrr_eq V irrPoly cons r h2]
  exact ⟨h1, h2⟩

theorem ownInst_hBasis_getD (j : ℕ) (hj : j < domExp V r.2) :
    (ownInst V irrPoly cons r).hBasis.getD j 0 = 2 ^ j := by
  simp [ownInst, List.getD_eq_getElem?_getD, hj]

theorem ownInst_mH : (ownInst V irrPoly cons r).mH = (ownLayout V r.2).m := by
  simp [ACSP.Affine.Instance.mH, ownInst, ownLayout_m]

/-- The `Fact` that the instance's modulus is irreducible (from Shoup's choice). -/
theorem ownIrr_fact (hI : Published.Shoup.IrreducibleChoice irrPoly) : Fact (Irreducible (ownIrr V irrPoly cons r)) :=
  ⟨(ownIrr_irreducible V irrPoly cons r hI).1⟩

variable [Fact (Irreducible (ownIrr V irrPoly cons r))]

/-- `H`'s basis is the join's `e_b = α^b` at `mH = (ownLayout).m`. -/
abbrev ownBasis : Fin (ownLayout V r.2).m → Field2 (ownIrr V irrPoly cons r) :=
  monoBasis (ownIrr V irrPoly cons r) (ownLayout V r.2).m


/-- The instance's `H` element of a coefficient vector is the join's cube element (`hBasis` masks `2^b`, offset
`0`). -/
theorem hElt_eq_cubeEval (coeff : Fin (ownLayout V r.2).m → Bool) :
    (ownInst V irrPoly cons r).hElt (fun b => coeff (Fin.cast (ownInst_mH V irrPoly cons r) b)) =
      Routing.cubeEval (ownLayout V r.2).m (ownBasis V irrPoly cons r) coeff := by
  unfold ACSP.Affine.Instance.hElt affineElt
  have h0 : elt (ownIrr V irrPoly cons r)
      (WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).hOffset) = 0 := by
    simp [ownInst, elt, WireExponent3_5.GF.toPoly]
  rw [h0, zero_add]
  unfold Routing.cubeEval
  refine Fintype.sum_equiv (finCongr (ownInst_mH V irrPoly cons r)) _ _ fun b => ?_
  have hb : b.val < domExp V r.2 := lt_of_lt_of_eq b.isLt (ownInst_mH V irrPoly cons r)
  have e : (ownInst V irrPoly cons r).hBasisPoly b = WireExponent3_5.GF.toPoly (2 ^ b.val) := by
    unfold ACSP.Affine.Instance.hBasisPoly
    rw [ownInst_hBasis_getD V irrPoly cons r b.val hb]
  rw [e, elt_two_pow]
  simp only [monoBasis, finCongr_apply, Fin.val_cast]

variable (hI : Published.Shoup.IrreducibleChoice irrPoly)
include hI

theorem ownBasis_independent : Routing.Independent (ownLayout V r.2).m (ownBasis V irrPoly cons r) := by
  obtain ⟨-, h2⟩ := ownIrr_irreducible V irrPoly cons r hI
  refine monoBasis_independent _ _ ?_
  rw [h2, ownLayout_m]
  have := domExp_add_two_le_fieldExp V r.2
  omega

/-- **Dock: routing soundness** (`thm:embedding` SOUNDNESS). If the routing part of the emitted constraint vanishes on `H`,
there is ONE permutation of the `N` lanes carrying every whole `C`-column record of the first data stage to the
last. -/
theorem dock_soundness (hR : Joins.AffineRouting)
    (coords : Routing.Coordinates (ownLayout V r.2).m (ownBasis V irrPoly cons r))
    (a : Field2 (ownIrr V irrPoly cons r) → Field2 (ownIrr V irrPoly cons r)) :
    (∀ z, Routing.InH _ (ownBasis V irrPoly cons r) z →
      Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly cons r) a z
        (Routing.emit coords (Routing.routingTerms (ownLayout V r.2))) = 0) →
    ∃ π : Equiv.Perm (Routing.Lane (ownLayout V r.2).k), ∀ x c,
      Routing.dataValue (ownLayout V r.2) (ownBasis V irrPoly cons r) a
        (Routing.switchCount (ownLayout V r.2).k) (π x) c =
      Routing.dataValue (ownLayout V r.2) (ownBasis V irrPoly cons r) a 0 x c := by
  intro h
  have C := hR (Field2 (ownIrr V irrPoly cons r))
  have hInd := ownBasis_independent V irrPoly cons r hI
  exact C.soundness _ _ hInd a ((C.polynomial _ _ hInd coords a).mp h)

/-- **Routing completion and interpolation** (the completeness direction of `thm:embedding`).
Endpoint records related by a permutation and any background table give a routed table that agrees
with the background off the routing data/switch points, and a polynomial of degree `< 2^{mH}`
that agrees with that table on `H`. -/
theorem dock_completion (hR : Joins.AffineRouting)
    (U W : Routing.Lane (ownLayout V r.2).k → Fin (ownLayout V r.2).C → Field2 (ownIrr V irrPoly cons r))
    (hU : ∀ x c, Routing.IsBit (U x c))
    (hW : ∀ x c, Routing.IsBit (W x c))
    (hπ : ∃ π : Equiv.Perm (Routing.Lane (ownLayout V r.2).k), ∀ x c, W (π x) c = U x c)
    (background : Field2 (ownIrr V irrPoly cons r) → Field2 (ownIrr V irrPoly cons r)) :
    ∃ a : Field2 (ownIrr V irrPoly cons r) → Field2 (ownIrr V irrPoly cons r),
      Routing.LocalRouting (ownLayout V r.2) (ownBasis V irrPoly cons r) a ∧
      (∀ x c, Routing.dataValue (ownLayout V r.2) (ownBasis V irrPoly cons r) a 0 x c = U x c) ∧
      (∀ x c, Routing.dataValue (ownLayout V r.2) (ownBasis V irrPoly cons r) a
        (Routing.switchCount (ownLayout V r.2).k) x c = W x c) ∧
      (∀ z, ¬ Routing.RoutingWritable (ownLayout V r.2) (ownBasis V irrPoly cons r) z → a z = background z) ∧
      ∃ A : (Field2 (ownIrr V irrPoly cons r))[X],
        A.degree < ((2 ^ (ownInst V irrPoly cons r).hBasis.length : ℕ) : WithBot ℕ) ∧
        ∀ z, Routing.InH _ (ownBasis V irrPoly cons r) z → A.eval z = a z := by
  have C := hR (Field2 (ownIrr V irrPoly cons r))
  have hInd := ownBasis_independent V irrPoly cons r hI
  obtain ⟨a, h1, h2, h3, h4⟩ := C.completion _ _ hInd U W hU hW hπ background
  obtain ⟨A, hA, hAa⟩ := C.interpolation _ _ hInd a
  refine ⟨a, h1, h2, h3, h4, A, ?_, hAa⟩
  have hl : (ownInst V irrPoly cons r).hBasis.length = (ownLayout V r.2).m := by
    simp [ownInst, ownLayout_m]
  rw [hl]; exact hA

/-! ### The input clause -/

omit hI in
theorem maskEval_two_pow (b : ℕ) (hb : b < (ownLayout V r.2).m) :
    Routing.maskEval (ownLayout V r.2).m (ownBasis V irrPoly cons r) (2 ^ b) = AdjoinRoot.root _ ^ b := by
  unfold Routing.maskEval
  rw [Finset.sum_eq_single ⟨b, hb⟩]
  · simp [monoBasis]
  · intro c _ hc
    rw [Nat.testBit_two_pow, if_neg]
    simp only [decide_eq_true_eq]
    intro h; exact hc (Fin.ext h.symm)
  · simp

omit [Fact (Irreducible (ownIrr V irrPoly cons r))] hI in
theorem ownInst_iOffset :
    WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).iOffset =
      WireExponent3_5.GF.toPoly (2 ^ tau V r.2) := rfl

omit [Fact (Irreducible (ownIrr V irrPoly cons r))] hI in
theorem ownInst_iBasis (j : ℕ) (hj : j < inExp V r) :
    (ownInst V irrPoly cons r).iBasisPoly j = WireExponent3_5.GF.toPoly
      (2 ^ (if j < wordExp V r.2 then laneExp V r.2 + stageExp V r.2 + j else j - wordExp V r.2)) := by
  unfold ACSP.Affine.Instance.iBasisPoly
  rw [ownInst_iBasis_list, inputBasisMasks]
  refine congrArg WireExponent3_5.GF.toPoly ?_
  rw [List.getD_eq_getElem?_getD]
  by_cases hjw : j < wordExp V r.2
  · rw [if_pos hjw, List.getElem?_append_left (by simpa using hjw), List.getElem?_map, List.getElem?_range hjw,
      Option.map_some, Option.getD_some]
  · rw [if_neg hjw, List.getElem?_append_right (by simp; omega)]
    have hj' : j - wordExp V r.2 < inExp V r - wordExp V r.2 := by
      have := wordExp_le_inExp V r
      omega
    simp only [List.length_map, List.length_range]
    rw [List.getElem?_map, List.getElem?_range hj', Option.map_some, Option.getD_some]

/-- **The input clause** (`app:affine-embedding`, “Input subspace”, and `def:acsp`). The instance's
`i`-th element of `I` (the point where `A(α_i) = x̄_i`) is bit `i mod w` of the `va` field (tag `0`)
of the input record on lane `T + ⌊i/w⌋`, stage `0`, role `0`, area `0`. -/
theorem dock_input_indexed (hR : Joins.AffineRouting) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) (i : ℕ)
    (hi : i < (ownXbar V r).length) :
    indexedElt (ownIrr V irrPoly cons r) (inExp V r)
      (ownInst V irrPoly cons r).iBasisPoly
      (WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).iOffset) i =
      Routing.label (ownLayout V r.2) (ownBasis V irrPoly cons r)
        (2 ^ tau V r.2 + i / 2 ^ wordExp V r.2) 0 (i % 2 ^ wordExp V r.2) 0 0 := by
  obtain ⟨hpow, _, hw, hlt, _⟩ := inExp_facts V r hn hnt
  have C := hR (Field2 (ownIrr V irrPoly cons r))
  have hInd := ownBasis_independent V irrPoly cons r hI
  have hk : (ownLayout V r.2).k - 1 = tau V r.2 := by simp [ownLayout, laneExp]
  have hmL : (ownLayout V r.2).m = laneExp V r.2 + stageExp V r.2 + colExp V r.2 + 4 := rfl
  obtain ⟨hpt, -, -⟩ := C.input _ _ hInd (wordExp V r.2) (inExp V r)
    (by show wordExp V r.2 ≤ colExp V r.2; unfold colExp; omega) hw (by rw [hk]; omega)
  have hi' : i < 2 ^ inExp V r := hpow ▸ hi
  rw [hk] at hpt
  rw [← hpt i hi']
  unfold indexedElt affineElt Routing.inputPoint
  rw [ownInst_iOffset V irrPoly cons r, elt_two_pow,
    maskEval_two_pow V irrPoly cons r ((ownLayout V r.2).k - 1) (by rw [hk, hmL]; unfold laneExp; omega), hk]
  refine congrArg (fun z : Field2 (ownIrr V irrPoly cons r) =>
    AdjoinRoot.root (ownIrr V irrPoly cons r) ^ tau V r.2 + z) (Finset.sum_congr rfl fun j _ => ?_)
  have hb := ownInst_iBasis V irrPoly cons r j j.isLt
  rw [hb, elt_two_pow (ownIrr V irrPoly cons r)]
  unfold Routing.inputBasis
  rw [maskEval_two_pow V irrPoly cons r
    (if j.val < wordExp V r.2 then (ownLayout V r.2).k + (ownLayout V r.2).ell + j.val else j.val - wordExp V r.2)
    (by rw [hmL]; show _ < laneExp V r.2 + stageExp V r.2 + colExp V r.2 + 4
        have := j.isLt; unfold colExp laneExp; split_ifs
        · show laneExp V r.2 + stageExp V r.2 + j.val < _; unfold laneExp; omega
        · omega)]
  rfl

/-- The direct instance input element has the literal input-record order. -/
theorem dock_input (hR : Joins.AffineRouting) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) (i : ℕ)
    (hi : i < (ownXbar V r).length) :
    (ownInst V irrPoly cons r).iElt i =
      Routing.label (ownLayout V r.2) (ownBasis V irrPoly cons r)
        (2 ^ tau V r.2 + i / 2 ^ wordExp V r.2) 0 (i % 2 ^ wordExp V r.2) 0 0 := by
  have hm := ownInst_m V irrPoly cons r
  exact (congrArg (fun m => indexedElt (ownIrr V irrPoly cons r) m
    (ownInst V irrPoly cons r).iBasisPoly
    (WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).iOffset) i) hm).trans
      (dock_input_indexed V irrPoly cons r hI hR hn hnt i hi)

end Dock

end NearCubicGates.Adapters.RAMACSP
