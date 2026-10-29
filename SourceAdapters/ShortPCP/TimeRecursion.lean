import SourceAdapters.ShortPCP.TimeBases

/-!
# Single-run time, reference layer 3: `Translate` and `D_{RS,=}` with poly(κ) field operations per level

BCGT13 §12.3.1 (`Translate`, `Q_{RS,=}`, `D_{RS,=}`) as transcribed in `PublishedStatements/BCGT13.lean`, for the
tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`, with the four exponential primitives replaced by their poly-time forms
(`TimeSubspace.lean`, `TimeBases.lean`): GetIndexOfElt of a random element is its coin value plus one, membership
`β ∈ L00` is the coin test `rv < 2`, `Z_{L0}` is evaluated by `zFast` (Algorithm 21's recursion), the column basis
is `zMulti B_{L0} B_{L1}` with offset `0`, and the index of a returned row point is `rowIdx`.

proof of `thm:short-pcp-ours`: "A single run of V_RS or V_VRS takes poly(f) field operations. Its recursion roughly halves the
dimension of the current affine subspace at each level and does poly(f) field operations per level". The theorems
`translate_eq` and `dEqF_eq` say that the poly-time recursions compute exactly the leaf's `Translate` and `D_{RS,=}`
on every independent basis (every basis reached from the domain `F` with its standard basis).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open Finset NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary

/-- The tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)` (pcpver G-P §1; the join's `tuple0`). -/
def T0 : Tuple := ⟨2, 4, 0, 1⟩

@[simp] theorem T0_η : T0.η = 2 := rfl
@[simp] theorem T0_κ0 : T0.κ0 = 4 := rfl
@[simp] theorem T0_γ : T0.γ = 0 := rfl
@[simp] theorem T0_μ : T0.μ = 1 := rfl

variable {F : Type} [Field F] [DecidableEq F]

/-- `Z_B(y)` by Algorithm 21's recursion (`|B|²` multiplications). -/
def zFast (B : List F) (y : F) : F := (zMulti B [y]).headD 0

omit [DecidableEq F] in
theorem zFast_eq [CharP F 2] (B : List F) (y : F) : zFast B y = zProd B y := by
  simp [zFast, zMulti_eq]

/-- `Translate` (§12.3.1), poly-time form. -/
def translateF : ℕ → List F → F → List Bool → ℕ → TrOut F
  | 0, B, O, _, i => .inp (eltWithIndex B O i) i
  | n + 1, B, O, r, i =>
    if B.length ≤ T0.κ0 then .inp (eltWithIndex B O i) i
    else
      let κ := B.length
      let k := κ / 2 - T0.γ
      let BL0 := B.take k
      let BL00 := B.take (k + T0.μ)
      let BL1 := B.drop k
      let nL := 2 ^ κ
      let nLb := 2 ^ (k + T0.μ + 1)
      let nL1 := 2 ^ BL1.length
      if r.head? = some false then
        let m := 1 + BL1.length
        let rv := bitsValue ((r.drop 1).take BL1.length)
        let β := sel BL1 rv + O
        let β' := zFast BL0 (β + O)
        let BLb := if rv < 2 then BL00 ++ [B.getD (k + T0.μ) 0] else BL00 ++ [β + O]
        match translateF n BLb O (r.drop m) i with
        | .inp α ι => if zFast BL0 (α + O) = β' then .inp α (rowIdx k rv ι) else .prf (nL + nLb * rv + ι)
        | .prf ι => .prf ((ι - nLb + nL) + nLb * nL1 + rv * lengthEq T0 (k + T0.μ + 1))
      else
        let m := 1 + (k + T0.μ)
        let av := bitsValue ((r.drop 1).take (k + T0.μ))
        let α := sel BL00 av + O
        let α' := zFast BL0 (α + O)
        let BZ := zMulti BL0 BL1
        match translateF n BZ 0 (r.drop m) i with
        | .inp β' ι => if α' = β' then .inp α (1 + av) else .prf (nL + nLb * (ι - 1) + (1 + av))
        | .prf ι => .prf ((ι - 2 ^ BZ.length + nL) + nLb * nL1 + nL1 * lengthEq T0 (k + T0.μ + 1) +
            av * lengthEq T0 BZ.length)

theorem indexOfElt_sel [CharP F 2] {B : List F} (hB : Indep B) (O : F) {v : ℕ} (hv : v < 2 ^ B.length) :
    indexOfElt B O (sel B v + O) = 1 + v := by
  have e : sel B v + O = eltWithIndex B O (1 + v) := by rw [eltWithIndex_eq, Nat.add_sub_cancel_left]
  rw [e, indexOfElt_eltWithIndex hB O _ (by omega) (by omega)]

/-- **`Translate` in poly-time form** (§12.3.1, proof of `thm:short-pcp-ours`): on an independent basis the poly-time recursion
is the leaf's, and every returned implicit-input point is the GetEltWithIndex of its returned index. -/
theorem translate_eq [CharP F 2] : ∀ (n : ℕ) (B : List F) (O : F) (r : List Bool) (i : ℕ), Indep B →
    Published.BCGT13.translate T0 n B O r i = translateF n B O r i ∧
      ∀ α j, translateF n B O r i = .inp α j → α = eltWithIndex B O j
  | 0, B, O, r, i, _ => by
    refine ⟨rfl, fun α j h => ?_⟩
    simp only [translateF, TrOut.inp.injEq] at h
    rw [← h.1, h.2]
  | n + 1, B, O, r, i, hB => by
    by_cases hκ : B.length ≤ 4
    · have e1 : translateF (n + 1) B O r i = .inp (eltWithIndex B O i) i := by simp [translateF, T0_κ0, hκ]
      refine ⟨by simp [Published.BCGT13.translate, translateF, T0_κ0, hκ], fun α j h => ?_⟩
      rw [e1, TrOut.inp.injEq] at h
      rw [← h.1, h.2]
    · have hk1 : B.length / 2 + 1 < B.length := by omega
      have h0 := indep_take hB (B.length / 2)
      have h00 := indep_take hB (B.length / 2 + 1)
      have h1 := indep_drop hB (B.length / 2) (by omega)
      have hl00 : (B.take (B.length / 2 + 1)).length = B.length / 2 + 1 := by simp; omega
      by_cases hr : r.head? = some false
      · -- the row test translation, steps (d) i–xi
        set rv := bitsValue ((r.drop 1).take (B.drop (B.length / 2)).length) with hrvdef
        have hrv : rv < 2 ^ (B.drop (B.length / 2)).length :=
          lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
        have hmem := mem_span_take_iff hB O (B.length / 2) hk1.le hrv
        have hidx := indexOfElt_sel h1 O hrv
        set BLb := (if rv < 2 then B.take (B.length / 2 + 1) ++ [B.getD (B.length / 2 + 1) 0]
          else B.take (B.length / 2 + 1) ++ [sel (B.drop (B.length / 2)) rv + O + O]) with hBLb
        have hIb : Indep BLb := by
          rw [hBLb]; split_ifs with h
          · rw [rowMem_eq B _ hk1]; exact indep_take hB _
          · have := indep_rowNew hB (B.length / 2) hk1 (by omega) hrv
            rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero, sel_drop B _ _ (by omega)]
        obtain ⟨ihe, ihi⟩ := translate_eq n BLb O (r.drop (1 + (B.drop (B.length / 2)).length)) i hIb
        have espec := rowIdx_spec O (B.length / 2) hk1 hrv
        simp only [] at espec
        rw [← hBLb] at espec
        constructor
        · simp only [Published.BCGT13.translate, translateF, T0_κ0, T0_γ, T0_μ, hκ, hr, if_false, if_true, Nat.sub_zero,
            getRandElt_eq, zFast_eq, zEval_eq h0, ← hrvdef, hmem, hidx, ← hBLb, ihe, Nat.add_sub_cancel_left]
          cases h : translateF n BLb O (r.drop (1 + (B.drop (B.length / 2)).length)) i with
          | inp α ι =>
            have hα := ihi α ι h
            have hj : indexOfElt B O α = rowIdx (B.length / 2) rv ι := by
              rw [hα, (espec ι).1]; exact indexOfElt_eltWithIndex hB O _ (espec ι).2.1 (espec ι).2.2
            simp only [hj]
          | prf ι => rfl
        · intro α j h
          simp only [translateF, T0_κ0, T0_γ, T0_μ, hκ, hr, if_false, if_true, Nat.sub_zero, zFast_eq, ← hrvdef,
            ← hBLb] at h
          cases h' : translateF n BLb O (r.drop (1 + (B.drop (B.length / 2)).length)) i with
          | inp α' ι =>
            rw [h'] at h
            simp only at h
            split_ifs at h with hz
            simp only [TrOut.inp.injEq] at h
            rw [← h.1, ← h.2, ihi α' ι h', (espec ι).1]
          | prf ι =>
            rw [h'] at h
            simp at h
      · -- the column test translation, steps (e) i–ix
        set av := bitsValue ((r.drop 1).take (B.length / 2 + 1)) with havdef
        have hav : av < 2 ^ (B.take (B.length / 2 + 1)).length := by
          rw [hl00]
          exact lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
        have hidx00 := indexOfElt_sel h00 O hav
        have hselB : sel (B.take (B.length / 2 + 1)) av = sel B av := by
          rw [sel_take, Nat.mod_eq_of_lt (by rw [hl00] at hav; exact hav)]
        have hidxB : indexOfElt B O (sel (B.take (B.length / 2 + 1)) av + O) = 1 + av := by
          rw [hselB]
          have hle : 2 ^ (B.take (B.length / 2 + 1)).length ≤ 2 ^ B.length := by
            rw [hl00]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
          exact indexOfElt_sel hB O (lt_of_lt_of_le hav hle)
        have hIZ := indep_zMulti hB (B.length / 2) (by omega)
        obtain ⟨ihe, ihi⟩ := translate_eq n (zMulti (B.take (B.length / 2)) (B.drop (B.length / 2))) 0
          (r.drop (1 + (B.length / 2 + 1))) i hIZ
        constructor
        · simp only [Published.BCGT13.translate, translateF, T0_κ0, T0_γ, T0_μ, hκ, hr, if_false, Nat.sub_zero, getRandElt_eq,
            zFast_eq, ← havdef]
          rw [colBasis_eq h0, zEval_offset h0]
          simp only [zEval_eq h0, ihe, hidx00, hidxB, Nat.add_sub_cancel_left]
          rfl
        · intro α j h
          simp only [translateF, T0_κ0, T0_γ, T0_μ, hκ, hr, if_false, Nat.sub_zero, zFast_eq, ← havdef] at h
          cases h' : translateF n (zMulti (B.take (B.length / 2)) (B.drop (B.length / 2))) 0
            (r.drop (1 + (B.length / 2 + 1))) i with
          | inp β' ι =>
            rw [h'] at h
            simp only at h
            split_ifs at h with hz
            simp only [TrOut.inp.injEq] at h
            rw [← h.1, ← h.2, eltWithIndex_eq, Nat.add_sub_cancel_left, hselB]
          | prf ι =>
            rw [h'] at h
            simp at h

/-- `D_{RS,=}` (§12.3.1, Algorithm 16), poly-time form, with the base-case degree test `bt` as a parameter
(supplied by `TimeDegree.lean`). -/
def dEqFF (bt : List F → F → ℕ → (ℕ → F) → Bool) : ℕ → List F → F → List Bool → (ℕ → F) → Bool
  | 0, B, O, _, ans => bt B O (dKE B.length T0.η) ans
  | n + 1, B, O, r, ans =>
    if B.length ≤ T0.κ0 then bt B O (dKE B.length T0.η) ans
    else
      let k := B.length / 2 - T0.γ
      let BL0 := B.take k
      let BL00 := B.take (k + T0.μ)
      let BL1 := B.drop k
      if r.head? = some false then
        let rv := bitsValue ((r.drop 1).take BL1.length)
        let BLb := if rv < 2 then BL00 ++ [B.getD (k + T0.μ) 0] else BL00 ++ [sel BL1 rv + O + O]
        dEqFF bt n BLb O (r.drop (1 + BL1.length)) ans
      else dEqFF bt n (zMulti BL0 BL1) 0 (r.drop (1 + (k + T0.μ))) ans

/-- **`D_{RS,=}` in poly-time form**: on an independent basis, given a base-case test that agrees with the leaf's
on independent bases. -/
theorem dEqF_eq [CharP F 2] (bt : List F → F → ℕ → (ℕ → F) → Bool)
    (hbt : ∀ (B : List F) (O : F) (d : ℕ) (ans : ℕ → F), Indep B → bt B O d ans = degreeTest B O d ans) :
    ∀ (n : ℕ) (B : List F) (O : F) (r : List Bool) (ans : ℕ → F), Indep B →
      dEqF T0 n B O r ans = dEqFF bt n B O r ans
  | 0, B, O, r, ans, hB => by simp only [dEqF, dEqFF, hbt B O _ ans hB]
  | n + 1, B, O, r, ans, hB => by
    by_cases hκ : B.length ≤ 4
    · simp only [dEqF, dEqFF, T0_κ0, hκ, if_true, hbt B O _ ans hB]
    · have hk1 : B.length / 2 + 1 < B.length := by omega
      have h0 := indep_take hB (B.length / 2)
      by_cases hr : r.head? = some false
      · set rv := bitsValue ((r.drop 1).take (B.drop (B.length / 2)).length) with hrvdef
        have hrv : rv < 2 ^ (B.drop (B.length / 2)).length :=
          lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
        have hmem := mem_span_take_iff hB O (B.length / 2) hk1.le hrv
        set BLb := (if rv < 2 then B.take (B.length / 2 + 1) ++ [B.getD (B.length / 2 + 1) 0]
          else B.take (B.length / 2 + 1) ++ [sel (B.drop (B.length / 2)) rv + O + O]) with hBLb
        have hIb : Indep BLb := by
          rw [hBLb]; split_ifs with h
          · rw [rowMem_eq B _ hk1]; exact indep_take hB _
          · have := indep_rowNew hB (B.length / 2) hk1 (by omega) hrv
            rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero, sel_drop B _ _ (by omega)]
        have ih := dEqF_eq bt hbt n BLb O (r.drop (1 + (B.drop (B.length / 2)).length)) ans hIb
        simp only [dEqF, dEqFF, T0_κ0, T0_γ, T0_μ, hκ, hr, if_false, if_true, Nat.sub_zero, getRandElt_eq,
          ← hrvdef, hmem, ← hBLb, ih]
      · have hIZ := indep_zMulti hB (B.length / 2) (by omega)
        have ih := dEqF_eq bt hbt n (zMulti (B.take (B.length / 2)) (B.drop (B.length / 2))) 0
          (r.drop (1 + (B.length / 2 + 1))) ans hIZ
        simp only [dEqF, dEqFF, T0_κ0, T0_γ, T0_μ, hκ, hr, if_false, Nat.sub_zero]
        rw [colBasis_eq h0, zEval_offset h0, ih]

end NearCubicGates.Adapters.ShortPCP.Time
