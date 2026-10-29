import SourceAdapters.ShortPCP.Machines.FLangLevels
import SourceAdapters.ShortPCP.Machines.FieldCellsProof

/-!
# Single-run time, machine layer 14: Lagrange evaluation

`Time.lagEval m pt val x = Σ_{i<m} val i · Π_{j<m, j≠i} (pt i − pt j)⁻¹ (x − pt j)` is the base-case degree test of
`D_{RS,=}` and `D_RS` (`Time.degreeTestF`, Algorithm 23) and the low-degree extension `p_x` of the instance (proof of `thm:short-pcp-ours`: "By Lagrange interpolation over the subspace `I` of size `|x̄|`, each evaluation takes `O(|x̄|²)` field
operations"). `lagP` computes it from packed lists of points (`49`) and values (`50`), `m` in `51`, `x` in `52`, into
`53` (scratch `45`, `46`, `54`, `55`); the inverse is the power `2^f − 2` (`Machines.inv_of_pow`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time

variable (G : Glob)

theorem mulW_lt (p ℓ a b : ℕ) : mulW p ℓ a b < 2 ^ ℓ := redW_lt _ _ _
theorem powW_lt (p ℓ a e : ℕ) : powW p ℓ a e < 2 ^ ℓ := redW_lt _ _ _

theorem ev_one {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) : ev φ 1 = 1 := by
  have : GF.toPoly 1 = 1 := by simp [GF.toPoly]
  simp [ev, GF.rep, this]

/-- The field inverse of a nonzero reduced word is its power `2^f − 2`. -/
theorem ev_inv {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (ℓ a : ℕ)
    (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hirr : Irreducible (GF.toPoly p)) (ha : a < 2 ^ ℓ) (ha0 : a ≠ 0) :
    ev φ (powW p ℓ a (2 ^ ℓ - 2)) = (ev φ a)⁻¹ := by
  rw [ev_powW φ ℓ a _ hp]
  apply eq_inv_of_mul_eq_one_left
  have h := inv_of_pow p ℓ a hp hℓ hirr ha ha0
  have := congrArg φ h
  rwa [map_mul, map_pow, map_one] at this

/-- The inner factor for `j ≠ i`, `46 := 46 · (pt i + pt j)^{-1} (x + pt j)`, with `pt i` in `45`. -/
def lagInner : S :=
  .ite (.eq (.v 55) (.v 54)) .skip
    (.set 46 (.fmul (.v 46) (.fmul (.finv (.fadd (.v 45) (getW 49 (.v 55)))) (.fadd (.v 52) (getW 49 (.v 55))))))

/-- One term `i` (index `54`): `45 := pt i`, `46 := Π_{j≠i} …`, `53 += val i · 46`. -/
def lagTerm : S :=
  .seq (.set 45 (getW 49 (.v 54))) (.seq (.set 46 (.k 1)) (.seq (.loop 55 (.v 51) lagInner)
    (.set 53 (.fadd (.v 53) (.fmul (getW 50 (.v 54)) (.v 46))))))

/-- **Lagrange evaluation** into `53`. -/
def lagP : S := .seq (.set 53 (.k 0)) (.loop 54 (.v 51) lagTerm)

/-- The variables `lagP` writes. -/
def lagW : List Var := [45, 46, 53, 54, 55]

theorem prod_ite_erase {F : Type} [Field F] (m i : ℕ) (hi : i < m) (g : ℕ → F) :
    ∏ j ∈ Finset.range m, (if j = i then 1 else g j) = ∏ j ∈ (Finset.range m).erase i, g j := by
  rw [← Finset.mul_prod_erase (Finset.range m) _ (Finset.mem_range.mpr hi), if_pos rfl, one_mul]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj)]

/-- **Lagrange evaluation** (`Time.lagEval`) on packed points and values with distinct points. -/
theorem lagP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (pts vals : List ℕ) (m : ℕ) (hpw : ∀ a ∈ pts, a < 2 ^ s.fl) (hvw : ∀ a ∈ vals, a < 2 ^ s.fl)
    (h49 : s.env 49 = packW s.fl pts) (h50 : s.env 50 = packW s.fl vals) (h51 : s.env 51 = m)
    (h52 : s.env 52 < 2 ^ s.fl) (h23 : s.env 23 = s.fl) (hok : fieldOk G s.fl s.fp = true)
    (hirr : Irreducible (GF.toPoly s.fp)) (hm : m ≤ G.N) (hmK : m * s.fl + s.fl + 1 ≤ G.K)
    (hdist : ∀ i j, i < m → j < m → i ≠ j → pts.getD i 0 ≠ pts.getD j 0) :
    let t := evalS G lagP s
    t.env 53 < 2 ^ s.fl ∧
      ev φ (t.env 53) = lagEval m (fun j => ev φ (pts.getD j 0)) (fun j => ev φ (vals.getD j 0)) (ev φ (s.env 52)) ∧
      Wr lagW s t := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hp1 : 1 < 2 ^ s.fl := Nat.one_lt_two_pow (by omega)
  have hgetw : ∀ (l : List ℕ), (∀ a ∈ l, a < 2 ^ s.fl) → ∀ j, l.getD j 0 < 2 ^ s.fl := by
    intro l hl j
    rcases Nat.lt_or_ge j l.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hl _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ h]; positivity
  have hiK : ∀ i, i < m → i * s.fl ≤ G.K := fun i hi => by
    have := Nat.mul_le_mul_right s.fl hi.le; omega
  set pt : ℕ → F := fun j => ev φ (pts.getD j 0) with hpt
  set val : ℕ → F := fun j => ev φ (vals.getD j 0) with hval
  set X : F := ev φ (s.env 52) with hX
  set g : ℕ → ℕ → F := fun i j => (pt i - pt j)⁻¹ * (X - pt j) with hg
  have hm1 : min (evalE G (s.setv 53 (min 0 G.cap)) (.v 51)) G.N = m := by
    simp only [evalE, FS.setv_env, Function.update_of_ne (show (51 : Var) ≠ 53 by decide), h51]; omega
  have hl := loop_inv G (i := 54) (n := .v 51) (body := lagTerm) (s := s.setv 53 (min 0 G.cap))
    (fun i' u => u.env 53 < 2 ^ s.fl ∧
      ev φ (u.env 53) = ∑ i ∈ Finset.range i', val i * ∏ j ∈ (Finset.range m).erase i, g i j ∧ Wr lagW s u)
    ⟨by simp [hc0], by simp [hc0], Wr.setv s (by decide) _⟩ (by
      rw [hm1]
      rintro i hi u ⟨u53, uev, uW⟩
      have u49 : u.env 49 = packW s.fl pts := (uW.env 49 (by decide)).trans h49
      have u50 : u.env 50 = packW s.fl vals := (uW.env 50 (by decide)).trans h50
      have u51 : u.env 51 = m := (uW.env 51 (by decide)).trans h51
      have u52 : u.env 52 = s.env 52 := uW.env 52 (by decide)
      have u23 : u.env 23 = s.fl := (uW.env 23 (by decide)).trans h23
      have ufl : u.fl = s.fl := uW.fl
      have ufp : u.fp = s.fp := uW.fp
      have hpi := getW_eval G (u.setv 54 i) 49 (.v 54) s.fl i pts hpw (by simp [u49]) (by simp [u23])
        (by simp [evalE]) (hiK i hi) (by omega)
      -- the state before the inner loop
      have hu2 : evalS G (.set 46 (.k 1)) (evalS G (.set 45 (getW 49 (.v 54))) (u.setv 54 i)) =
          ((u.setv 54 i).setv 45 (pts.getD i 0)).setv 46 1 := by
        simp only [evalS_set, hpi, evalE, hc1]
      have hm2 : min (evalE G (((u.setv 54 i).setv 45 (pts.getD i 0)).setv 46 1) (.v 51)) G.N = m := by
        simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_false, u51]; omega
      have hin := loop_inv G (i := 55) (n := .v 51) (body := lagInner) (s := ((u.setv 54 i).setv 45 (pts.getD i 0)).setv 46 1)
        (fun j' w => w.env 46 < 2 ^ s.fl ∧ ev φ (w.env 46) = ∏ j ∈ Finset.range j', (if j = i then 1 else g i j) ∧
          Wr [45, 46, 54, 55] u w ∧ w.env 45 = pts.getD i 0 ∧ w.env 54 = i)
        ⟨by simp only [FS.setv_env, Function.update_self]; exact hp1, by simp [ev_one], ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans
          (Wr.setv _ (by decide) _), by simp, by simp⟩ (by
          rw [hm2]
          rintro j hj w ⟨w46, wev, wW, w45, w54⟩
          have w49 : w.env 49 = packW s.fl pts := (wW.env 49 (by decide)).trans u49
          have w52 : w.env 52 = s.env 52 := (wW.env 52 (by decide)).trans u52
          have w23 : w.env 23 = s.fl := (wW.env 23 (by decide)).trans u23
          have wfl : w.fl = s.fl := wW.fl.trans ufl
          have wfp : w.fp = s.fp := wW.fp.trans ufp
          rw [Finset.prod_range_succ]
          by_cases hji : j = i
          · subst hji
            have hc : evalE G (w.setv 55 j) (.eq (.v 55) (.v 54)) = 1 := by simp [evalE, w54]
            simp only [lagInner, evalS_ite, hc, one_ne_zero, if_false, if_true, evalS_skip, mul_one]
            exact ⟨by simpa using w46, by simpa using wev, wW.trans (Wr.setv _ (by decide) _), by simpa using w45,
              by simpa using w54⟩
          · have hc : evalE G (w.setv 55 j) (.eq (.v 55) (.v 54)) = 0 := by simp [evalE, w54, hji]
            have hpj := getW_eval G (w.setv 55 j) 49 (.v 55) s.fl j pts hpw (by simp [w49]) (by simp [w23])
              (by simp [evalE]) (hiK j hj) (by omega)
            have hpiw := hgetw pts hpw i
            have hpjw := hgetw pts hpw j
            have hxw : s.env 52 < 2 ^ s.fl := h52
            have hne : (pts.getD i 0 ^^^ pts.getD j 0) ≠ 0 := by
              intro h; apply hdist i j hi hj (Ne.symm hji)
              have := Nat.xor_xor_cancel_left (pts.getD i 0) (pts.getD j 0); rw [h, Nat.xor_zero] at this
              exact this
            have hxor := Nat.xor_lt_two_pow hpiw hpjw
            have hxx := Nat.xor_lt_two_pow hxw hpjw
            have hinv := ev_inv φ s.fl _ hmod hf1 hirr hxor hne
            have hpow_lt := powW_lt s.fp s.fl (pts.getD i 0 ^^^ pts.getD j 0) (2 ^ s.fl - 2)
            simp only [lagInner, evalS_ite, hc, if_true, evalS_set]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · simp only [FS.setv_env, Function.update_self, evalE, FS.setv_fl, wfl]; exact mulW_lt _ _ _ _
            · simp (config := { decide := true }) only [FS.setv_env, Function.update_self, Function.update_apply,
                evalE, if_false, hpj, w45, w52, FS.setv_fl, FS.setv_fp, wfl, wfp]
              rw [Nat.mod_eq_of_lt w46, Nat.mod_eq_of_lt hxor, Nat.mod_eq_of_lt hxor, Nat.mod_eq_of_lt hxx,
                Nat.mod_eq_of_lt hxx, Nat.mod_eq_of_lt hpow_lt, Nat.mod_eq_of_lt (mulW_lt s.fp s.fl _ _), ev_mulW φ s.fl _ _ hmod,
                ev_mulW φ s.fl _ _ hmod, hinv, ev_xor, ev_xor, wev, if_neg hji]
              simp only [hg, hpt, hX, CharTwo.sub_eq_add]
            · exact (wW.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
            · simp (config := { decide := true }) [Function.update_apply, w45]
            · simp (config := { decide := true }) [Function.update_apply, w54])
      rw [hm2] at hin
      obtain ⟨i46, iev, iW, i45, i54⟩ := hin
      generalize hu3 : evalS G (.loop 55 (.v 51) lagInner) (((u.setv 54 i).setv 45 (pts.getD i 0)).setv 46 1) = u3
        at i46 iev iW i45 i54
      have v53 : u3.env 53 = u.env 53 := iW.env 53 (by decide)
      have v50 : u3.env 50 = packW s.fl vals := (iW.env 50 (by decide)).trans u50
      have v23 : u3.env 23 = s.fl := (iW.env 23 (by decide)).trans u23
      have vfl : u3.fl = s.fl := iW.fl.trans ufl
      have vfp : u3.fp = s.fp := iW.fp.trans ufp
      have hvi := getW_eval G u3 50 (.v 54) s.fl i vals hvw v50 v23 (by simp [evalE, i54]) (hiK i hi) (by omega)
      have hviw := hgetw vals hvw i
      have hmw := mulW_lt s.fp s.fl (vals.getD i 0) (u3.env 46)
      have e : evalS G lagTerm (u.setv 54 i) = u3.setv 53 ((u.env 53 ^^^ mulW s.fp s.fl (vals.getD i 0) (u3.env 46))
          % 2 ^ s.fl) := by
        simp only [lagTerm, evalS_seq]
        rw [hu2, hu3]
        simp only [evalS_set, evalE, hvi, v53, vfl, vfp, Nat.mod_eq_of_lt hviw, Nat.mod_eq_of_lt i46]
      rw [e]
      refine ⟨by simp; exact Nat.mod_lt _ (by positivity), ?_, ?_⟩
      · simp only [FS.setv_env, Function.update_self]
        rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow u53 hmw), ev_xor, ev_mulW φ s.fl _ _ hmod, uev, iev,
          prod_ite_erase m i hi, Finset.sum_range_succ]
      · exact (uW.trans (iW.mono (W' := lagW) (by decide))).trans (Wr.setv (W := lagW) _ (by decide) _))
  rw [hm1] at hl
  obtain ⟨a, b, c⟩ := hl
  exact ⟨a, b.trans (by simp only [lagEval, hval, hpt, hg, hX]), c⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
