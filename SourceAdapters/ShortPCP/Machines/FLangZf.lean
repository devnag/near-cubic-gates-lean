import SourceAdapters.ShortPCP.Machines.FLangTable

/-!
# Single-run time, machine layer 18: `Z_B` at one point, and `rowIdx`

`Time.zFast B y = (zMulti B [y]).headD 0` evaluates the subspace polynomial of `span B` at `y` (Algorithm 21; proof of `thm:short-pcp-ours`). It is used by `Translate` (row and column tests, `Lvl.post`) and by `V_VRS` (`Z_H(α + O_H)`). `zfP y`
runs `zMP` on the one-point list `[y]` (basis packed in `26`, length in `27`; result word in `28`, `zfP_spec`).
`rowIdxE` is the index arithmetic `Time.rowIdx` for `rv ≥ 2` as one expression (`rowIdxE_eval`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13

variable (G : Glob)

/-- `28 := Z_B(y)` for the packed basis `B` in `26` (length `27`). -/
def zfP (y : E) : S := .seq (.set 28 y) (.seq (.set 29 (.k 1)) zMP)

/-- The variables `zfP` writes. -/
def zfW : List Var := 29 :: zMW

/-- **`Z_B` at one point.** -/
theorem zfP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (y : E)
    (B : List ℕ) (yw : ℕ) (hB : ∀ a ∈ B, a < 2 ^ s.fl) (hy : evalE G s y = yw) (hyw : yw < 2 ^ s.fl)
    (h26 : s.env 26 = packW s.fl B) (h27 : s.env 27 = B.length) (h23 : s.env 23 = s.fl)
    (hok : fieldOk G s.fl s.fp = true) (hK : s.fl * (B.length + 1) + 1 ≤ G.K) (hN : B.length + 1 ≤ G.N) :
    let t := evalS G (zfP y) s
    t.env 28 < 2 ^ s.fl ∧ ev φ (t.env 28) = zFast (B.map (ev φ)) (ev φ yw) ∧ Wr zfW s t := by
  intro t
  have hc1 : min 1 G.cap = 1 := min_cap (by have := (fl_bounds hok).1; omega)
  have hz := zMP_spec G ((s.setv 28 yw).setv 29 1) φ B [yw] hB (by simpa using hyw)
    (by simp; exact h26) (by simp; exact h27) (by simp [packW]) (by simp)
    (by simp; exact h23) hok (by simpa using hK) (by simpa using hN)
  obtain ⟨l, z28, zl, zlw, zlm, zW⟩ := hz
  have ht : t = evalS G zMP ((s.setv 28 yw).setv 29 1) := by
    show evalS G (zfP y) s = _
    simp only [zfP, evalS_seq, evalS_set, hy, evalE, hc1]
  rw [ht]
  obtain ⟨a, rfl⟩ : ∃ a, l = [a] := by
    match l, zl with
    | [a], _ => exact ⟨a, rfl⟩
  refine ⟨by rw [z28]; simpa [packW] using zlw a (by simp), ?_, ?_⟩
  · rw [z28]
    simp only [packW, mul_zero, add_zero]
    have := congrArg (fun z : List F => z.headD 0) zlm
    simpa [zFast] using this
  · exact ((Wr.setv (W := zfW) (i := 28) s (by decide) _).trans (Wr.setv (W := zfW) (i := 29) _ (by decide) _)).trans
      (zW.mono (by decide))

/-! ## `rowIdx` -/

/-- `Time.rowIdx k rv ι` for `rv ≥ 2` (`k` in `44`, `rv` in `45`, `ι` in `54`). -/
def rowIdxE : E :=
  .add (.k 1) (.bxor (.md (.md (.sub (.v 54) (.k 1)) (.shl (.k 1) (.add (.v 44) (.k 2)))) (.shl (.k 1) (.add (.v 44) (.k 1))))
    (.mul (.md (.shr (.md (.sub (.v 54) (.k 1)) (.shl (.k 1) (.add (.v 44) (.k 2)))) (.add (.v 44) (.k 1))) (.k 2))
      (.shl (.v 45) (.v 44))))

theorem rowIdxE_eval (s : FS) (k rv ι M : ℕ) (h44 : s.env 44 = k) (h45 : s.env 45 = rv) (h54 : s.env 54 = ι)
    (hrv2 : 2 ≤ rv) (hM : rv * 2 ^ k < 2 ^ M) (hkM : k + 2 ≤ M) (hMK : M + 1 ≤ G.K) :
    evalE G s rowIdxE = rowIdx k rv ι := by
  have hc := cap_ge G
  have hpM := pow_le_cap (G := G) (a := M + 1) hMK
  rw [pow_succ] at hpM
  have hM1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have ek1 : min (k + 1) G.cap = k + 1 := min_cap (by omega)
  have ek2 : min (k + 2) G.cap = k + 2 := min_cap (by omega)
  have hk2M : 2 ^ (k + 2) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hkM
  have hk1M : 2 ^ (k + 1) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
  have p1 : min (2 ^ (k + 1)) G.cap = 2 ^ (k + 1) := min_eq_left (by omega)
  have p2 : min (2 ^ (k + 2)) G.cap = 2 ^ (k + 2) := min_eq_left (by omega)
  have ek : min k G.cap = k := min_cap (by omega)
  have p3 : min (rv * 2 ^ k) G.cap = rv * 2 ^ k := min_eq_left (by omega)
  have hMK' : 2 ^ M ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
  set Z := (ι - 1) % 2 ^ (k + 2) with hZ
  have hX : Z % 2 ^ (k + 1) < 2 ^ M := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hk1M
  unfold rowIdx
  rw [if_neg (by omega), Nat.testBit_eq_decide_div_mod_eq]
  simp only [rowIdxE, evalE, h44, h45, h54, hc1, hc2, one_mul, ek1, ek2, p1, p2, ek, p3, ← hZ]
  rcases Nat.mod_two_eq_zero_or_one (Z / 2 ^ (k + 1)) with hb | hb
  · have e0 : min (0 * (rv * 2 ^ k)) G.cap = 0 := by simp
    have hx := Nat.xor_lt_two_pow hX (show 0 < 2 ^ M by positivity)
    rw [hb, e0]
    simp only [Nat.xor_zero, show decide ((0 : ℕ) = 1) = false by decide, Bool.false_eq_true, if_false]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hX hMK')]
    exact min_eq_left (by omega)
  · rw [hb, one_mul, p3]
    simp only [show decide ((1 : ℕ) = 1) = true by decide, if_true, mul_comm (2 ^ k) rv]
    have hx := Nat.xor_lt_two_pow hX hM
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hx hMK')]
    exact min_eq_left (by omega)

end NearCubicGates.Adapters.ShortPCP.Machines.FL
