import SourceAdapters.ShortPCP.Machines.FLangPack
import SourceAdapters.ShortPCP.TimeIter

/-!
# Single-run time, machine layer 11: the subspace polynomial on packed lists (Algorithm 21)

`zMP` computes `zMulti B ys = ys.map Z_B` (`Time.zMulti_eq`, char 2) for packed lists `B`, `ys` of field words:
the points `B ++ ys` are held in one packed number `V`; for `j = |B| − 1, …, 0` every point `z` becomes `z·(z + h)`
with `h` the current value at position `j`, i.e. `Z_{B_{≥j}} = Z_{B_{>j}}·(Z_{B_{>j}} + Z_{B_{>j}}(b_j))`
(`Time.zProd_cons`). That is `|B|·(|B| + |ys|)` field products (proof of `thm:short-pcp-ours`: Algorithm 21 within the
`poly(f)` field operations of a level).

Variables: input `26` (packed `B`), `27` (`|B|`), `28` (packed `ys`), `29` (`|ys|`), width `23` (`= f`); output `28`
(the packed result, same length); scratch `30`–`37`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time

variable (G : Glob)

/-! ## Field elements of words -/

section Ev

variable {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F)

/-- The field element of a word (X3′: `GF.rep`). -/
noncomputable def ev (a : ℕ) : F := φ (GF.rep p a)

theorem ev_xor (a b : ℕ) : ev φ (a ^^^ b) = ev φ a + ev φ b := by simp [ev, GF.rep_xor]

theorem ev_mulW (ℓ a b : ℕ) (hp : GF.ModulusOk p ℓ) : ev φ (mulW p ℓ a b) = ev φ a * ev φ b := by
  simp [ev, rep_mulW p ℓ a b hp]

theorem ev_powW (ℓ a e : ℕ) (hp : GF.ModulusOk p ℓ) : ev φ (powW p ℓ a e) = ev φ a ^ e := by
  simp [ev, rep_powW p ℓ a e hp]

@[simp] theorem ev_zero : ev φ 0 = 0 := by simp [ev]

end Ev

/-! ## Reading a packed word -/

/-- Word `i` of the packed list in `V` (width in `23`). -/
def getW (V : Var) (i : E) : E := .md (.shr (.v V) (.mul i (.v 23))) (.shl (.k 1) (.v 23))

theorem getW_eval (s : FS) (V : Var) (i : E) (w j : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w)
    (hV : s.env V = packW w l) (h23 : s.env 23 = w) (hi : evalE G s i = j) (hj : j * w ≤ G.K) (hw : w + 1 ≤ G.K) :
    evalE G s (getW V i) = l.getD j 0 := by
  have hc := cap_ge G
  have h1 : min 1 G.cap = 1 := by have := Nat.lt_two_pow_self (n := G.K); omega
  have h2 : 2 ^ w ≤ G.cap := by
    have := pow_le_cap (G := G) (a := w + 1) hw; rw [pow_succ] at this; have := Nat.one_le_two_pow (n := w); omega
  simp only [getW, evalE, hV, h23, hi, h1, one_mul, min_eq_left h2, min_eq_left (hj.trans hc)]
  exact packW_get w l hl j

/-! ## The routine -/

/-- The body of the inner map: `36 := x·(x + h)` for the word `x` at position `34` of `V` (`30`), `h` in `32`. -/
def zBody : S := .seq (.set 35 (getW 30 (.v 34))) (.set 36 (.fmul (.v 35) (.fadd (.v 35) (.v 32))))

/-- **Algorithm 21 on packed lists**: `28 := zMulti B ys`. -/
def zMP : S :=
  .seq (.set 30 (.add (.v 26) (.shl (.v 28) (.mul (.v 27) (.v 23))))) (.seq (.set 37 (.add (.v 27) (.v 29)))
    (.seq (.loop 33 (.v 27) (.seq (.set 32 (getW 30 (.sub (.sub (.v 27) (.v 33)) (.k 1))))
      (.seq (genP 37 34 36 31 23 zBody) (.set 30 (.v 31)))))
    (.set 28 (.shr (.v 30) (.mul (.v 27) (.v 23))))))

/-- The variables `zMP` writes. -/
def zMW : List Var := [28, 30, 31, 32, 33, 34, 35, 36, 37]

theorem mod_two_pow_of_lt {a w : ℕ} (h : a < 2 ^ w) : a % 2 ^ w = a := Nat.mod_eq_of_lt h

/-- One pass of the outer loop on the field side (`Time.zProd_cons`). -/
theorem zstep {F : Type} [Field F] [CharP F 2] (Bf : List F) (j : ℕ) (hj : j < Bf.length) (orig : List F)
    (hoj : orig.getD j 0 = Bf.getD j 0) :
    (orig.map (zProd (Bf.drop (j + 1)))).map (fun z => z * (z + zProd (Bf.drop (j + 1)) (orig.getD j 0))) =
      orig.map (zProd (Bf.drop j)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro y _
  simp only [Function.comp, List.drop_eq_getElem_cons hj, zProd_cons, hoj, List.getD_eq_getElem _ _ hj]

/-- **The routine `zMP`.** -/
theorem zMP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (B ys : List ℕ) (hB : ∀ a ∈ B, a < 2 ^ s.fl) (hys : ∀ a ∈ ys, a < 2 ^ s.fl)
    (h26 : s.env 26 = packW s.fl B) (h27 : s.env 27 = B.length) (h28 : s.env 28 = packW s.fl ys)
    (h29 : s.env 29 = ys.length) (h23 : s.env 23 = s.fl) (hok : fieldOk G s.fl s.fp = true)
    (hK : s.fl * (B.length + ys.length) + 1 ≤ G.K) (hN : B.length + ys.length ≤ G.N) :
    let t := evalS G zMP s
    ∃ l : List ℕ, t.env 28 = packW s.fl l ∧ l.length = ys.length ∧ (∀ a ∈ l, a < 2 ^ s.fl) ∧
      l.map (ev φ) = zMulti (B.map (ev φ)) (ys.map (ev φ)) ∧ Wr zMW s t := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  set w := s.fl with hw
  set k := B.length with hk
  set m := ys.length with hm
  have hc := cap_ge G
  have hkm : w * k + w * m + 1 ≤ G.K := by rw [← mul_add]; exact hK
  have hpk : 2 ^ (w * (k + m)) ≤ G.cap + 1 := pow_le_cap (by omega)
  have hBm : ∀ a ∈ B ++ ys, a < 2 ^ w := by
    intro a ha; rcases List.mem_append.mp ha with h | h; exacts [hB a h, hys a h]
  -- the initial state
  have hlB := packW_lt w B hB
  have hly := packW_lt w ys hys
  have ekw : min (k * w) G.cap = k * w := by
    have : k * w ≤ G.K := by rw [mul_comm]; omega
    omega
  have hsh : packW w ys * 2 ^ (k * w) + 2 ^ (k * w) ≤ 2 ^ (w * (k + m)) := by
    rw [mul_add, pow_add, mul_comm k w, mul_comm (2 ^ (w * k))]
    have := Nat.mul_le_mul_right (2 ^ (w * k)) (show packW w ys + 1 ≤ 2 ^ (w * m) from hly)
    rw [add_mul, one_mul] at this; linarith
  have e0a : min (packW w ys * 2 ^ (k * w)) G.cap = packW w ys * 2 ^ (k * w) := by
    have := Nat.one_le_two_pow (n := k * w); omega
  have e0b : min (packW w B + packW w ys * 2 ^ (k * w)) G.cap = packW w B + packW w ys * 2 ^ (k * w) := by
    have : packW w B < 2 ^ (k * w) := by rw [mul_comm]; exact hlB
    omega
  have hV0 : packW w B + packW w ys * 2 ^ (k * w) = packW w (B ++ ys) := by
    rw [packW_append, mul_comm (packW w ys), mul_comm k w]
  have e0c : min (packW w (B ++ ys)) G.cap = packW w (B ++ ys) := by rw [← hV0]; exact e0b
  have em : min (k + m) G.cap = k + m := by
    have : k + m ≤ G.K := by nlinarith
    omega
  set s1 := (s.setv 30 (packW w (B ++ ys))).setv 37 (k + m) with hs1
  have hs1e : evalS G (.seq (.set 30 (.add (.v 26) (.shl (.v 28) (.mul (.v 27) (.v 23)))))
      (.set 37 (.add (.v 27) (.v 29)))) s = s1 := by
    simp (config := { decide := true }) only [evalS_seq, evalS_set, evalE, FS.setv_env, Function.update_apply,
      if_false, h26, h27, h28, h29, h23, ← hw, ekw, e0a, e0b, hV0, e0c, em, hs1]
  -- the invariant of the outer loop
  set Bf := B.map (ev φ) with hBf
  have hBfl : Bf.length = k := by simp [Bf, hk]
  let P : ℕ → FS → Prop := fun j u => ∃ l : List ℕ, u.env 30 = packW w l ∧ l.length = k + m ∧
    (∀ a ∈ l, a < 2 ^ w) ∧ l.map (ev φ) = ((B ++ ys).map (ev φ)).map (zProd (Bf.drop (k - j))) ∧
    u.env 37 = k + m ∧ Wr zMW s u
  have hP0 : P 0 s1 := ⟨B ++ ys, by simp [s1], by simp [hk, hm], hBm, by
    rw [Nat.sub_zero, ← hBfl, List.drop_length]; simp [Function.comp_def], by simp [s1],
    (Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)⟩
  have hn1 : min (evalE G s1 (.v 27)) G.N = k := by
    simp (config := { decide := true }) only [evalE, s1, FS.setv_env, Function.update_apply, if_false, h27]; omega
  have hl := loop_inv G (i := 33) (n := .v 27) (s := s1)
    (body := .seq (.set 32 (getW 30 (.sub (.sub (.v 27) (.v 33)) (.k 1))))
      (.seq (genP 37 34 36 31 23 zBody) (.set 30 (.v 31)))) P hP0 (by
    rw [hn1]
    rintro j hj u ⟨l, u30, ul, ulw, ulm, u37, uW⟩
    have u27 : u.env 27 = k := (uW.env 27 (by decide)).trans h27
    have u23 : u.env 23 = w := (uW.env 23 (by decide)).trans h23
    have hjK : (k - j - 1) * w ≤ G.K := by
      have : (k - j - 1) * w ≤ k * w := Nat.mul_le_mul_right _ (by omega)
      rw [mul_comm k w] at this; omega
    have hc1 : min 1 G.cap = 1 := by omega
    have hh := getW_eval G (u.setv 33 j) 30 (.sub (.sub (.v 27) (.v 33)) (.k 1)) w (k - j - 1) l ulw
      (by simp [u30]) (by simp [u23]) (by simp [evalE, u27, hc1]) hjK (by omega)
    set h := l.getD (k - j - 1) 0 with hhdef
    set u2 := (u.setv 33 j).setv 32 h with hu2
    have u2_30 : u2.env 30 = packW w l := by simp [u2, u30]
    have u2_23 : u2.env 23 = w := by simp [u2, u23]
    have u2_37 : u2.env 37 = k + m := by simp [u2, u37]
    have u2_32 : u2.env 32 = h := by simp [u2]
    have hfl2 : u2.fl = w := by rw [hw]; simp [u2, uW.fl]
    have hfp2 : u2.fp = s.fp := by simp [u2, uW.fp]
    -- the inner map
    let g : ℕ → ℕ := fun p => mulW s.fp w (l.getD p 0 % 2 ^ w) ((l.getD p 0 ^^^ h) % 2 ^ w % 2 ^ w)
    have hgen := genP_spec G 37 34 36 31 23 zBody [35, 36] u2 (k + m) w g (by rw [u2_37]; omega) u2_23
      (by rw [mul_add]; omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        intro p hp t' tW tp
        have t30 : t'.env 30 = packW w l := (tW.env 30 (by decide)).trans u2_30
        have t23 : t'.env 23 = w := (tW.env 23 (by decide)).trans u2_23
        have t32 : t'.env 32 = h := (tW.env 32 (by decide)).trans u2_32
        have tfl : t'.fl = w := tW.fl.trans hfl2
        have tfp : t'.fp = s.fp := tW.fp.trans hfp2
        have hpK : p * w ≤ G.K := by
          have : p * w ≤ (k + m) * w := Nat.mul_le_mul_right _ hp.le
          rw [mul_comm (k + m) w] at this; omega
        have hx := getW_eval G t' 30 (.v 34) w p l ulw t30 t23 (by simp [evalE, tp]) hpK (by omega)
        refine ⟨?_, redW_lt _ _ _, (Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)⟩
        simp (config := { decide := true }) only [zBody, evalS_seq, evalS_set, evalE, FS.setv_env,
          Function.update_apply, if_true, if_false, hx, t32, FS.setv_fl, FS.setv_fp, tfl, tfp, g])
    obtain ⟨g31, gW⟩ := hgen
    have hgw : ∀ a ∈ (List.range (k + m)).map g, a < 2 ^ w := by
      intro a ha; simp only [List.mem_map] at ha; obtain ⟨p, -, rfl⟩ := ha; exact redW_lt _ _ _
    refine ⟨(List.range (k + m)).map g, ?_, by simp, hgw, ?_, ?_, ?_⟩
    · simp only [evalS_seq, evalS_set, FS.setv_env, Function.update_self, evalE]
      rw [hh]; exact g31
    · -- the field side
      have hkj : k - j = (k - j - 1) + 1 := by omega
      have hj1 : k - j - 1 < Bf.length := by rw [hBfl]; omega
      have hlk : k - j - 1 < l.length := by rw [ul]; omega
      have hhl : ev φ h = zProd (Bf.drop (k - j)) (((B ++ ys).map (ev φ)).getD (k - j - 1) 0) := by
        have := congrArg (fun z : List F => z.getD (k - j - 1) 0) ulm
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
        rw [hhdef, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem hlk] at this ⊢
        rw [List.getElem?_eq_getElem (by simp; omega)] at this ⊢
        simpa using this
      rw [show k - (j + 1) = k - j - 1 by omega]
      rw [← zstep Bf (k - j - 1) hj1 ((B ++ ys).map (ev φ)) (by
        simp only [hBf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append_left
          (show k - j - 1 < B.length by omega)]), ← hkj, ← hhl, ← ulm]
      apply List.ext_getElem (by simp [ul])
      intro p h1 h2
      simp only [List.length_map, List.length_range] at h1
      have hpl : p < l.length := by rw [ul]; exact h1
      have hlp : l[p] < 2 ^ w := ulw _ (List.getElem_mem _)
      have hhw : h < 2 ^ w := by rw [hhdef, List.getD_eq_getElem _ _ hlk]; exact ulw _ (List.getElem_mem _)
      simp only [List.getElem_map, List.getElem_range, g, List.getD_eq_getElem _ _ hpl,
        Nat.mod_eq_of_lt hlp, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hlp hhw)]
      rw [ev_mulW φ w _ _ hmod, ev_xor]
    · simp only [evalS_seq, evalS_set, FS.setv_env]
      rw [hh, Function.update_of_ne (by decide), gW.env 37 (by decide), u2_37]
    · simp only [evalS_seq, evalS_set]
      rw [hh]
      exact ((uW.trans ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))).trans
        (gW.mono (by decide : ∀ x ∈ ([31, 34, 35, 36] : List Var), x ∈ zMW))).trans (Wr.setv _ (by decide) _))
  rw [hn1] at hl
  obtain ⟨l, f30, fl, flw, flm, -, fW⟩ := hl
  set u := evalS G (.loop 33 (.v 27) (.seq (.set 32 (getW 30 (.sub (.sub (.v 27) (.v 33)) (.k 1))))
      (.seq (genP 37 34 36 31 23 zBody) (.set 30 (.v 31))))) s1 with hu
  have ht : t = u.setv 28 (evalE G u (.shr (.v 30) (.mul (.v 27) (.v 23)))) := by
    show evalS G zMP s = _
    simp only [zMP, evalS_seq]
    rw [show evalS G (.set 37 (.add (.v 27) (.v 29))) (evalS G (.set 30 (.add (.v 26) (.shl (.v 28)
      (.mul (.v 27) (.v 23))))) s) = s1 from hs1e]
    rfl
  have f27 : u.env 27 = k := (fW.env 27 (by decide)).trans h27
  have f23 : u.env 23 = w := (fW.env 23 (by decide)).trans h23
  refine ⟨l.drop k, ?_, by simp [fl], fun a ha => flw a (List.mem_of_mem_drop ha), ?_, ?_⟩
  · rw [ht]
    simp only [FS.setv_env, Function.update_self, evalE, f30, f27, f23, ekw]
    rw [packW_drop w l flw k, mul_comm k w]
  · rw [List.map_drop, flm, Nat.sub_self, List.drop_zero, zMulti_eq, List.map_append, List.map_append,
      List.drop_append_of_le_length (by simp [hk]), List.drop_eq_nil_of_le (by simp [hk]), List.nil_append]
  · rw [ht]; exact fW.trans (Wr.setv _ (by decide) _)

end NearCubicGates.Adapters.ShortPCP.Machines.FL
