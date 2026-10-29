import SourceAdapters.ShortPCP.Machines.FLangZ

/-!
# Single-run time, machine layer 12: one level of the recursion of `V_{RS,=}`

BCGT13 §12.3.1 (proof of `thm:short-pcp-ours`: "Its recursion roughly halves the dimension of the current affine subspace at each
level and does poly(f) field operations per level"). A level `Time.Lvl` (basis, offset, remaining coins) is held in
variables: `38` the packed basis, `39` its length `κ`, `40` the offset word, `41` the position of the remaining coins
in the coin list `u` (`42 = bitsValue u`, `43 = |u|`); the width is `23 = f`. `stepP` replaces it by `Lvl.step`
(`TimeIter.lean`): the row domain `L_β` (coin `0`: the first `k + 1` basis words and one more word, `sel` of the
upper half by `κ − k` coins) or the column domain `Z_{L0}(L1)` (`zMP`), `k = ⌊κ/2⌋` (`stepP_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## Coin windows -/

theorem bitsValue_eq_packW : ∀ u : List Bool, bitsValue u = packW 1 (u.map Bool.toNat)
  | [] => rfl
  | b :: u => by simp [bitsValue, packW, bitsValue_eq_packW u]

theorem toNat_lt_two (u : List Bool) : ∀ a ∈ u.map Bool.toNat, a < 2 ^ 1 := by
  intro a ha; simp only [List.mem_map] at ha; obtain ⟨b, -, rfl⟩ := ha; cases b <;> simp

theorem bitsValue_window (u : List Bool) (a b : ℕ) : bitsValue ((u.drop a).take b) = bitsValue u / 2 ^ a % 2 ^ b := by
  rw [bitsValue_eq_packW, bitsValue_eq_packW, List.map_take, List.map_drop,
    packW_take 1 _ (fun x hx => toNat_lt_two u x (List.mem_of_mem_drop hx)), packW_drop 1 _ (toNat_lt_two u),
    one_mul, one_mul]

theorem head_drop_iff (u : List Bool) (a : ℕ) :
    (u.drop a).head? = some false ↔ a < u.length ∧ bitsValue u / 2 ^ a % 2 = 0 := by
  have h := packW_get 1 (u.map Bool.toNat) (toNat_lt_two u) a
  rw [← bitsValue_eq_packW, mul_one, pow_one] at h
  rw [h, List.head?_drop]
  rcases Nat.lt_or_ge a u.length with ha | ha
  · rw [List.getElem?_eq_getElem ha, List.getD_eq_getElem _ _ (by simpa using ha)]
    cases hb : u[a] <;> simp [ha, hb]
  · rw [List.getElem?_eq_none ha]; simp; omega

/-! ## The level representation -/

/-- The level `x` is held in `38`–`41` (coins `u`, width `w`). -/
def LRep {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (w : ℕ) (u : List Bool) (s : FS)
    (x : Lvl F) : Prop :=
  ∃ l : List ℕ, s.env 38 = packW w l ∧ s.env 39 = l.length ∧ (∀ a ∈ l, a < 2 ^ w) ∧ l.map (ev φ) = x.B ∧
    s.env 40 < 2 ^ w ∧ ev φ (s.env 40) = x.O ∧ x.r = u.drop (s.env 41)

/-- The new basis of the row domain: the first `k + 1` words and the word in `46`. -/
def rowB : E := .add (.md (.v 38) (.shl (.k 1) (.mul (.add (.v 44) (.k 1)) (.v 23))))
  (.shl (.v 46) (.mul (.add (.v 44) (.k 1)) (.v 23)))

/-- The row step (`44 = k`): `45 := rv`, `46 :=` the new word, then the basis, the coin position and `κ := k + 2`. -/
def rowP : S :=
  .seq (.set 45 (.md (.shr (.v 42) (.add (.v 41) (.k 1))) (.shl (.k 1) (.sub (.v 39) (.v 44)))))
  (.seq (.ite (.lt (.v 45) (.k 2)) (.set 46 (getW 38 (.add (.v 44) (.k 1))))
    (.seq (.set 20 (.shr (.v 38) (.mul (.v 44) (.v 23)))) (.seq (.set 21 (.sub (.v 39) (.v 44)))
      (.seq (.set 22 (.v 45)) (.seq selP (.set 46 (.fadd (.fadd (.v 24) (.v 40)) (.v 40))))))))
  (.seq (.set 38 rowB) (.seq (.set 41 (.add (.add (.v 41) (.k 1)) (.sub (.v 39) (.v 44))))
    (.set 39 (.add (.v 44) (.k 2))))))

/-- The column step (`44 = k`): `zMP` on the halves, offset `0`, coin position `+ k + 2`, `κ := κ − k`. -/
def colP : S :=
  .seq (.set 26 (.md (.v 38) (.shl (.k 1) (.mul (.v 44) (.v 23))))) (.seq (.set 27 (.v 44))
  (.seq (.set 28 (.shr (.v 38) (.mul (.v 44) (.v 23)))) (.seq (.set 29 (.sub (.v 39) (.v 44))) (.seq zMP
  (.seq (.set 38 (.v 28)) (.seq (.set 41 (.add (.add (.v 41) (.k 1)) (.add (.v 44) (.k 1))))
  (.seq (.set 39 (.sub (.v 39) (.v 44))) (.set 40 (.k 0)))))))))

/-- **One level**: `k := ⌊κ/2⌋`, then the row step on coin `0`, the column step otherwise. -/
def stepP : S :=
  .seq (.set 44 (.div (.v 39) (.k 2)))
    (.ite (.mul (.lt (.v 41) (.v 43)) (.eq (.md (.shr (.v 42) (.v 41)) (.k 2)) (.k 0))) rowP colP)

/-- The variables `stepP` writes. -/
def stepW : List Var := [38, 39, 40, 41, 44, 45, 46, 20, 21, 22, 24, 25, 26, 27, 29] ++ zMW

theorem min_cap {G : Glob} {x : ℕ} (h : x ≤ G.K) : min x G.cap = x := min_eq_left (h.trans (cap_ge G))

theorem min_cap_pow {G : Glob} {a : ℕ} (h : a + 1 ≤ G.K) : min (2 ^ a) G.cap = 2 ^ a := by
  have := pow_le_cap (G := G) h; rw [pow_succ] at this; have := Nat.one_le_two_pow (n := a)
  exact min_eq_left (by omega)

theorem min_cap_lt {G : Glob} {x a : ℕ} (hx : x < 2 ^ a) (h : a ≤ G.K) : min x G.cap = x := by
  have := pow_le_cap (G := G) h; exact min_eq_left (by omega)

/-- **The column step.** -/
theorem colP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl)
    (h44 : s.env 44 = x.B.length / 2) (hok : fieldOk G s.fl s.fp = true)
    (hK : s.fl * x.B.length + 1 ≤ G.K) (hN : x.B.length ≤ G.N) (hoff : s.env 41 + x.B.length + 2 ≤ G.K) :
    let t := evalS G colP s
    LRep φ s.fl u t ⟨zMulti (x.B.take (x.B.length / 2)) (x.B.drop (x.B.length / 2)), 0,
      x.r.drop (1 + (x.B.length / 2 + 1))⟩ ∧ Wr stepW s t ∧ t.env 41 ≤ s.env 41 + x.B.length + 2 := by
  intro t
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := hx
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hκ : x.B.length = l.length := by rw [← hlm, List.length_map]
  rw [hκ] at h44 hK hN hoff ⊢
  obtain ⟨k, hk⟩ : ∃ k, k = l.length / 2 := ⟨_, rfl⟩
  rw [← hk] at h44 ⊢
  have hkκ : k ≤ l.length := by rw [hk]; exact Nat.div_le_self _ _
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hkw0 : k * s.fl ≤ s.fl * l.length := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hkκ
  have e1 : min (k * s.fl) G.cap = k * s.fl := min_cap (by omega)
  have e2 : min (2 ^ (k * s.fl)) G.cap = 2 ^ (k * s.fl) := min_cap_pow (by omega)
  have ek : min k G.cap = k := min_cap (by omega)
  have hB : ∀ a ∈ l.take k, a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_take ha)
  have hys : ∀ a ∈ l.drop k, a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_drop ha)
  have hs4e : evalS G (.set 29 (.sub (.v 39) (.v 44))) (evalS G (.set 28 (.shr (.v 38) (.mul (.v 44) (.v 23))))
      (evalS G (.set 27 (.v 44)) (evalS G (.set 26 (.md (.v 38) (.shl (.k 1) (.mul (.v 44) (.v 23))))) s))) =
      (((s.setv 26 (packW s.fl (l.take k))).setv 27 k).setv 28 (packW s.fl (l.drop k))).setv 29 (l.length - k) := by
    simp (config := { decide := true }) only [evalS_seq, evalS_set, evalE, FS.setv_env, Function.update_apply,
      if_false, h38, h39, h44, h23, hc1, one_mul, e1, e2]
    rw [packW_take _ l hlw, packW_drop _ l hlw, mul_comm s.fl k]
  have hz := zMP_spec G ((((s.setv 26 (packW s.fl (l.take k))).setv 27 k).setv 28 (packW s.fl (l.drop k))).setv 29
      (l.length - k)) φ (l.take k) (l.drop k) hB hys (by simp) (by simp; omega) (by simp) (by simp)
    (by simp (config := { decide := true }) [Function.update_apply, h23]) hok
    (by simp only [FS.setv_fl, List.length_take, List.length_drop]; rw [min_eq_left hkκ, Nat.add_sub_cancel' hkκ]; omega)
    (by simp only [List.length_take, List.length_drop]; omega)
  obtain ⟨l', z28, zl, zlw, zlm, zW⟩ := hz
  generalize ht5 : evalS G zMP ((((s.setv 26 (packW s.fl (l.take k))).setv 27 k).setv 28
    (packW s.fl (l.drop k))).setv 29 (l.length - k)) = t5 at z28 zW
  have t5W : Wr (zMW ++ [26, 27, 29]) s t5 :=
    ((Wr.setv s (by decide) _).trans ((Wr.setv _ (by decide) _).trans ((Wr.setv _ (by decide) _).trans
      (Wr.setv _ (by decide) _)))).trans (zW.mono (fun y hy => by simp [hy]))
  have f39 : t5.env 39 = l.length := by rw [t5W.env 39 (by decide), h39]
  have f41 : t5.env 41 = s.env 41 := t5W.env 41 (by decide)
  have f44 : t5.env 44 = k := by rw [t5W.env 44 (by decide), h44]
  have e3 : min (s.env 41 + 1) G.cap = s.env 41 + 1 := min_cap (by omega)
  have e4 : min (k + 1) G.cap = k + 1 := min_cap (by omega)
  have e5 : min (s.env 41 + 1 + (k + 1)) G.cap = s.env 41 + 1 + (k + 1) := min_cap (by omega)
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have ht : t = (((t5.setv 38 (packW s.fl l')).setv 41 (s.env 41 + 1 + (k + 1))).setv 39 (l.length - k)).setv 40 0 := by
    show evalS G colP s = _
    simp only [colP, evalS_seq]
    rw [hs4e, ht5]
    simp (config := { decide := true }) only [evalS_seq, evalS_set, evalE, FS.setv_env, Function.update_apply,
      if_false, z28, f39, f41, f44, hc1, e3, e4, e5, hc0, FS.setv_fl]
  have hlk : (l.drop k).length = l.length - k := List.length_drop
  refine ⟨⟨l', ?_, ?_, zlw, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [ht]; simp (config := { decide := true }) [Function.update_apply]
  · rw [ht]; simp (config := { decide := true }) [Function.update_apply]; omega
  · show l'.map (ev φ) = zMulti (x.B.take k) (x.B.drop k)
    simp only [FS.setv_fp] at zlm
    rw [zlm, List.map_take, List.map_drop, hlm]
  · rw [ht]; simp
  · rw [ht]; simp
  · rw [ht]; simp (config := { decide := true }) [Function.update_apply, hr, List.drop_drop]; omega
  · rw [ht]
    exact (((t5W.mono (by decide : ∀ y ∈ (zMW ++ [26, 27, 29] : List Var), y ∈ stepW)).trans (Wr.setv _ (by decide) _)).trans
      ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))).trans (Wr.setv _ (by decide) _)
  · rw [ht]; simp (config := { decide := true }) [Function.update_apply]; omega

/-- **The row step.** -/
theorem rowP_spec {F : Type} [Field F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl)
    (h44 : s.env 44 = x.B.length / 2) (h42 : s.env 42 = bitsValue u) (hok : fieldOk G s.fl s.fp = true)
    (h3 : 3 ≤ x.B.length) (hK : s.fl * x.B.length + 1 ≤ G.K) (hN : x.B.length ≤ G.N)
    (hoff : s.env 41 + x.B.length + 2 ≤ G.K) :
    let t := evalS G rowP s
    LRep φ s.fl u t ⟨if bitsValue ((x.r.drop 1).take (x.B.drop (x.B.length / 2)).length) < 2 then
        x.B.take (x.B.length / 2 + 1) ++ [x.B.getD (x.B.length / 2 + 1) 0]
      else x.B.take (x.B.length / 2 + 1) ++
        [sel (x.B.drop (x.B.length / 2)) (bitsValue ((x.r.drop 1).take (x.B.drop (x.B.length / 2)).length)) + x.O + x.O],
      x.O, x.r.drop (1 + (x.B.drop (x.B.length / 2)).length)⟩ ∧ Wr stepW s t ∧
      t.env 41 ≤ s.env 41 + x.B.length + 2 := by
  intro t
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := hx
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hκ : x.B.length = l.length := by rw [← hlm, List.length_map]
  rw [hκ] at h44 hK hN hoff h3 ⊢
  obtain ⟨k, hk⟩ : ∃ k, k = l.length / 2 := ⟨_, rfl⟩
  rw [← hk] at h44 ⊢
  have hk2 : k + 2 ≤ l.length := by omega
  have hdl : (x.B.drop k).length = l.length - k := by rw [List.length_drop, hκ]
  rw [hdl]
  obtain ⟨rv, hrv⟩ : ∃ rv, rv = bitsValue ((x.r.drop 1).take (l.length - k)) := ⟨_, rfl⟩
  rw [← hrv]
  have hrv' : rv = bitsValue u / 2 ^ (s.env 41 + 1) % 2 ^ (l.length - k) := by
    rw [hrv, hr, List.drop_drop, bitsValue_window]
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have hmulκ : ∀ j, j ≤ l.length → j * s.fl ≤ s.fl * l.length := fun j hj => by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hj
  have e1 : min (s.env 41 + 1) G.cap = s.env 41 + 1 := min_cap (by omega)
  have e2 : min (2 ^ (l.length - k)) G.cap = 2 ^ (l.length - k) := min_cap_pow (by
    have := hmulκ (l.length - k) (by omega); have : l.length - k ≤ (l.length - k) * s.fl := Nat.le_mul_of_pos_right _ hf1
    omega)
  -- the new word
  obtain ⟨wd, hwd, hevwd, t2, ht2, t2_46, t2W⟩ : ∃ wd, wd < 2 ^ s.fl ∧
      ev φ wd = (if rv < 2 then x.B.getD (k + 1) 0 else sel (x.B.drop k) rv + x.O + x.O) ∧
      ∃ t2, evalS G (.ite (.lt (.v 45) (.k 2)) (.set 46 (getW 38 (.add (.v 44) (.k 1))))
        (.seq (.set 20 (.shr (.v 38) (.mul (.v 44) (.v 23)))) (.seq (.set 21 (.sub (.v 39) (.v 44)))
          (.seq (.set 22 (.v 45)) (.seq selP (.set 46 (.fadd (.fadd (.v 24) (.v 40)) (.v 40))))))))
          (s.setv 45 rv) = t2 ∧ t2.env 46 = wd ∧ Wr [46, 20, 21, 22, 24, 25] (s.setv 45 rv) t2 := by
    by_cases hlt : rv < 2
    · have ek1 : min (k + 1) G.cap = k + 1 := min_cap (by omega)
      have hg := getW_eval G (s.setv 45 rv) 38 (.add (.v 44) (.k 1)) s.fl (k + 1) l hlw (by simp [h38])
        (by simp [h23]) (by simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply,
          if_false, h44, hc1, ek1])
        (by have := hmulκ (k + 1) (by omega); omega) (by omega)
      refine ⟨l.getD (k + 1) 0, ?_, ?_, _, rfl, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ (by omega)]; exact hlw _ (List.getElem_mem _)
      · rw [if_pos hlt, ← hlm, ← ev_zero φ, List.getD_map]
      · rw [evalS_ite]; simp [evalE, hlt, hc2, hg]
      · rw [evalS_ite]; simp only [evalE, FS.setv_env, Function.update_self, hlt, hc2, if_true, one_ne_zero,
          if_false, evalS_set]
        exact Wr.setv (W := [46, 20, 21, 22, 24, 25]) _ (by decide) _
    · have hlk : (l.drop k).length = l.length - k := List.length_drop
      have hdw : ∀ a ∈ l.drop k, a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_drop ha)
      have hkK : k * s.fl ≤ G.K := by have := hmulκ k (by omega); omega
      have hs2e : evalS G (.set 22 (.v 45)) (evalS G (.set 21 (.sub (.v 39) (.v 44)))
          (evalS G (.set 20 (.shr (.v 38) (.mul (.v 44) (.v 23)))) (s.setv 45 rv))) =
          (((s.setv 45 rv).setv 20 (packW s.fl (l.drop k))).setv 21 (l.length - k)).setv 22 rv := by
        simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false,
          if_true, h38, h44, h23, h39, min_cap hkK]
        rw [packW_drop _ l hlw, mul_comm k s.fl]
      have hsel := selP_spec G ((((s.setv 45 rv).setv 20 (packW s.fl (l.drop k))).setv 21 (l.length - k)).setv 22 rv)
        φ (l.drop k) hdw (by simp) (by simp [hlk])
        (by simp (config := { decide := true }) [Function.update_apply, h23]) hok
        (by simp only [FS.setv_fl]; rw [hlk]; have := hmulκ (l.length - k) (by omega); have := cap_ge G; omega)
        (by rw [hlk]; omega)
      obtain ⟨h24, hsel24, selW⟩ := hsel
      simp only [FS.setv_fl, FS.setv_fp] at h24 hsel24
      generalize ht3 : evalS G selP ((((s.setv 45 rv).setv 20 (packW s.fl (l.drop k))).setv 21
        (l.length - k)).setv 22 rv) = t3 at h24 hsel24 selW
      have t3_40 : t3.env 40 = s.env 40 := by rw [selW.env 40 (by decide)]; simp
      have t3fl : t3.fl = s.fl := by rw [selW.fl]; rfl
      refine ⟨((t3.env 24 ^^^ s.env 40) % 2 ^ s.fl ^^^ s.env 40) % 2 ^ s.fl, Nat.mod_lt _ (by positivity), ?_,
        _, rfl, ?_, ?_⟩
      · rw [if_neg hlt, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) h40),
          Nat.mod_eq_of_lt (Nat.xor_lt_two_pow h24 h40), ev_xor, ev_xor, hO]
        congr 2
        refine hsel24.trans ?_
        simp only [FS.setv_env, Function.update_self, ← hlm, List.map_drop]
        rfl
      · rw [evalS_ite]
        simp only [evalE, FS.setv_env, Function.update_self, show ¬ rv < 2 from hlt, hc2, if_false, if_true,
          evalS_seq]
        rw [hs2e, ht3]
        simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_true,
          if_false, t3_40, t3fl]
      · rw [evalS_ite]
        simp only [evalE, FS.setv_env, Function.update_self, show ¬ rv < 2 from hlt, hc2, if_false, if_true,
          evalS_seq]
        rw [hs2e, ht3]
        simp only [evalS_set]
        exact ((((Wr.setv (W := [46, 20, 21, 22, 24, 25]) _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans
          (Wr.setv _ (by decide) _)).trans (selW.mono (by decide))).trans (Wr.setv _ (by decide) _)
  -- the frame of the branch
  have tW : Wr (45 :: [46, 20, 21, 22, 24, 25]) s t2 :=
    (Wr.setv s (by decide) _).trans (t2W.mono (fun y hy => List.mem_cons_of_mem _ hy))
  have f38 : t2.env 38 = packW s.fl l := (tW.env 38 (by decide)).trans h38
  have f39 : t2.env 39 = l.length := (tW.env 39 (by decide)).trans h39
  have f41 : t2.env 41 = s.env 41 := tW.env 41 (by decide)
  have f44 : t2.env 44 = k := (tW.env 44 (by decide)).trans h44
  have f23 : t2.env 23 = s.fl := (tW.env 23 (by decide)).trans h23
  have f40 : t2.env 40 = s.env 40 := tW.env 40 (by decide)
  have h45 : evalE G s (.md (.shr (.v 42) (.add (.v 41) (.k 1))) (.shl (.k 1) (.sub (.v 39) (.v 44)))) = rv := by
    simp only [evalE, h42, h39, h44, hc1, one_mul, e1, e2]; exact hrv'.symm
  have hk1K : (k + 1) * s.fl ≤ G.K := by have := hmulκ (k + 1) (by omega); omega
  have hk2 : 2 ^ ((k + 1) * s.fl) * 2 ^ s.fl ≤ G.cap := by
    rw [← pow_add]
    have := pow_le_cap (G := G) (a := (k + 1) * s.fl + s.fl + 1) (by
      have e : (k + 1) * s.fl + s.fl = (k + 2) * s.fl := by ring
      have := hmulκ (k + 2) hk2; omega)
    rw [pow_succ] at this; have := Nat.one_le_two_pow (n := (k + 1) * s.fl + s.fl); omega
  have hpt : packW s.fl l % 2 ^ ((k + 1) * s.fl) < 2 ^ ((k + 1) * s.fl) := Nat.mod_lt _ (by positivity)
  have hwd2 : wd * 2 ^ ((k + 1) * s.fl) + 2 ^ ((k + 1) * s.fl) ≤ 2 ^ ((k + 1) * s.fl) * 2 ^ s.fl := by
    have := Nat.mul_le_mul_right (2 ^ ((k + 1) * s.fl)) (show wd + 1 ≤ 2 ^ s.fl from hwd)
    rw [add_mul, one_mul, mul_comm (2 ^ s.fl)] at this; exact this
  have r1 : min (k + 1) G.cap = k + 1 := min_cap (by omega)
  have r2 : min ((k + 1) * s.fl) G.cap = (k + 1) * s.fl := min_cap hk1K
  have r3 : min (2 ^ ((k + 1) * s.fl)) G.cap = 2 ^ ((k + 1) * s.fl) := min_cap_pow (by
    have := hmulκ (k + 1) (by omega); omega)
  have r4 : min (wd * 2 ^ ((k + 1) * s.fl)) G.cap = wd * 2 ^ ((k + 1) * s.fl) := min_eq_left (by omega)
  have r5 : min (packW s.fl l % 2 ^ ((k + 1) * s.fl) + wd * 2 ^ ((k + 1) * s.fl)) G.cap =
      packW s.fl l % 2 ^ ((k + 1) * s.fl) + wd * 2 ^ ((k + 1) * s.fl) := min_eq_left (by omega)
  have r6 : min (s.env 41 + 1 + (l.length - k)) G.cap = s.env 41 + 1 + (l.length - k) := min_cap (by omega)
  have r7 : min (k + 2) G.cap = k + 2 := min_cap (by omega)
  have ht : t = ((t2.setv 38 (packW s.fl l % 2 ^ ((k + 1) * s.fl) + wd * 2 ^ ((k + 1) * s.fl))).setv 41
      (s.env 41 + 1 + (l.length - k))).setv 39 (k + 2) := by
    show evalS G rowP s = _
    simp only [rowP, evalS_seq]
    rw [show evalS G (.set 45 (.md (.shr (.v 42) (.add (.v 41) (.k 1))) (.shl (.k 1) (.sub (.v 39) (.v 44))))) s =
      s.setv 45 rv by rw [evalS_set, h45], ht2]
    simp (config := { decide := true }) only [rowB, evalS_set, evalE, FS.setv_env, Function.update_apply,
      if_false, if_true, f38, f39, f41, f44, f23, t2_46, hc1, hc2, one_mul, e1, r1, r2, r3, r4, r5, r6, r7]
  have hlen : (l.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
  refine ⟨⟨l.take (k + 1) ++ [wd], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [ht]; simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]
    rw [packW_append, packW_take _ l hlw, hlen]; simp [packW, mul_comm]
  · rw [ht]; simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]
    simp [hlen]
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hlw a (List.mem_of_mem_take h)
    · simp at h; rw [h]; exact hwd
  · rw [List.map_append, List.map_take, hlm]
    split_ifs at hevwd ⊢ <;> simp [hevwd]
  · rw [ht]; simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true, f40]
    exact h40
  · rw [ht]; simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true, f40]
    exact hO
  · rw [ht]; simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]
    rw [hr, List.drop_drop]; congr 1; omega
  · rw [ht]
    exact ((tW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans ((Wr.setv _ (by decide) _).trans
      (Wr.setv _ (by decide) _))
  · rw [ht]; simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]
    omega

theorem LRep.setv {F : Type} [Field F] {p : ℕ} {φ : AdjoinRoot (GF.toPoly p) →+* F} {w : ℕ} {u : List Bool}
    {s : FS} {x : Lvl F} (h : LRep φ w u s x) (i : Var) (hi : i ∉ ([38, 39, 40, 41] : List Var)) (v : ℕ) :
    LRep φ w u (s.setv i v) x := by
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  refine ⟨l, ?_, ?_, hlw, hlm, ?_, ?_, ?_⟩ <;>
    simp only [FS.setv_env, Function.update_of_ne (Ne.symm hi.1), Function.update_of_ne (Ne.symm hi.2.1),
      Function.update_of_ne (Ne.symm hi.2.2.1), Function.update_of_ne (Ne.symm hi.2.2.2)] <;> assumption

/-- **One level of the recursion** (`Lvl.step`, proof of `thm:short-pcp-ours`). -/
theorem stepP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl)
    (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length) (hok : fieldOk G s.fl s.fp = true)
    (h3 : 3 ≤ x.B.length) (hK : s.fl * x.B.length + 1 ≤ G.K) (hN : x.B.length ≤ G.N)
    (hoff : s.env 41 + x.B.length + 2 ≤ G.K) :
    LRep φ s.fl u (evalS G stepP s) x.step ∧ Wr stepW s (evalS G stepP s) ∧
      (evalS G stepP s).env 41 ≤ s.env 41 + x.B.length + 2 := by
  have hl := hx
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := hl
  have hκ : x.B.length = l.length := by rw [← hlm, List.length_map]
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  set s1 := s.setv 44 (x.B.length / 2) with hs1
  have hx1 : LRep φ s1.fl u s1 x := hx.setv 44 (by decide) _
  have e1 : evalS G stepP s = evalS G (.ite (.mul (.lt (.v 41) (.v 43)) (.eq (.md (.shr (.v 42) (.v 41)) (.k 2))
      (.k 0))) rowP colP) s1 := by
    simp only [stepP, evalS_seq, evalS_set, evalE, h39, hc2, hκ, s1]
  have hcond : (evalE G s1 (.mul (.lt (.v 41) (.v 43)) (.eq (.md (.shr (.v 42) (.v 41)) (.k 2)) (.k 0))) = 0) ↔
      ¬ x.r.head? = some false := by
    rw [hr, head_drop_iff]
    simp only [evalE, s1, FS.setv_env, Function.update_of_ne (show (41 : Var) ≠ 44 by decide),
      Function.update_of_ne (show (43 : Var) ≠ 44 by decide), Function.update_of_ne (show (42 : Var) ≠ 44 by decide),
      h42, h43, hc2, hc0]
    split_ifs <;> simp_all [hc1]
  have s1W : Wr stepW s s1 := Wr.setv s (by decide) _
  rw [e1, evalS_ite]
  by_cases hh : x.r.head? = some false
  · rw [if_neg (fun h => (hcond.mp h) hh)]
    have hrow := rowP_spec G s1 φ u x hx1 (by simp [s1, h23]) (by simp [s1]) (by simp [s1, h42]) hok h3 hK hN
      (by simp [s1]; exact hoff)
    refine ⟨?_, s1W.trans hrow.2.1, by simpa [s1] using hrow.2.2⟩
    rw [Lvl.step, if_pos hh]
    exact hrow.1
  · rw [if_pos (hcond.mpr hh)]
    have hcol := colP_spec G s1 φ u x hx1 (by simp [s1, h23]) (by simp [s1]) hok hK hN (by simp [s1]; exact hoff)
    refine ⟨?_, s1W.trans hcol.2.1, by simpa [s1] using hcol.2.2⟩
    rw [Lvl.step, if_neg hh]
    exact hcol.1

end NearCubicGates.Adapters.ShortPCP.Machines.FL
