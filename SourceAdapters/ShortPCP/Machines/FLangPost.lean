import SourceAdapters.ShortPCP.Machines.FLangZf

/-!
# Single-run time, machine layer 19: `Translate`'s post-processing at one level

BCGT13 §12.3.1 (d) viii–xi and (e) vi–ix; proof of `thm:short-pcp-ours` ("Its recursion roughly halves the dimension of the current
affine subspace at each level and does poly(f) field operations per level"). `Time.translateF` is a right fold of
`Lvl.post` over the levels (`Time.translateF_iter`). `postP` applies `Lvl.post` of the level held in `38`–`41` to the
result held in `52` (tag: `0` a point of the implicit input, `1` a proof index), `53` (the point's word) and `54`
(the index) (`TRep`); `length_{RS,=}` is read from the table in `17`/`18` (`TblRep`). The row branch (coin `0`)
compares `Z_{L0}(α + O)` with `β' = Z_{L0}(β)`, the column branch compares `Z_{L0}(α + O)` with the next level's
point (`zfP`); the indices are the closed forms of `Lvl.post` (`post_row`, `post_col`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## Expressions without clamping -/

section Eval

variable {G} {s : FS}

theorem eE_v (i : Var) : evalE G s (.v i) = s.env i := rfl

theorem eE_k {n : ℕ} (h : n ≤ G.cap) : evalE G s (.k n) = n := min_eq_left h

theorem eE_add {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) (h : x + y ≤ G.cap) :
    evalE G s (.add a b) = x + y := by simp only [evalE, ha, hb, min_eq_left h]

theorem eE_sub {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) :
    evalE G s (.sub a b) = x - y := by simp only [evalE, ha, hb]

theorem eE_mul {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) (h : x * y ≤ G.cap) :
    evalE G s (.mul a b) = x * y := by simp only [evalE, ha, hb, min_eq_left h]

theorem eE_md {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) :
    evalE G s (.md a b) = x % y := by simp only [evalE, ha, hb]

theorem eE_div {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) :
    evalE G s (.div a b) = x / y := by simp only [evalE, ha, hb]

theorem eE_shr {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) :
    evalE G s (.shr a b) = x / 2 ^ y := by simp only [evalE, ha, hb]

theorem eE_pow {a : E} {x : ℕ} (ha : evalE G s a = x) (h : x + 1 ≤ G.K) : evalE G s (.shl (.k 1) a) = 2 ^ x := by
  have h1 : min 1 G.cap = 1 := min_cap (by omega)
  simp only [evalE, ha, h1, one_mul, min_cap_pow h]

theorem eE_eq {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) :
    evalE G s (.eq a b) = if x = y then 1 else 0 := by simp only [evalE, ha, hb]

theorem eE_lt {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) :
    evalE G s (.lt a b) = if x < y then 1 else 0 := by simp only [evalE, ha, hb]

theorem eE_fadd {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) (hx : x < 2 ^ s.fl)
    (hy : y < 2 ^ s.fl) : evalE G s (.fadd a b) = x ^^^ y := by
  simp only [evalE, ha, hb]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx hy)

end Eval

/-! ## Representations -/

/-- `Translate`'s result in `52` (tag), `53` (point word), `54` (index); input indices are at most `2^w`. -/
def TRep {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (w : ℕ) (s : FS) : TrOut F → Prop
  | .inp α j => s.env 52 = 0 ∧ s.env 53 < 2 ^ w ∧ ev φ (s.env 53) = α ∧ s.env 54 = j ∧ j ≤ 2 ^ w
  | .prf j => s.env 52 = 1 ∧ s.env 54 = j

/-- The DP tables in `17`/`18` (word width `8f + 16`): `length_{RS,=}` and `rand_{RS,=}` at `0, …, f` (BCGT13
recursions (28) and (27)). -/
def TblRep (s : FS) (f : ℕ) : Prop :=
  s.env 17 = 8 * f + 16 ∧ ∃ l : List ℕ, s.env 18 = packW (8 * f + 16) l ∧ (∀ a ∈ l, a < 2 ^ (8 * f + 16)) ∧
    ∀ j ≤ f, l.getD j 0 = lengthEq T0 j ∧ l.getD (f + 1 + j) 0 = randEq T0 j

theorem TblRep.congr {s t : FS} {f : ℕ} (h : TblRep s f) (h17 : t.env 17 = s.env 17) (h18 : t.env 18 = s.env 18) :
    TblRep t f := by
  obtain ⟨a, l, b, c⟩ := h; exact ⟨h17.trans a, l, h18.trans b, c⟩

theorem TblRep.of_wr {s t : FS} {f : ℕ} {W : List Var} (h : TblRep s f) (hw : Wr W s t) (h17 : (17 : Var) ∉ W)
    (h18 : (18 : Var) ∉ W) : TblRep t f := h.congr (hw.env 17 h17) (hw.env 18 h18)

/-- The table entry `j` (for `j ≤ f`) of `length_{RS,=}`. -/
theorem TblRep.len {t : FS} {f : ℕ} (h : TblRep t f) {e : E} {j : ℕ} (he : evalE G t e = j) (hj : j ≤ f)
    (hK : (f + 1) * (8 * f + 16) + 1 ≤ G.K) : evalE G t (getT e) = lengthEq T0 j := by
  obtain ⟨h17, l, h18, hl, hv⟩ := h
  have e1 : (f + 1) * (8 * f + 16) = f * (8 * f + 16) + (8 * f + 16) := by ring
  have e2 : j * (8 * f + 16) ≤ f * (8 * f + 16) := Nat.mul_le_mul_right _ hj
  rw [getT_eval G t e (8 * f + 16) j l hl h18 h17 he (by omega) (by omega)]
  exact (hv j hj).1

/-! ## `Lvl.post` in closed form -/

section Closed

variable {F : Type} [Field F] [DecidableEq F]

/-- The row branch of `Lvl.post` (`Bk = B.take k`, `β'` the image of the row point). -/
def rowRes (Bk : List F) (O β' : F) (κ k rv : ℕ) : TrOut F → TrOut F
  | .inp α ι => if zFast Bk (α + O) = β' then .inp α (rowIdx k rv ι) else .prf (2 ^ κ + 2 ^ (k + 2) * rv + ι)
  | .prf ι => .prf ((ι - 2 ^ (k + 2) + 2 ^ κ) + 2 ^ (κ + 2) + rv * lengthEq T0 (k + 2))

/-- The column branch of `Lvl.post` (`α` the column point). -/
def colRes (Bk : List F) (O α : F) (κ k av : ℕ) : TrOut F → TrOut F
  | .inp β' ι => if zFast Bk (α + O) = β' then .inp α (1 + av) else .prf (2 ^ κ + 2 ^ (k + 2) * (ι - 1) + (1 + av))
  | .prf ι => .prf ((ι - 2 ^ (κ - k) + 2 ^ κ) + 2 ^ (κ + 2) + 2 ^ (κ - k) * lengthEq T0 (k + 2) +
      av * lengthEq T0 (κ - k))

theorem pow_split (κ k : ℕ) (hk : k ≤ κ) : 2 ^ (k + 1 + 1) * 2 ^ (κ - k) = 2 ^ (κ + 2) := by
  rw [← pow_add]; congr 1; omega

theorem post_row (x : Lvl F) (res : TrOut F) (h : x.r.head? = some false) :
    x.post res = rowRes (x.B.take (x.B.length / 2)) x.O
      (zFast (x.B.take (x.B.length / 2)) (sel (x.B.drop (x.B.length / 2))
        (bitsValue ((x.r.drop 1).take (x.B.length - x.B.length / 2))) + x.O + x.O))
      x.B.length (x.B.length / 2) (bitsValue ((x.r.drop 1).take (x.B.length - x.B.length / 2))) res := by
  have hk : x.B.length / 2 ≤ x.B.length := Nat.div_le_self _ _
  unfold Lvl.post
  simp only [h, if_true, List.length_drop]
  cases res with
  | inp α ι => rfl
  | prf ι => simp only [rowRes, pow_split _ _ hk]

theorem post_col (x : Lvl F) (res : TrOut F) (h : ¬ x.r.head? = some false) :
    x.post res = colRes (x.B.take (x.B.length / 2)) x.O
      (sel (x.B.take (x.B.length / 2 + 1)) (bitsValue ((x.r.drop 1).take (x.B.length / 2 + 1))) + x.O)
      x.B.length (x.B.length / 2) (bitsValue ((x.r.drop 1).take (x.B.length / 2 + 1))) res := by
  have hk : x.B.length / 2 ≤ x.B.length := Nat.div_le_self _ _
  unfold Lvl.post
  simp only [h, if_false, List.length_drop]
  cases res with
  | inp α ι => rfl
  | prf ι => simp only [colRes, pow_split _ _ hk]

end Closed

/-! ## The program -/

/-- `2^e`. -/
abbrev pw (e : E) : E := .shl (.k 1) e

/-- `rv`: the `κ − k` coins after the level's first coin (`44 = k`). -/
def rvE : E := .md (.shr (.v 42) (.add (.v 41) (.k 1))) (pw (.sub (.v 39) (.v 44)))

/-- `av`: the `k + 1` coins after the level's first coin. -/
def avE : E := .md (.shr (.v 42) (.add (.v 41) (.k 1))) (pw (.add (.v 44) (.k 1)))

/-- Row branch, first part: `45 := rv`, `24 := sel (B.drop k) rv`, `26`/`27 := B.take k`, `55 := β'`. -/
def rowPre : S :=
  .seq (.set 45 rvE) (.seq (.set 20 (.shr (.v 38) (.mul (.v 44) (.v 23)))) (.seq (.set 21 (.sub (.v 39) (.v 44)))
  (.seq (.set 22 (.v 45)) (.seq selP (.seq (.set 26 (.md (.v 38) (pw (.mul (.v 44) (.v 23))))) (.seq (.set 27 (.v 44))
  (.seq (zfP (.fadd (.fadd (.v 24) (.v 40)) (.v 40))) (.set 55 (.v 28)))))))))

def rowSmallE : E := .add (.k 1) (.md (.sub (.v 54) (.k 1)) (pw (.add (.v 44) (.k 2))))
def rowOutE : E := .add (.add (pw (.v 39)) (.mul (pw (.add (.v 44) (.k 2))) (.v 45))) (.v 54)
def rowPrfE : E :=
  .add (.add (.add (.sub (.v 54) (pw (.add (.v 44) (.k 2)))) (pw (.v 39))) (pw (.add (.v 39) (.k 2))))
    (.mul (.v 45) (getT (.add (.v 44) (.k 2))))

/-- Row branch, second part (on the result). -/
def rowCase : S :=
  .ite (.eq (.v 52) (.k 0))
    (.seq (zfP (.fadd (.v 53) (.v 40)))
      (.ite (.eq (.v 28) (.v 55)) (.ite (.lt (.v 45) (.k 2)) (.set 54 rowSmallE) (.set 54 rowIdxE))
        (.seq (.set 52 (.k 1)) (.set 54 rowOutE))))
    (.set 54 rowPrfE)

/-- Column branch, first part: `45 := av`, `46 := α = sel (B.take (k+1)) av + O`, `28 := Z_{L0}(α + O)`. -/
def colPre : S :=
  .seq (.set 45 avE) (.seq (.set 20 (.md (.v 38) (pw (.mul (.add (.v 44) (.k 1)) (.v 23)))))
  (.seq (.set 21 (.add (.v 44) (.k 1))) (.seq (.set 22 (.v 45)) (.seq selP (.seq (.set 46 (.fadd (.v 24) (.v 40)))
  (.seq (.set 26 (.md (.v 38) (pw (.mul (.v 44) (.v 23))))) (.seq (.set 27 (.v 44)) (zfP (.fadd (.v 46) (.v 40))))))))))

def colOutE : E :=
  .add (.add (pw (.v 39)) (.mul (pw (.add (.v 44) (.k 2))) (.sub (.v 54) (.k 1)))) (.add (.k 1) (.v 45))
def colPrfE : E :=
  .add (.add (.add (.add (.sub (.v 54) (pw (.sub (.v 39) (.v 44)))) (pw (.v 39))) (pw (.add (.v 39) (.k 2))))
    (.mul (pw (.sub (.v 39) (.v 44))) (getT (.add (.v 44) (.k 2))))) (.mul (.v 45) (getT (.sub (.v 39) (.v 44))))

/-- Column branch, second part (on the result). -/
def colCase : S :=
  .ite (.eq (.v 52) (.k 0))
    (.ite (.eq (.v 28) (.v 53)) (.seq (.set 53 (.v 46)) (.set 54 (.add (.k 1) (.v 45))))
      (.seq (.set 52 (.k 1)) (.set 54 colOutE)))
    (.set 54 colPrfE)

/-- The level's first coin is `0`. -/
def headC : E := .mul (.lt (.v 41) (.v 43)) (.eq (.md (.shr (.v 42) (.v 41)) (.k 2)) (.k 0))

/-- **`Lvl.post` of the level in `38`–`41`** on the result in `52`–`54`. -/
def postP : S := .seq (.set 44 (.div (.v 39) (.k 2))) (.ite headC (.seq rowPre rowCase) (.seq colPre colCase))

/-- The variables `postP` writes. -/
def postW : List Var := [44, 45, 20, 21, 22, 24, 25, 26, 27, 46, 52, 53, 54, 55] ++ zfW

/-! ## Transport of the routine specifications along a field-preserving state change -/

theorem selP_at {F : Type} [Field F] (s0 s : FS) (φ : AdjoinRoot (GF.toPoly s0.fp) →+* F) (hp : s.fp = s0.fp)
    (hl : s.fl = s0.fl) (l : List ℕ) (hlw : ∀ a ∈ l, a < 2 ^ s0.fl) (h20 : s.env 20 = packW s0.fl l)
    (h21 : s.env 21 = l.length) (h23 : s.env 23 = s0.fl) (hok : fieldOk G s0.fl s0.fp = true)
    (hcap : l.length * s0.fl ≤ G.cap) (hN : l.length ≤ G.N) :
    let t := evalS G selP s
    t.env 24 < 2 ^ s0.fl ∧ ev φ (t.env 24) = sel (l.map (ev φ)) (s.env 22) ∧ Wr [24, 25] s t := by
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s
  obtain rfl : fp = s0.fp := hp
  obtain rfl : fl = s0.fl := hl
  exact selP_spec G ⟨env, out, s0.fl, s0.fp, ip, bad⟩ φ l hlw h20 h21 h23 hok hcap hN

theorem zfP_at {F : Type} [Field F] [CharP F 2] (s0 s : FS) (φ : AdjoinRoot (GF.toPoly s0.fp) →+* F)
    (hp : s.fp = s0.fp) (hl : s.fl = s0.fl) (y : E) (B : List ℕ) (yw : ℕ) (hB : ∀ a ∈ B, a < 2 ^ s0.fl)
    (hy : evalE G s y = yw) (hyw : yw < 2 ^ s0.fl) (h26 : s.env 26 = packW s0.fl B) (h27 : s.env 27 = B.length)
    (h23 : s.env 23 = s0.fl) (hok : fieldOk G s0.fl s0.fp = true) (hK : s0.fl * (B.length + 1) + 1 ≤ G.K)
    (hN : B.length + 1 ≤ G.N) :
    let t := evalS G (zfP y) s
    t.env 28 < 2 ^ s0.fl ∧ ev φ (t.env 28) = zFast (B.map (ev φ)) (ev φ yw) ∧ Wr zfW s t := by
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s
  obtain rfl : fp = s0.fp := hp
  obtain rfl : fl = s0.fl := hl
  exact zfP_spec G ⟨env, out, s0.fl, s0.fp, ip, bad⟩ φ y B yw hB hy hyw h26 h27 h23 hok hK hN

/-! ## The row branch -/

/-- The variables of the row branch's first part. -/
def rowPreW : List Var := [45, 20, 21, 22, 24, 25, 26, 27, 55] ++ zfW

theorem rowPre_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u)
    (h44 : s.env 44 = x.B.length / 2) (hok : fieldOk G s.fl s.fp = true) (h3 : 3 ≤ x.B.length)
    (hK : s.fl * x.B.length + 1 ≤ G.K) (hN : x.B.length ≤ G.N) (hoff : s.env 41 + x.B.length + 2 ≤ G.K) :
    let t := evalS G rowPre s
    t.env 45 = bitsValue ((x.r.drop 1).take (x.B.length - x.B.length / 2)) ∧ t.env 55 < 2 ^ s.fl ∧
      ev φ (t.env 55) = zFast (x.B.take (x.B.length / 2)) (sel (x.B.drop (x.B.length / 2))
        (bitsValue ((x.r.drop 1).take (x.B.length - x.B.length / 2))) + x.O + x.O) ∧
      (∃ lk : List ℕ, t.env 26 = packW s.fl lk ∧ lk.length = x.B.length / 2 ∧ (∀ a ∈ lk, a < 2 ^ s.fl) ∧
        lk.map (ev φ) = x.B.take (x.B.length / 2)) ∧ t.env 27 = x.B.length / 2 ∧ Wr rowPreW s t := by
  intro t
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := hx
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hκ : x.B.length = l.length := by rw [← hlm, List.length_map]
  rw [hκ] at h44 hK hN hoff h3 ⊢
  obtain ⟨k, hk⟩ : ∃ k, k = l.length / 2 := ⟨_, rfl⟩
  rw [← hk] at h44 ⊢
  have hkκ : k ≤ l.length := by rw [hk]; exact Nat.div_le_self _ _
  have hmulκ : ∀ j, j ≤ l.length → j * s.fl ≤ s.fl * l.length := fun j hj => by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hj
  have hlK : l.length ≤ s.fl * l.length := Nat.le_mul_of_pos_left _ hf1
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  obtain ⟨rv, hrv⟩ : ∃ rv, rv = bitsValue ((x.r.drop 1).take (l.length - k)) := ⟨_, rfl⟩
  rw [← hrv]
  have hrv' : rv = bitsValue u / 2 ^ (s.env 41 + 1) % 2 ^ (l.length - k) := by
    rw [hrv, hr, List.drop_drop, bitsValue_window]
  have e45 : evalE G s rvE = rv := by
    have e1 : min (s.env 41 + 1) G.cap = s.env 41 + 1 := min_cap (by omega)
    have e2 : min (2 ^ (l.length - k)) G.cap = 2 ^ (l.length - k) := min_cap_pow (by omega)
    simp only [rvE, pw, evalE, h42, h39, h44, hc1, one_mul, e1, e2]; exact hrv'.symm
  have hdw : ∀ a ∈ l.drop k, a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_drop ha)
  have hlk : (l.drop k).length = l.length - k := List.length_drop
  have hkK : k * s.fl ≤ G.K := by have := hmulκ k hkκ; omega
  have hs1 : evalS G (.set 22 (.v 45)) (evalS G (.set 21 (.sub (.v 39) (.v 44)))
      (evalS G (.set 20 (.shr (.v 38) (.mul (.v 44) (.v 23)))) (evalS G (.set 45 rvE) s))) =
      (((s.setv 45 rv).setv 20 (packW s.fl (l.drop k))).setv 21 (l.length - k)).setv 22 rv := by
    rw [show evalS G (.set 45 rvE) s = s.setv 45 rv by rw [evalS_set, e45]]
    simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false,
      if_true, h38, h44, h23, h39, min_cap hkK]
    rw [packW_drop _ l hlw, mul_comm k s.fl]
  obtain ⟨h24, hsel24, selW⟩ := selP_at G s ((((s.setv 45 rv).setv 20 (packW s.fl (l.drop k))).setv 21
      (l.length - k)).setv 22 rv) φ rfl rfl (l.drop k) hdw (by simp) (by simp [hlk])
    (by simp (config := { decide := true }) [Function.update_apply, h23]) hok
    (by rw [hlk]; have := hmulκ (l.length - k) (by omega); have := cap_ge G; omega) (by rw [hlk]; omega)
  generalize ht3 : evalS G selP ((((s.setv 45 rv).setv 20 (packW s.fl (l.drop k))).setv 21
    (l.length - k)).setv 22 rv) = t3 at h24 hsel24 selW
  have t3W : Wr [45, 20, 21, 22, 24, 25] s t3 :=
    ((((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)).trans (selW.mono (by decide))
  have t3fl : t3.fl = s.fl := t3W.fl
  have t3fp : t3.fp = s.fp := t3W.fp
  have f38 : t3.env 38 = packW s.fl l := (t3W.env 38 (by decide)).trans h38
  have f44 : t3.env 44 = k := (t3W.env 44 (by decide)).trans h44
  have f23 : t3.env 23 = s.fl := (t3W.env 23 (by decide)).trans h23
  have f40 : t3.env 40 = s.env 40 := t3W.env 40 (by decide)
  have f45 : t3.env 45 = rv := by rw [selW.env 45 (by decide)]; simp (config := { decide := true }) [Function.update_apply]
  have hkK1 : k * s.fl + 1 ≤ G.K := by have := hmulκ k hkκ; omega
  have hs2 : evalS G (.set 27 (.v 44)) (evalS G (.set 26 (.md (.v 38) (pw (.mul (.v 44) (.v 23))))) t3) =
      (t3.setv 26 (packW s.fl (l.take k))).setv 27 k := by
    simp (config := { decide := true }) only [evalS_set, evalE, pw, FS.setv_env, Function.update_apply, if_false,
      f38, f44, f23, hc1, one_mul, min_cap hkK, min_cap_pow hkK1]
    rw [packW_take _ l hlw, mul_comm s.fl k]
  have hB : ∀ a ∈ l.take k, a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_take ha)
  have hlt : (l.take k).length = k := by rw [List.length_take]; omega
  have hyw : evalE G ((t3.setv 26 (packW s.fl (l.take k))).setv 27 k) (.fadd (.fadd (.v 24) (.v 40)) (.v 40)) =
      (t3.env 24 ^^^ s.env 40) ^^^ s.env 40 := by
    have a1 : evalE G ((t3.setv 26 (packW s.fl (l.take k))).setv 27 k) (.v 24) = t3.env 24 := by
      simp (config := { decide := true }) [evalE, Function.update_apply]
    have a2 : evalE G ((t3.setv 26 (packW s.fl (l.take k))).setv 27 k) (.v 40) = s.env 40 := by
      simp (config := { decide := true }) [evalE, Function.update_apply, f40]
    have hfl : ((t3.setv 26 (packW s.fl (l.take k))).setv 27 k).fl = s.fl := by simp [t3fl]
    rw [eE_fadd (eE_fadd a1 a2 (by rw [hfl]; exact h24) (by rw [hfl]; exact h40)) a2
      (by rw [hfl]; exact Nat.xor_lt_two_pow h24 h40) (by rw [hfl]; exact h40)]
  obtain ⟨z28, hz28, zW⟩ := zfP_at G s ((t3.setv 26 (packW s.fl (l.take k))).setv 27 k) φ (by simp [t3fp])
    (by simp [t3fl]) (.fadd (.fadd (.v 24) (.v 40)) (.v 40)) (l.take k) _ hB hyw
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h24 h40) h40) (by simp) (by simp [hlt])
    (by simp (config := { decide := true }) [Function.update_apply, f23]) hok
    (by rw [hlt]; have := hmulκ (k + 1) (by omega); have e : (k + 1) * s.fl = s.fl * (k + 1) := mul_comm _ _
        omega) (by rw [hlt]; omega)
  generalize ht4 : evalS G (zfP (.fadd (.fadd (.v 24) (.v 40)) (.v 40)))
    ((t3.setv 26 (packW s.fl (l.take k))).setv 27 k) = t4 at z28 hz28 zW
  have ht : t = t4.setv 55 (t4.env 28) := by
    show evalS G rowPre s = _
    simp only [rowPre, evalS_seq]
    rw [hs1, ht3, hs2, ht4]; rfl
  have t4W : Wr (rowPreW) s t4 :=
    (((t3W.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (zW.mono (by decide))
  refine ⟨?_, ?_, ?_, ⟨l.take k, ?_, hlt, hB, ?_⟩, ?_, ?_⟩
  · rw [ht]; simp only [FS.setv_env, Function.update_of_ne (show (45 : Var) ≠ 55 by decide)]
    rw [zW.env 45 (by decide)]; simp (config := { decide := true }) [Function.update_apply, f45]
  · rw [ht]; simpa using z28
  · rw [ht]; simp only [FS.setv_env, Function.update_self]
    rw [hz28, List.map_take, hlm, ev_xor, ev_xor, hO]
    congr 3
    refine hsel24.trans ?_
    simp only [FS.setv_env, Function.update_self, ← hlm, List.map_drop]
  · rw [ht]; simp only [FS.setv_env, Function.update_of_ne (show (26 : Var) ≠ 55 by decide)]
    rw [zW.env 26 (by decide)]; simp
  · rw [List.map_take, hlm]
  · rw [ht]; simp only [FS.setv_env, Function.update_of_ne (show (27 : Var) ≠ 55 by decide)]
    rw [zW.env 27 (by decide)]; simp
  · rw [ht]; exact t4W.trans (Wr.setv _ (by decide) _)

/-- The variables of the second parts. -/
def caseW : List Var := [52, 53, 54] ++ zfW

/-- Numeric facts shared by the two second parts. -/
theorem case_nums (f K : ℕ) (hf : 1 ≤ f) (hK : (f + 1) * (8 * f + 16) + 1 ≤ K) :
    9 * f + 21 ≤ K ∧ f * (f + 1) + 1 ≤ K ∧ 2 ^ f ≤ 2 ^ (9 * f + 16) ∧
      2 ^ (9 * f + 20) = 16 * 2 ^ (9 * f + 16) := by
  have e1 : (f + 1) * 24 ≤ (f + 1) * (8 * f + 16) := Nat.mul_le_mul_left _ (by omega)
  have e2 : f * (f + 1) ≤ (8 * f + 16) * (f + 1) := Nat.mul_le_mul_right _ (by omega)
  rw [mul_comm (8 * f + 16)] at e2
  refine ⟨by omega, by omega, Nat.pow_le_pow_right (by norm_num) (by omega), ?_⟩
  rw [show 9 * f + 20 = 9 * f + 16 + 4 by ring, pow_add]; norm_num; ring

theorem prod_le (a b f c : ℕ) (ha : a < 2 ^ f) (hb : b < 2 ^ c) : a * b ≤ 2 ^ (f + c) := by
  rw [pow_add]; exact Nat.mul_le_mul ha.le hb.le

theorem rowCase_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s0 s : FS)
    (φ : AdjoinRoot (GF.toPoly s0.fp) →+* F) (hp : s.fp = s0.fp) (hl : s.fl = s0.fl)
    (res : TrOut F) (hres : TRep φ s0.fl s res) (lk : List ℕ) (κ k rv : ℕ)
    (h26 : s.env 26 = packW s0.fl lk) (h27 : s.env 27 = k) (hlk : lk.length = k)
    (hlkw : ∀ a ∈ lk, a < 2 ^ s0.fl) (h39 : s.env 39 = κ) (h44 : s.env 44 = k) (h45 : s.env 45 = rv)
    (hrv : rv < 2 ^ (κ - k)) (h40 : s.env 40 < 2 ^ s0.fl) (h55 : s.env 55 < 2 ^ s0.fl) (h23 : s.env 23 = s0.fl)
    (hok : fieldOk G s0.fl s0.fp = true) (hirr : Irreducible (GF.toPoly s0.fp))
    (hk : k = κ / 2) (h5 : 5 ≤ κ) (hκf : κ ≤ s0.fl) (htb : TblRep s s0.fl)
    (hK : (s0.fl + 1) * (8 * s0.fl + 16) + 1 ≤ G.K) (hN : s0.fl + 1 ≤ G.N)
    (hidx : s.env 54 + 2 ^ (9 * s0.fl + 20) ≤ G.cap) :
    let t := evalS G rowCase s
    TRep φ s0.fl t (rowRes (lk.map (ev φ)) (ev φ (s.env 40)) (ev φ (s.env 55)) κ k rv res) ∧ Wr caseW s t ∧
      t.env 54 ≤ s.env 54 + 2 ^ (9 * s0.fl + 20) := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  obtain ⟨hK1, hK2, P0, PP⟩ := case_nums s0.fl G.K hf1 hK
  have hpκ : 2 ^ κ ≤ 2 ^ s0.fl := Nat.pow_le_pow_right (by norm_num) hκf
  have hκ2 : 2 ^ (κ + 2) = 4 * 2 ^ κ := by rw [pow_add]; ring
  have hk2 : 2 ^ (k + 2) * 2 ^ (κ - k) = 2 ^ (κ + 2) := by rw [← pow_add, show k + 2 + (κ - k) = κ + 2 by omega]
  have hrvk : 2 ^ (k + 2) * rv ≤ 2 ^ (κ + 2) := by rw [← hk2]; exact Nat.mul_le_mul_left _ hrv.le
  have hrvf : rv < 2 ^ s0.fl := lt_of_lt_of_le hrv (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hLE : lengthEq T0 (k + 2) < 2 ^ (8 * s0.fl + 16) :=
    lt_of_lt_of_le (lengthEq_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hprod : rv * lengthEq T0 (k + 2) ≤ 2 ^ (9 * s0.fl + 16) := by
    have := prod_le _ _ _ _ hrvf hLE; rwa [show s0.fl + (8 * s0.fl + 16) = 9 * s0.fl + 16 by ring] at this
  have hcap := cap_ge G
  have v0 : ∀ t : FS, evalE G t (.k 0) = 0 := fun t => eE_k (Nat.zero_le _)
  have v1 : ∀ t : FS, evalE G t (.k 1) = 1 := fun t => eE_k (by omega)
  have v2 : ∀ t : FS, evalE G t (.k 2) = 2 := fun t => eE_k (by omega)
  cases res with
  | inp α ι =>
    obtain ⟨r52, r53, r53e, r54, rι⟩ := hres
    have hy : evalE G s (.fadd (.v 53) (.v 40)) = s.env 53 ^^^ s.env 40 :=
      eE_fadd rfl rfl (by rw [hl]; exact r53) (by rw [hl]; exact h40)
    obtain ⟨z28, hz28, zW⟩ := zfP_at G s0 s φ hp hl _ lk _ hlkw hy (Nat.xor_lt_two_pow r53 h40) h26
      (by rw [h27, hlk]) h23 hok (by
        rw [hlk]; have := Nat.mul_le_mul_left s0.fl (show k + 1 ≤ s0.fl + 1 by omega); omega)
      (by rw [hlk]; omega)
    generalize ht1 : evalS G (zfP (.fadd (.v 53) (.v 40))) s = t1 at z28 hz28 zW
    rw [ev_xor, r53e] at hz28
    have t52 : t1.env 52 = 0 := (zW.env 52 (by decide)).trans r52
    have t53 : t1.env 53 = s.env 53 := zW.env 53 (by decide)
    have t54 : t1.env 54 = ι := (zW.env 54 (by decide)).trans r54
    have t55 : t1.env 55 = s.env 55 := zW.env 55 (by decide)
    have t45 : t1.env 45 = rv := (zW.env 45 (by decide)).trans h45
    have t44 : t1.env 44 = k := (zW.env 44 (by decide)).trans h44
    have t39 : t1.env 39 = κ := (zW.env 39 (by decide)).trans h39
    have hpre : t = evalS G (.ite (.eq (.v 28) (.v 55)) (.ite (.lt (.v 45) (.k 2)) (.set 54 rowSmallE)
        (.set 54 rowIdxE)) (.seq (.set 52 (.k 1)) (.set 54 rowOutE))) t1 := by
      show evalS G rowCase s = _
      rw [rowCase, evalS_ite, eE_eq (eE_v 52) (v0 s), r52, if_pos rfl, if_neg one_ne_zero, evalS_seq, ht1]
    have hc : evalE G t1 (.eq (.v 28) (.v 55)) = if t1.env 28 = s.env 55 then 1 else 0 := by
      rw [eE_eq (eE_v 28) (eE_v 55), t55]
    have hb := rowIdx_bounds k rv ι κ (by omega) (by
      rw [mul_comm]; calc rv * 2 ^ k < 2 ^ (κ - k) * 2 ^ k := Nat.mul_lt_mul_of_pos_right hrv (by positivity)
        _ = 2 ^ κ := by rw [← pow_add, show κ - k + k = κ by omega])
    by_cases heq : t1.env 28 = s.env 55
    · have hz : zFast (lk.map (ev φ)) (α + ev φ (s.env 40)) = ev φ (s.env 55) :=
        hz28.symm.trans (congrArg (ev φ) heq)
      have ht : t = t1.setv 54 (rowIdx k rv ι) := by
        rw [hpre, evalS_ite, hc, if_pos heq, if_neg one_ne_zero, evalS_ite, eE_lt (eE_v 45) (v2 t1), t45]
        by_cases hr2 : rv < 2
        · have hm : (ι - 1) % 2 ^ (k + 2) < 2 ^ (k + 2) := Nat.mod_lt _ (by positivity)
          have hpk : 2 ^ (k + 2) ≤ 2 ^ s0.fl := Nat.pow_le_pow_right (by norm_num) (by omega)
          have a44 : evalE G t1 (.add (.v 44) (.k 2)) = k + 2 := eE_add t44 (v2 t1) (by omega)
          have hv : evalE G t1 rowSmallE = rowIdx k rv ι := by
            rw [rowSmallE, eE_add (v1 t1) (eE_md (eE_sub (eE_v 54) (v1 t1)) (eE_pow a44 (by omega)))
              (by rw [t54]; omega), t54]
            unfold rowIdx; rw [if_pos hr2]
          rw [if_pos hr2, if_neg one_ne_zero, evalS_set, hv]
        · have hv : evalE G t1 rowIdxE = rowIdx k rv ι :=
            rowIdxE_eval G t1 k rv ι κ t44 t45 t54 (by omega) (by
              calc rv * 2 ^ k < 2 ^ (κ - k) * 2 ^ k := Nat.mul_lt_mul_of_pos_right hrv (by positivity)
                _ = 2 ^ κ := by rw [← pow_add, show κ - k + k = κ by omega]) (by omega) (by omega)
          rw [if_neg hr2, if_pos rfl, evalS_set, hv]
      refine ⟨?_, ?_, ?_⟩
      · simp only [rowRes, if_pos hz]; rw [ht]
        refine ⟨?_, ?_, ?_, ?_, hb.2.trans hpκ⟩ <;>
          simp (config := { decide := true }) [Function.update_apply, t52, t53, r53, r53e]
      · rw [ht]; exact (zW.mono (by decide)).trans (Wr.setv (W := caseW) _ (by decide) _)
      · rw [ht]; simp only [FS.setv_env, Function.update_self]; have := hb.2; omega
    · have hz : zFast (lk.map (ev φ)) (α + ev φ (s.env 40)) ≠ ev φ (s.env 55) := by
        intro h; apply heq; exact ev_inj φ s0.fl _ _ hmod hirr z28 h55 (by rw [hz28, h])
      have hv : evalE G (t1.setv 52 1) rowOutE = 2 ^ κ + 2 ^ (k + 2) * rv + ι := by
        have a39 : evalE G (t1.setv 52 1) (.v 39) = κ := by simp [evalE, t39]
        have a44 : evalE G (t1.setv 52 1) (.v 44) = k := by simp [evalE, t44]
        have a45 : evalE G (t1.setv 52 1) (.v 45) = rv := by simp [evalE, t45]
        have a54 : evalE G (t1.setv 52 1) (.v 54) = ι := by simp [evalE, t54]
        rw [rowOutE, eE_add (eE_add (eE_pow a39 (by omega)) (eE_mul (eE_pow (eE_add a44 (v2 _) (by omega))
          (by omega)) a45 (by omega)) (by omega)) a54 (by omega)]
      have ht : t = (t1.setv 52 1).setv 54 (2 ^ κ + 2 ^ (k + 2) * rv + ι) := by
        rw [hpre, evalS_ite, hc, if_neg heq, if_pos rfl, evalS_seq, evalS_set, evalS_set, v1, hv]
      refine ⟨?_, ?_, ?_⟩
      · simp only [rowRes, if_neg hz]
        rw [ht]; simp (config := { decide := true }) [TRep, Function.update_apply]
      · rw [ht]; exact ((zW.mono (by decide)).trans (Wr.setv (W := caseW) _ (by decide) _)).trans
          (Wr.setv _ (by decide) _)
      · rw [ht]; simp only [FS.setv_env, Function.update_self]; rw [r54]; omega
  | prf ι =>
    obtain ⟨r52, r54⟩ := hres
    have hsub : ι - 2 ^ (k + 2) ≤ ι := Nat.sub_le _ _
    have hv : evalE G s rowPrfE = (ι - 2 ^ (k + 2) + 2 ^ κ) + 2 ^ (κ + 2) + rv * lengthEq T0 (k + 2) := by
      have a39 : evalE G s (.v 39) = κ := h39
      have a44 : evalE G s (.add (.v 44) (.k 2)) = k + 2 := eE_add h44 (v2 s) (by omega)
      have a45 : evalE G s (.v 45) = rv := h45
      have a54 : evalE G s (.v 54) = ι := r54
      rw [rowPrfE, eE_add (eE_add (eE_add (eE_sub a54 (eE_pow a44 (by omega))) (eE_pow a39 (by omega)) (by omega))
        (eE_pow (eE_add a39 (v2 s) (by omega)) (by omega)) (by omega))
        (eE_mul a45 (htb.len G a44 (by omega) hK) (by omega)) (by omega)]
    have ht : t = s.setv 54 ((ι - 2 ^ (k + 2) + 2 ^ κ) + 2 ^ (κ + 2) + rv * lengthEq T0 (k + 2)) := by
      show evalS G rowCase s = _
      rw [rowCase, evalS_ite, eE_eq (eE_v 52) (v0 s), r52, if_neg one_ne_zero, if_pos rfl, evalS_set, hv]
    refine ⟨?_, ?_, ?_⟩
    · rw [ht]; simp (config := { decide := true }) [rowRes, TRep, Function.update_apply, r52]
    · rw [ht]; exact Wr.setv _ (by decide) _
    · rw [ht]; simp only [FS.setv_env, Function.update_self]; rw [r54]; omega

/-! ## The column branch -/

/-- The variables of the column branch's first part. -/
def colPreW : List Var := [45, 20, 21, 22, 24, 25, 46, 26, 27] ++ zfW

theorem colPre_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u)
    (h44 : s.env 44 = x.B.length / 2) (hok : fieldOk G s.fl s.fp = true) (h3 : 3 ≤ x.B.length)
    (hK : s.fl * x.B.length + 1 ≤ G.K) (hN : x.B.length ≤ G.N) (hoff : s.env 41 + x.B.length + 2 ≤ G.K) :
    let t := evalS G colPre s
    t.env 45 = bitsValue ((x.r.drop 1).take (x.B.length / 2 + 1)) ∧ t.env 46 < 2 ^ s.fl ∧
      ev φ (t.env 46) = sel (x.B.take (x.B.length / 2 + 1)) (bitsValue ((x.r.drop 1).take (x.B.length / 2 + 1))) +
        x.O ∧ t.env 28 < 2 ^ s.fl ∧
      ev φ (t.env 28) = zFast (x.B.take (x.B.length / 2)) (ev φ (t.env 46) + x.O) ∧ Wr colPreW s t := by
  intro t
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := hx
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hκ : x.B.length = l.length := by rw [← hlm, List.length_map]
  rw [hκ] at h44 hK hN hoff h3 ⊢
  obtain ⟨k, hk⟩ : ∃ k, k = l.length / 2 := ⟨_, rfl⟩
  rw [← hk] at h44 ⊢
  have hkκ : k + 1 ≤ l.length := by omega
  have hmulκ : ∀ j, j ≤ l.length → j * s.fl ≤ s.fl * l.length := fun j hj => by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hj
  have hlK : l.length ≤ s.fl * l.length := Nat.le_mul_of_pos_left _ hf1
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  obtain ⟨av, hav⟩ : ∃ av, av = bitsValue ((x.r.drop 1).take (k + 1)) := ⟨_, rfl⟩
  rw [← hav]
  have hav' : av = bitsValue u / 2 ^ (s.env 41 + 1) % 2 ^ (k + 1) := by
    rw [hav, hr, List.drop_drop, bitsValue_window]
  have ek1 : min (k + 1) G.cap = k + 1 := min_cap (by omega)
  have e45 : evalE G s avE = av := by
    have e1 : min (s.env 41 + 1) G.cap = s.env 41 + 1 := min_cap (by omega)
    have e2 : min (2 ^ (k + 1)) G.cap = 2 ^ (k + 1) := min_cap_pow (by omega)
    simp only [avE, pw, evalE, h42, h44, hc1, one_mul, e1, e2, ek1]; exact hav'.symm
  have htw : ∀ a ∈ l.take (k + 1), a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_take ha)
  have hlt1 : (l.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
  have hk1K : (k + 1) * s.fl ≤ G.K := by have := hmulκ (k + 1) hkκ; omega
  have hk1K' : (k + 1) * s.fl + 1 ≤ G.K := by have := hmulκ (k + 1) hkκ; omega
  have hs1 : evalS G (.set 22 (.v 45)) (evalS G (.set 21 (.add (.v 44) (.k 1)))
      (evalS G (.set 20 (.md (.v 38) (pw (.mul (.add (.v 44) (.k 1)) (.v 23))))) (evalS G (.set 45 avE) s))) =
      (((s.setv 45 av).setv 20 (packW s.fl (l.take (k + 1)))).setv 21 (k + 1)).setv 22 av := by
    rw [show evalS G (.set 45 avE) s = s.setv 45 av by rw [evalS_set, e45]]
    simp (config := { decide := true }) only [evalS_set, evalE, pw, FS.setv_env, Function.update_apply, if_false,
      if_true, h38, h44, h23, hc1, one_mul, ek1, min_cap hk1K, min_cap_pow hk1K']
    rw [packW_take _ l hlw, mul_comm (k + 1) s.fl]
  obtain ⟨h24, hsel24, selW⟩ := selP_at G s ((((s.setv 45 av).setv 20 (packW s.fl (l.take (k + 1)))).setv 21
      (k + 1)).setv 22 av) φ rfl rfl (l.take (k + 1)) htw (by simp) (by simp [hlt1])
    (by simp (config := { decide := true }) [Function.update_apply, h23]) hok
    (by rw [hlt1]; have := cap_ge G; omega) (by rw [hlt1]; omega)
  generalize ht3 : evalS G selP ((((s.setv 45 av).setv 20 (packW s.fl (l.take (k + 1)))).setv 21
    (k + 1)).setv 22 av) = t3 at h24 hsel24 selW
  have t3W : Wr [45, 20, 21, 22, 24, 25] s t3 :=
    ((((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)).trans (selW.mono (by decide))
  have t3fl : t3.fl = s.fl := t3W.fl
  have t3fp : t3.fp = s.fp := t3W.fp
  have f38 : t3.env 38 = packW s.fl l := (t3W.env 38 (by decide)).trans h38
  have f44 : t3.env 44 = k := (t3W.env 44 (by decide)).trans h44
  have f23 : t3.env 23 = s.fl := (t3W.env 23 (by decide)).trans h23
  have f40 : t3.env 40 = s.env 40 := t3W.env 40 (by decide)
  have f45 : t3.env 45 = av := by rw [selW.env 45 (by decide)]; simp (config := { decide := true }) [Function.update_apply]
  have h22 : ((((s.setv 45 av).setv 20 (packW s.fl (l.take (k + 1)))).setv 21 (k + 1)).setv 22 av).env 22 = av := by
    simp
  rw [h22] at hsel24
  have hkK : k * s.fl ≤ G.K := by have := hmulκ k (by omega); omega
  have hkK1 : k * s.fl + 1 ≤ G.K := by have := hmulκ k (by omega); omega
  have hα : t3.env 24 ^^^ s.env 40 < 2 ^ s.fl := Nat.xor_lt_two_pow h24 h40
  have hs2 : evalS G (.set 27 (.v 44)) (evalS G (.set 26 (.md (.v 38) (pw (.mul (.v 44) (.v 23)))))
      (evalS G (.set 46 (.fadd (.v 24) (.v 40))) t3)) =
      ((t3.setv 46 (t3.env 24 ^^^ s.env 40)).setv 26 (packW s.fl (l.take k))).setv 27 k := by
    have a46 : evalE G t3 (.fadd (.v 24) (.v 40)) = t3.env 24 ^^^ s.env 40 :=
      eE_fadd rfl f40 (by rw [t3fl]; exact h24) (by rw [t3fl]; exact h40)
    rw [show evalS G (.set 46 (.fadd (.v 24) (.v 40))) t3 = t3.setv 46 (t3.env 24 ^^^ s.env 40) by
      rw [evalS_set, a46]]
    simp (config := { decide := true }) only [evalS_set, evalE, pw, FS.setv_env, Function.update_apply, if_false,
      f38, f44, f23, hc1, one_mul, min_cap hkK, min_cap_pow hkK1]
    rw [packW_take _ l hlw, mul_comm s.fl k]
  have hB : ∀ a ∈ l.take k, a < 2 ^ s.fl := fun a ha => hlw a (List.mem_of_mem_take ha)
  have hlt : (l.take k).length = k := by rw [List.length_take]; omega
  have hyw : evalE G (((t3.setv 46 (t3.env 24 ^^^ s.env 40)).setv 26 (packW s.fl (l.take k))).setv 27 k)
      (.fadd (.v 46) (.v 40)) = (t3.env 24 ^^^ s.env 40) ^^^ s.env 40 := by
    have hfl : (((t3.setv 46 (t3.env 24 ^^^ s.env 40)).setv 26 (packW s.fl (l.take k))).setv 27 k).fl = s.fl := by
      simp [t3fl]
    refine eE_fadd ?_ ?_ (by rw [hfl]; exact hα) (by rw [hfl]; exact h40)
    · simp (config := { decide := true }) [evalE, Function.update_apply]
    · simp (config := { decide := true }) [evalE, Function.update_apply, f40]
  obtain ⟨z28, hz28, zW⟩ := zfP_at G s (((t3.setv 46 (t3.env 24 ^^^ s.env 40)).setv 26 (packW s.fl (l.take k))).setv 27 k)
    φ (by simp [t3fp]) (by simp [t3fl]) (.fadd (.v 46) (.v 40)) (l.take k) _ hB hyw (Nat.xor_lt_two_pow hα h40)
    (by simp) (by simp [hlt]) (by simp (config := { decide := true }) [Function.update_apply, f23]) hok
    (by rw [hlt]; have := hmulκ (k + 1) (by omega); have e : (k + 1) * s.fl = s.fl * (k + 1) := mul_comm _ _
        omega) (by rw [hlt]; omega)
  generalize ht4 : evalS G (zfP (.fadd (.v 46) (.v 40)))
    (((t3.setv 46 (t3.env 24 ^^^ s.env 40)).setv 26 (packW s.fl (l.take k))).setv 27 k) = t4 at z28 hz28 zW
  have ht : t = t4 := by
    show evalS G colPre s = _
    simp only [colPre, evalS_seq]
    rw [hs1, ht3, hs2, ht4]
  have t4W : Wr colPreW s t4 :=
    ((((t3W.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)).trans (zW.mono (by decide))
  have t46 : t4.env 46 = t3.env 24 ^^^ s.env 40 := by
    rw [zW.env 46 (by decide)]; simp (config := { decide := true }) [Function.update_apply]
  have hev46 : ev φ (t4.env 46) = sel (x.B.take (k + 1)) av + x.O := by
    rw [t46, ev_xor, hO, hsel24, ← hlm, List.map_take]
  rw [ht]
  refine ⟨?_, by rw [t46]; exact hα, hev46, z28, ?_, t4W⟩
  · rw [zW.env 45 (by decide)]; simp (config := { decide := true }) [Function.update_apply, f45]
  · rw [hz28, List.map_take, hlm, ev_xor, ← t46, hO]

/-- **The column branch, second part.** -/
theorem colCase_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s0 s : FS)
    (φ : AdjoinRoot (GF.toPoly s0.fp) →+* F) (hp : s.fp = s0.fp) (hl : s.fl = s0.fl)
    (res : TrOut F) (hres : TRep φ s0.fl s res) (Bk : List F) (O α : F) (κ k av : ℕ)
    (h39 : s.env 39 = κ) (h44 : s.env 44 = k) (h45 : s.env 45 = av) (hav : av < 2 ^ (k + 1))
    (h46 : s.env 46 < 2 ^ s0.fl) (h46e : ev φ (s.env 46) = α) (h28 : s.env 28 < 2 ^ s0.fl)
    (h28e : ev φ (s.env 28) = zFast Bk (α + O))
    (hok : fieldOk G s0.fl s0.fp = true) (hirr : Irreducible (GF.toPoly s0.fp))
    (hk : k = κ / 2) (h5 : 5 ≤ κ) (hκf : κ ≤ s0.fl) (htb : TblRep s s0.fl)
    (hK : (s0.fl + 1) * (8 * s0.fl + 16) + 1 ≤ G.K)
    (hidx : s.env 54 + 2 ^ (9 * s0.fl + 20) ≤ G.cap) :
    let t := evalS G colCase s
    TRep φ s0.fl t (colRes Bk O α κ k av res) ∧ Wr [52, 53, 54] s t ∧
      t.env 54 ≤ s.env 54 + 2 ^ (9 * s0.fl + 20) := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  obtain ⟨hK1, hK2, P0, PP⟩ := case_nums s0.fl G.K hf1 hK
  have hpκ : 2 ^ κ ≤ 2 ^ s0.fl := Nat.pow_le_pow_right (by norm_num) hκf
  have hκ2 : 2 ^ (κ + 2) = 4 * 2 ^ κ := by rw [pow_add]; ring
  have havf : av < 2 ^ s0.fl := lt_of_lt_of_le hav (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcap := cap_ge G
  have v0 : ∀ t : FS, evalE G t (.k 0) = 0 := fun t => eE_k (Nat.zero_le _)
  have v1 : ∀ t : FS, evalE G t (.k 1) = 1 := fun t => eE_k (by omega)
  have v2 : ∀ t : FS, evalE G t (.k 2) = 2 := fun t => eE_k (by omega)
  cases res with
  | inp β' ι =>
    obtain ⟨r52, r53, r53e, r54, rι⟩ := hres
    have hc : evalE G s (.eq (.v 28) (.v 53)) = if s.env 28 = s.env 53 then 1 else 0 := eE_eq (eE_v 28) (eE_v 53)
    have hpre : t = evalS G (.ite (.eq (.v 28) (.v 53)) (.seq (.set 53 (.v 46)) (.set 54 (.add (.k 1) (.v 45))))
        (.seq (.set 52 (.k 1)) (.set 54 colOutE))) s := by
      show evalS G colCase s = _
      rw [colCase, evalS_ite, eE_eq (eE_v 52) (v0 s), r52, if_pos rfl, if_neg one_ne_zero]
    by_cases heq : s.env 28 = s.env 53
    · have hz : zFast Bk (α + O) = β' := by rw [← h28e, heq, r53e]
      have hv : evalE G (s.setv 53 (s.env 46)) (.add (.k 1) (.v 45)) = 1 + av :=
        eE_add (v1 _) (by simp [evalE, h45]) (by omega)
      have ht : t = (s.setv 53 (s.env 46)).setv 54 (1 + av) := by
        rw [hpre, evalS_ite, hc, if_pos heq, if_neg one_ne_zero, evalS_seq, evalS_set, evalS_set, eE_v 46, hv]
      refine ⟨?_, ?_, ?_⟩
      · simp only [colRes, if_pos hz]; rw [ht]
        refine ⟨?_, ?_, ?_, ?_, by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k + 1 ≤ s0.fl by omega); omega⟩ <;>
          simp (config := { decide := true }) [Function.update_apply, r52, h46, h46e]
      · rw [ht]; exact (Wr.setv (W := [52, 53, 54]) _ (by decide) _).trans (Wr.setv _ (by decide) _)
      · rw [ht]; simp only [FS.setv_env, Function.update_self]
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k + 1 ≤ s0.fl by omega); omega
    · have hz : ¬ zFast Bk (α + O) = β' := by
        intro h; apply heq; exact ev_inj φ s0.fl _ _ hmod hirr h28 r53 (by rw [h28e, h, r53e])
      have hm : 2 ^ (k + 2) * (ι - 1) ≤ 2 ^ (9 * s0.fl + 16) := by
        calc 2 ^ (k + 2) * (ι - 1) ≤ 2 ^ s0.fl * 2 ^ s0.fl :=
              Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega)
          _ ≤ 2 ^ (9 * s0.fl + 16) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hv : evalE G (s.setv 52 1) colOutE = 2 ^ κ + 2 ^ (k + 2) * (ι - 1) + (1 + av) := by
        have a39 : evalE G (s.setv 52 1) (.v 39) = κ := by simp [evalE, h39]
        have a44 : evalE G (s.setv 52 1) (.v 44) = k := by simp [evalE, h44]
        have a45 : evalE G (s.setv 52 1) (.v 45) = av := by simp [evalE, h45]
        have a54 : evalE G (s.setv 52 1) (.v 54) = ι := by simp [evalE, r54]
        rw [colOutE, eE_add (eE_add (eE_pow a39 (by omega)) (eE_mul (eE_pow (eE_add a44 (v2 _) (by omega))
          (by omega)) (eE_sub a54 (v1 _)) (by omega)) (by omega)) (eE_add (v1 _) a45 (by omega)) (by omega)]
      have ht : t = (s.setv 52 1).setv 54 (2 ^ κ + 2 ^ (k + 2) * (ι - 1) + (1 + av)) := by
        rw [hpre, evalS_ite, hc, if_neg heq, if_pos rfl, evalS_seq, evalS_set, evalS_set, v1, hv]
      refine ⟨?_, ?_, ?_⟩
      · simp only [colRes, if_neg hz]
        rw [ht]; simp (config := { decide := true }) [TRep, Function.update_apply]
      · rw [ht]; exact (Wr.setv (W := [52, 53, 54]) _ (by decide) _).trans (Wr.setv _ (by decide) _)
      · rw [ht]; simp only [FS.setv_env, Function.update_self]; rw [r54]; omega
  | prf ι =>
    obtain ⟨r52, r54⟩ := hres
    have hsub : ι - 2 ^ (κ - k) ≤ ι := Nat.sub_le _ _
    have hLE1 : lengthEq T0 (k + 2) < 2 ^ (8 * s0.fl + 16) :=
      lt_of_lt_of_le (lengthEq_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hLE2 : lengthEq T0 (κ - k) < 2 ^ (8 * s0.fl + 16) :=
      lt_of_lt_of_le (lengthEq_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hqf : 2 ^ (κ - k) < 2 ^ s0.fl := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hqf' : 2 ^ (κ - k) ≤ 2 ^ (9 * s0.fl + 16) := by omega
    have p1 : 2 ^ (κ - k) * lengthEq T0 (k + 2) ≤ 2 ^ (9 * s0.fl + 16) := by
      have := prod_le _ _ _ _ hqf hLE1; rwa [show s0.fl + (8 * s0.fl + 16) = 9 * s0.fl + 16 by ring] at this
    have p2 : av * lengthEq T0 (κ - k) ≤ 2 ^ (9 * s0.fl + 16) := by
      have := prod_le _ _ _ _ havf hLE2; rwa [show s0.fl + (8 * s0.fl + 16) = 9 * s0.fl + 16 by ring] at this
    have hv : evalE G s colPrfE = (ι - 2 ^ (κ - k) + 2 ^ κ) + 2 ^ (κ + 2) + 2 ^ (κ - k) * lengthEq T0 (k + 2) +
        av * lengthEq T0 (κ - k) := by
      have a39 : evalE G s (.v 39) = κ := h39
      have a44 : evalE G s (.add (.v 44) (.k 2)) = k + 2 := eE_add h44 (v2 s) (by omega)
      have aq : evalE G s (.sub (.v 39) (.v 44)) = κ - k := eE_sub h39 h44
      have a45 : evalE G s (.v 45) = av := h45
      have a54 : evalE G s (.v 54) = ι := r54
      rw [colPrfE, eE_add (eE_add (eE_add (eE_add (eE_sub a54 (eE_pow aq (by omega))) (eE_pow a39 (by omega))
        (by omega)) (eE_pow (eE_add a39 (v2 s) (by omega)) (by omega)) (by omega))
        (eE_mul (eE_pow aq (by omega)) (htb.len G a44 (by omega) hK) (by omega)) (by omega))
        (eE_mul a45 (htb.len G aq (by omega) hK) (by omega)) (by omega)]
    have ht : t = s.setv 54 ((ι - 2 ^ (κ - k) + 2 ^ κ) + 2 ^ (κ + 2) + 2 ^ (κ - k) * lengthEq T0 (k + 2) +
        av * lengthEq T0 (κ - k)) := by
      show evalS G colCase s = _
      rw [colCase, evalS_ite, eE_eq (eE_v 52) (v0 s), r52, if_neg one_ne_zero, if_pos rfl, evalS_set, hv]
    refine ⟨?_, ?_, ?_⟩
    · rw [ht]; simp (config := { decide := true }) [colRes, TRep, Function.update_apply, r52]
    · rw [ht]; exact Wr.setv _ (by decide) _
    · rw [ht]; simp only [FS.setv_env, Function.update_self]; rw [r54]; omega

/-! ## One level -/

theorem TRep.congr {F : Type} [Field F] {p : ℕ} {φ : AdjoinRoot (GF.toPoly p) →+* F} {w : ℕ} {s t : FS}
    {r : TrOut F} (h : TRep φ w s r) (h52 : t.env 52 = s.env 52) (h53 : t.env 53 = s.env 53)
    (h54 : t.env 54 = s.env 54) : TRep φ w t r := by
  cases r with
  | inp α j => obtain ⟨a, b, c, d, e⟩ := h; exact ⟨h52.trans a, h53 ▸ b, h53 ▸ c, h54.trans d, e⟩
  | prf j => obtain ⟨a, b⟩ := h; exact ⟨h52.trans a, h54.trans b⟩

/-- **`Lvl.post` of the level in `38`–`41`** on the result in `52`–`54` (BCGT13 §12.3.1; proof of `thm:short-pcp-ours`): the
result is `x.post res`, and the index grows by at most `2^(9f+20)`. -/
theorem postP_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s : FS)
    (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (x : Lvl F) (res : TrOut F)
    (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length)
    (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp)) (hst : ¬ x.stop = true)
    (hκf : x.B.length ≤ s.fl) (htb : TblRep s s.fl) (hres : TRep φ s.fl s res)
    (hK : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K) (hN : s.fl + 1 ≤ G.N)
    (hoff : s.env 41 + x.B.length + 2 ≤ G.K) (hidx : s.env 54 + 2 ^ (9 * s.fl + 20) ≤ G.cap) :
    let t := evalS G postP s
    TRep φ s.fl t (x.post res) ∧ Wr postW s t ∧ t.env 54 ≤ s.env 54 + 2 ^ (9 * s.fl + 20) := by
  intro t
  have h5 : 5 ≤ x.B.length := by simp [Lvl.stop] at hst; omega
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  obtain ⟨hK1, hK2, -, -⟩ := case_nums s.fl G.K hf1 hK
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have hl := hx
  obtain ⟨l, -, h39, -, hlm, h40, hO, hr⟩ := hl
  have h39' : s.env 39 = x.B.length := by rw [h39, ← hlm, List.length_map]
  have hKκ : s.fl * x.B.length + 1 ≤ G.K := by
    have := Nat.mul_le_mul_left s.fl hκf
    have e : s.fl * (s.fl + 1) = s.fl * s.fl + s.fl := by ring
    omega
  set s1 := s.setv 44 (x.B.length / 2) with hs1
  have hx1 : LRep φ s1.fl u s1 x := hx.setv 44 (by decide) _
  have e1 : evalS G postP s = evalS G (.ite headC (.seq rowPre rowCase) (.seq colPre colCase)) s1 := by
    simp only [postP, evalS_seq, evalS_set, evalE, h39', hc2, s1]
  have hcond : (evalE G s1 headC = 0) ↔ ¬ x.r.head? = some false := by
    rw [hr, head_drop_iff]
    simp only [headC, evalE, s1, FS.setv_env, Function.update_of_ne (show (41 : Var) ≠ 44 by decide),
      Function.update_of_ne (show (43 : Var) ≠ 44 by decide), Function.update_of_ne (show (42 : Var) ≠ 44 by decide),
      h42, h43, hc2, hc0]
    split_ifs <;> simp_all [hc1]
  have s1W : Wr postW s s1 := Wr.setv s (by decide) _
  have g23 : s1.env 23 = s1.fl := by simp [s1, h23]
  have g42 : s1.env 42 = bitsValue u := by simp [s1, h42]
  have g44 : s1.env 44 = x.B.length / 2 := by simp [s1]
  have g41 : s1.env 41 + x.B.length + 2 ≤ G.K := by simp [s1]; exact hoff
  show TRep φ s.fl (evalS G postP s) _ ∧ Wr postW s (evalS G postP s) ∧ (evalS G postP s).env 54 ≤ _
  rw [e1, evalS_ite]
  by_cases hh : x.r.head? = some false
  · rw [if_neg (fun h => (hcond.mp h) hh), evalS_seq, post_row x res hh]
    obtain ⟨r45, r55, r55e, ⟨lk, r26, rlk, rlkw, rlkm⟩, r27, rW⟩ :=
      rowPre_spec G s1 φ u x hx1 g23 g42 g44 hok (by omega) hKκ (by omega) g41
    generalize ht1 : evalS G rowPre s1 = t1 at r45 r55 r55e r26 r27 rW ⊢
    have tW : Wr postW s t1 := s1W.trans (rW.mono (by decide))
    have hrv : bitsValue ((x.r.drop 1).take (x.B.length - x.B.length / 2)) < 2 ^ (x.B.length - x.B.length / 2) :=
      lt_of_lt_of_le (bv_lt _) (Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _))
    have q39 : t1.env 39 = x.B.length := (rW.env 39 (by decide)).trans (by simp [s1, h39'])
    have q44 : t1.env 44 = x.B.length / 2 := (rW.env 44 (by decide)).trans g44
    have q40 : t1.env 40 = s.env 40 := (rW.env 40 (by decide)).trans (by simp [s1])
    have q23 : t1.env 23 = s.fl := (tW.env 23 (by decide)).trans h23
    have q52 : t1.env 52 = s.env 52 := (rW.env 52 (by decide)).trans (by simp [s1])
    have q53 : t1.env 53 = s.env 53 := (rW.env 53 (by decide)).trans (by simp [s1])
    have q54 : t1.env 54 = s.env 54 := (rW.env 54 (by decide)).trans (by simp [s1])
    have htb1 : TblRep t1 s.fl := htb.of_wr tW (by decide) (by decide)
    obtain ⟨c1, c2, c3⟩ := rowCase_spec G s t1 φ tW.fp tW.fl res (hres.congr q52 q53 q54) lk x.B.length
      (x.B.length / 2) _ r26 r27 rlk rlkw q39 q44 r45 hrv (by rw [q40]; exact h40) r55 q23 hok hirr rfl h5 hκf
      htb1 hK hN (by rw [q54]; exact hidx)
    have rlkm' : lk.map (ev φ) = x.B.take (x.B.length / 2) := rlkm
    have r55e' : ev φ (t1.env 55) = zFast (x.B.take (x.B.length / 2)) (sel (x.B.drop (x.B.length / 2))
        (bitsValue ((x.r.drop 1).take (x.B.length - x.B.length / 2))) + x.O + x.O) := r55e
    rw [rlkm', q40, hO, r55e'] at c1
    exact ⟨c1, tW.trans (c2.mono (by decide)), by rw [q54] at c3; exact c3⟩
  · rw [if_pos (hcond.mpr hh), evalS_seq, post_col x res hh]
    obtain ⟨r45, r46, r46e, r28, r28e, rW⟩ := colPre_spec G s1 φ u x hx1 g23 g42 g44 hok (by omega) hKκ (by omega) g41
    generalize ht1 : evalS G colPre s1 = t1 at r45 r46 r46e r28 r28e rW ⊢
    have tW : Wr postW s t1 := s1W.trans (rW.mono (by decide))
    have hav : bitsValue ((x.r.drop 1).take (x.B.length / 2 + 1)) < 2 ^ (x.B.length / 2 + 1) :=
      lt_of_lt_of_le (bv_lt _) (Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _))
    have q39 : t1.env 39 = x.B.length := (rW.env 39 (by decide)).trans (by simp [s1, h39'])
    have q44 : t1.env 44 = x.B.length / 2 := (rW.env 44 (by decide)).trans g44
    have q52 : t1.env 52 = s.env 52 := (rW.env 52 (by decide)).trans (by simp [s1])
    have q53 : t1.env 53 = s.env 53 := (rW.env 53 (by decide)).trans (by simp [s1])
    have q54 : t1.env 54 = s.env 54 := (rW.env 54 (by decide)).trans (by simp [s1])
    have htb1 : TblRep t1 s.fl := htb.of_wr tW (by decide) (by decide)
    rw [r46e] at r28e
    obtain ⟨c1, c2, c3⟩ := colCase_spec G s t1 φ tW.fp tW.fl res (hres.congr q52 q53 q54) (x.B.take (x.B.length / 2))
      x.O _ x.B.length (x.B.length / 2) _ q39 q44 r45 hav r46 r46e r28 r28e hok hirr rfl h5 hκf htb1 hK
      (by rw [q54]; exact hidx)
    exact ⟨c1, tW.trans (c2.mono (by decide)), by rw [q54] at c3; exact c3⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
