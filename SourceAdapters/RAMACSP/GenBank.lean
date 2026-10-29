import SourceAdapters.RAMACSP.GenList
import SourceAdapters.Routing.LayoutPacking

/-!
# Printing the neighbor bank

Paper: the paragraph "Neighbors" of `app:affine-embedding` (the translations `X ↦ X + b`, `b ∈ H`: within a vertex the
`16C` sums `E(0,0,c,r,a)`; the two predecessor families `Γ_t` plus a role and area mask; the network edges `δ_s`,
`δ_s + e_{d_s}`, the role masks, the pair partners, the column successors `ζ_t` and the lane flips `e_b`), and
`lem:generator` ("It emits the neighbor offsets, which are sums of basis elements").

`bankGP P` prints `natWord |bank|`, then `wd b` for every entry `b` of `Routing.globalBank l` in order, for any
per-entry printer `P` that prints `wd` of its argument's value (`bankGP_spec`); the layout `l` has `k, ℓ, q` in the
program variables `31, 32, 34`. Each of the ten sections of `globalBank` is one counted loop over `50`, with the
masks as `cellMask` expressions `cellE` and exclusive-ors. Every loop runs over `< 2k`, `< k`, `< q` or `< 16C`
entries, never over `H`. With the pair printer (`pairP`) it prints the neighbors of `def:acsp`,
`listWord pairWord (globalBank l).map (1, ·)` (`bankPairP_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicWires.RepairRepresentation (natWord)

variable {G : Glob}

/-! ## Mask expressions -/

/-- `2^e`. -/
def two (e : E) : E := .shl (.k 1) e

/-- `cellMask l x s c r a` with `k, ℓ, q` in `31, 32, 34`. -/
def cellE (ex es ec er ea : E) : E :=
  .add ex (.mul (two (.v 31)) (.add es (.mul (two (.v 32)) (.add ec (.mul (two (.v 34)) (.add er (.mul (.k 8) ea)))))))

/-- The layout in the program variables. -/
structure LV (l : Routing.Layout) (t : FS) : Prop where
  k : t.env 31 = l.k
  ell : t.env 32 = l.ell
  q : t.env 34 = l.q

theorem eE_two {t : FS} {e : E} {x : ℕ} (he : evalE G t e = x) (h : x + 1 ≤ G.K) : evalE G t (two e) = 2 ^ x :=
  eE_pow he h

theorem le_mul_two_pow (a x : ℕ) : x ≤ 2 ^ a * x := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos a)

theorem cellE_eval {t : FS} {l : Routing.Layout} (hl : LV l t) {ex es ec er ea : E} {x s c r a : ℕ}
    (hx : evalE G t ex = x) (hs : evalE G t es = s) (hc : evalE G t ec = c) (hr : evalE G t er = r)
    (ha : evalE G t ea = a) (hb : Routing.cellMask l x s c r a ≤ G.cap) (hK : l.m + 1 ≤ G.K) :
    evalE G t (cellE ex es ec er ea) = Routing.cellMask l x s c r a := by
  have hm : l.m = l.k + l.ell + l.q + 4 := rfl
  unfold Routing.cellMask at hb ⊢
  generalize hV4 : r + 8 * a = V4 at hb ⊢
  generalize hV3 : c + 2 ^ l.q * V4 = V3 at hb ⊢
  generalize hV2 : s + 2 ^ l.ell * V3 = V2 at hb ⊢
  have i4 := le_mul_two_pow l.q V4
  have i3 := le_mul_two_pow l.ell V3
  have i2 := le_mul_two_pow l.k V2
  have hc8 : 8 ≤ G.cap := by
    have := cap_add G; have : 2 ^ 4 ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega); omega
  have e8 : evalE G t (.mul (.k 8) ea) = 8 * a := eE_mul (eE_k hc8) ha (by omega)
  have e4 : evalE G t (.add er (.mul (.k 8) ea)) = V4 := by rw [eE_add hr e8 (by omega), hV4]
  have eq' : evalE G t (two (.v 34)) = 2 ^ l.q := eE_two (by rw [eE_v, hl.q]) (by omega)
  have e3 : evalE G t (.add ec (.mul (two (.v 34)) (.add er (.mul (.k 8) ea)))) = V3 := by
    rw [eE_add hc (eE_mul eq' e4 (by omega)) (by omega), hV3]
  have eℓ : evalE G t (two (.v 32)) = 2 ^ l.ell := eE_two (by rw [eE_v, hl.ell]) (by omega)
  have e2 : evalE G t (.add es (.mul (two (.v 32)) (.add ec (.mul (two (.v 34)) (.add er (.mul (.k 8) ea)))))) =
      V2 := by
    rw [eE_add hs (eE_mul eℓ e3 (by omega)) (by omega), hV2]
  have ek : evalE G t (two (.v 31)) = 2 ^ l.k := eE_two (by rw [eE_v, hl.k]) (by omega)
  exact eE_add hx (eE_mul ek e2 (by omega)) (by omega)

theorem eE_bxor {t : FS} {a b : E} {x y : ℕ} (ha : evalE G t a = x) (hb : evalE G t b = y) (hx : x < 2 ^ G.K)
    (hy : y < 2 ^ G.K) : evalE G t (.bxor a b) = x ^^^ y := by
  simp only [evalE, ha, hb]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx hy)

/-! ## The ten sections of `globalBank` -/

/-- `stageDelta l j` at `j` in `50`. -/
def sdE : E := .bxor (cellE (.k 0) (.v 50) (.k 0) (.k 0) (.k 0)) (cellE (.k 0) (.add (.v 50) (.k 1)) (.k 0) (.k 0) (.k 0))
/-- `dimension k j = min j (2k − 2 − j)`. -/
def dimE : E := .sub (.v 50) (.sub (.v 50) (.sub (.sub (.mul (.k 2) (.v 31)) (.k 2)) (.v 50)))
/-- `eta l r`. -/
def etaE (r : ℕ) : E := cellE (.k 0) (.k 0) (.k 0) (.k r) (.k 0)
/-- `2^(j+1) − 1`. -/
def carryE : E := .sub (two (.add (.v 50) (.k 1))) (.k 1)
/-- The bank's length `5 + 2(2k − 1) + 4k + q + 16·2^q`. -/
def bankLenE : E := .add (.add (.add (.k 5) (.mul (.k 2) (.sub (.mul (.k 2) (.v 31)) (.k 1)))) (.mul (.k 4) (.v 31)))
  (.add (.v 34) (.mul (.k 16) (two (.v 34))))

theorem globalBank_length (l : Routing.Layout) :
    (Routing.globalBank l).length = 5 + 2 * (2 * l.k - 1) + 4 * l.k + l.q + 16 * 2 ^ l.q := by
  simp [Routing.globalBank, Routing.routingBank, Routing.switchCount, Routing.Layout.C]; omega

/-! ## Values of the mask expressions -/

section Values

variable {l : Routing.Layout} {t : FS}

theorem cap_ge_m (hK : l.m + 8 ≤ G.K) {x : ℕ} (hx : x < 2 ^ l.m) : x ≤ G.cap := by
  have := cap_add G; have : 2 ^ l.m ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega); omega

theorem lt_K_of_m (hK : l.m + 8 ≤ G.K) {x : ℕ} (hx : x < 2 ^ l.m) : x < 2 ^ G.K :=
  lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem k_val (hK : l.m + 8 ≤ G.K) {c : ℕ} (hc : c < 2 ^ l.m) : evalE G t (.k c) = c := eE_k (cap_ge_m hK hc)

theorem one_lt_m (l : Routing.Layout) : 1 < 2 ^ l.m :=
  Nat.one_lt_two_pow (show l.m ≠ 0 by unfold Routing.Layout.m; omega)

theorem cell_val (hl : LV l t) (hK : l.m + 8 ≤ G.K) {es ec er : E} {s c r : ℕ} (hs : evalE G t es = s)
    (hc : evalE G t ec = c) (hr : evalE G t er = r) (a : ℕ) (ea : E) (ha : evalE G t ea = a)
    (hin : Routing.InRange l 0 s c r a) :
    evalE G t (cellE (.k 0) es ec er ea) = Routing.cellMask l 0 s c r a ∧ Routing.cellMask l 0 s c r a < 2 ^ l.m := by
  have hlt := Routing.LayoutFacts.cellMask_lt l 0 s c r a hin
  exact ⟨cellE_eval hl (k_val hK (Nat.two_pow_pos _)) hs hc hr ha (cap_ge_m hK hlt) (by omega), hlt⟩

theorem k0 (hK : l.m + 8 ≤ G.K) : evalE G t (.k 0) = 0 := k_val (l := l) hK (Nat.two_pow_pos _)

theorem sd_val (hl : LV l t) (hK : l.m + 8 ≤ G.K) {j : ℕ} (h50 : t.env 50 = j) (hj : j + 1 < 2 ^ l.ell) :
    evalE G t sdE = Routing.stageDelta l j ∧ Routing.stageDelta l j < 2 ^ l.m := by
  have hC : 0 < l.C := Nat.two_pow_pos _
  have hℓm : 2 ^ l.ell ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by unfold Routing.Layout.m; omega)
  obtain ⟨e1, l1⟩ := cell_val hl hK (s := j) (by rw [eE_v, h50]) (k0 hK) (k0 hK) 0 (.k 0) (k0 hK)
    ⟨Nat.two_pow_pos _, by omega, hC, by norm_num, by norm_num⟩
  obtain ⟨e2, l2⟩ := cell_val hl hK (s := j + 1) (eE_add (by rw [eE_v, h50]) (k_val hK (one_lt_m l))
      (cap_ge_m hK (by omega))) (k0 hK) (k0 hK) 0 (.k 0) (k0 hK)
    ⟨Nat.two_pow_pos _, hj, hC, by norm_num, by norm_num⟩
  exact ⟨eE_bxor e1 e2 (lt_K_of_m hK l1) (lt_K_of_m hK l2), Nat.xor_lt_two_pow l1 l2⟩

theorem small_lt_m (l : Routing.Layout) {c : ℕ} (hc : c < 32) : c < 2 ^ l.m :=
  lt_of_lt_of_le hc (by
    have := l.k_pos
    have : 2 ^ 5 ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by unfold Routing.Layout.m; omega)
    simpa using this)

theorem two_k_lt (l : Routing.Layout) : 2 * l.k < 2 ^ l.m :=
  lt_of_le_of_lt l.stages_fit (Nat.pow_lt_pow_right (by norm_num) (by unfold Routing.Layout.m; omega))

theorem dim_val (hl : LV l t) (hK : l.m + 8 ≤ G.K) {j : ℕ} (h50 : t.env 50 = j) (hj : j < 2 * l.k - 1) :
    evalE G t dimE = Routing.dimension l.k j := by
  have hkm := two_k_lt l
  have e2k : evalE G t (.mul (.k 2) (.v 31)) = 2 * l.k :=
    eE_mul (k_val hK (small_lt_m l (by norm_num))) (by rw [eE_v, hl.k]) (cap_ge_m hK hkm)
  unfold dimE Routing.dimension
  rw [eE_sub (by rw [eE_v, h50]) (eE_sub (by rw [eE_v, h50]) (eE_sub (eE_sub e2k (k_val hK (small_lt_m l
    (by norm_num)))) (by rw [eE_v, h50])))]
  omega

theorem two_val (hK : l.m + 8 ≤ G.K) {j : ℕ} (h50 : t.env 50 = j) (hj : j < l.m) :
    evalE G t (two (.v 50)) = 2 ^ j ∧ 2 ^ j < 2 ^ l.m :=
  ⟨eE_two (by rw [eE_v, h50]) (by omega), Nat.pow_lt_pow_right (by norm_num) hj⟩

theorem eta_val (hl : LV l t) (hK : l.m + 8 ≤ G.K) (r : ℕ) (hr : r < 8) :
    evalE G t (etaE r) = Routing.eta l r ∧ Routing.eta l r < 2 ^ l.m :=
  cell_val hl hK (k0 hK) (k0 hK) (k_val hK (small_lt_m l (by omega)))
    0 (.k 0) (k0 hK) ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _, hr, by norm_num⟩

theorem area_val (hl : LV l t) (hK : l.m + 8 ≤ G.K) :
    evalE G t (cellE (.k 0) (.k 0) (.k 0) (.k 0) (.k 1)) = Routing.areaMask l ∧ Routing.areaMask l < 2 ^ l.m :=
  cell_val hl hK (k0 hK) (k0 hK) (k0 hK) 1 (.k 1) (k_val hK (one_lt_m l))
    ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _, by norm_num, by norm_num⟩

theorem carry_val (hK : l.m + 8 ≤ G.K) {j : ℕ} (h50 : t.env 50 = j) (hj : j + 1 < l.m) :
    evalE G t carryE = 2 ^ (j + 1) - 1 := by
  have hp : 2 ^ (j + 1) < 2 ^ l.m := Nat.pow_lt_pow_right (by norm_num) hj
  unfold carryE
  exact eE_sub (eE_two (eE_add (by rw [eE_v, h50]) (k_val hK (one_lt_m l)) (cap_ge_m hK (by
    have := Nat.lt_two_pow_self (n := j + 1); omega))) (by omega)) (k_val hK (one_lt_m l))

end Values

/-! ## The layout in the program variables -/

theorem lv_of {l : Routing.Layout} {s t : FS} (hl : LV l s) (h : ∀ i : Var, i ∉ LW → t.env i = s.env i) : LV l t :=
  ⟨(h 31 (by decide)).trans hl.k, (h 32 (by decide)).trans hl.ell, (h 34 (by decide)).trans hl.q⟩

theorem nbl_m {l : Routing.Layout} {x : ℕ} (hx : x < 2 ^ l.m) (hK : l.m + 8 ≤ G.K) : natBitLength x + 2 ≤ G.K := by
  have := natBitLength_le_of_lt (show 1 ≤ l.m by have := l.k_pos; unfold Routing.Layout.m; omega) hx; omega


section Generic

/-- A per-entry printer: `P g` prints `wd b` when `g` evaluates to `b` on every state agreeing off the scratch. -/
def PrinterSpec (G : Glob) (P : E → S) (wd : ℕ → List Bool) : Prop :=
  ∀ (s : FS) (g : E) (b : ℕ), (∀ t, AgS s t → evalE G t g = b) → natBitLength b + 2 ≤ G.K → 8 ≤ G.K →
    G.K ≤ G.N → Em SW s (evalS G (P g) s) (wd b)

variable (P : E → S) (wd : ℕ → List Bool)

theorem secSpecG (hP : PrinterSpec G P wd) (s : FS) (lenE : E) (n : ℕ) (hn : min (evalE G s lenE) G.N = n) (g : E) (fv : ℕ → ℕ)
    (hg : ∀ j < n, ∀ t : FS, (∀ i : Var, i ∉ LW → t.env i = s.env i) → t.env 50 = j → t.fl = s.fl → t.fp = s.fp →
      evalE G t g = fv j)
    (hb : ∀ j < n, natBitLength (fv j) + 2 ≤ G.K) (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) :
    Em LW s (evalS G (.loop 50 lenE (P g)) s) ((List.range n).flatMap (fun j => wd (fv j))) := by
  refine (Em_loop 50 lenE (P g) LW (mem_LW.mpr (Or.inr (by decide))) s n hn (fun _ => True) trivial
    (fun j => wd (fv j)) (fun j hj t _ te => ⟨trivial, ?_⟩)).2
  have h := hP (t.setv 50 j) g (fv j) (fun u hu => hg j hj u (fun i hi => by
      rw [hu.1 i (fun hm => hi (SW_sub_LW i hm))]; simp only [FS.setv_env, Function.update_apply]
      rw [if_neg (show i ≠ 50 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]
      exact te.env i hi)
    (by rw [hu.1 50 (not_mem_SW (by decide))]; simp) (by rw [hu.2.1]; exact te.fl) (by rw [hu.2.2]; exact te.fp))
    (hb j hj) hK hN
  exact h.mono SW_sub_LW

theorem oneSpecG (hP : PrinterSpec G P wd) (s : FS) (g : E) (b : ℕ)
    (hg : ∀ t : FS, (∀ i : Var, i ∉ SW → t.env i = s.env i) → t.fl = s.fl → t.fp = s.fp → evalE G t g = b)
    (hb : natBitLength b + 2 ≤ G.K) (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) :
    Em LW s (evalS G (P g) s) (wd b) :=
  (hP s g b (fun u hu => hg u hu.1 hu.2.1 hu.2.2) hb hK hN).mono SW_sub_LW

/-! ## The generic bank printer -/

/-- **The bank printer**, generic in the per-entry printer `P`. -/
def bankGP : S :=
  .seq (emitNatE bankLenE) (.seq (P (.k 0))
  (.seq (.loop 50 (.sub (.mul (.k 2) (.v 31)) (.k 1)) (P sdE))
  (.seq (.loop 50 (.sub (.mul (.k 2) (.v 31)) (.k 1)) (P (.bxor sdE (two dimE))))
  (.seq (.loop 50 (.v 31) (P (two (.v 50))))
  (.seq (P (etaE 1)) (.seq (P (etaE 2)) (.seq (P (.bxor (etaE 3) (etaE 1))) (.seq (P (.bxor (etaE 4) (etaE 1)))
  (.seq (.loop 50 (.v 31) (P (.bxor (.bxor (etaE 4) (etaE 1)) (two (.v 50)))))
  (.seq (.loop 50 (.v 34) (P (cellE (.k 0) (.k 0) carryE (.k 0) (.k 0))))
  (.seq (.loop 50 (.mul (.k 16) (two (.v 34))) (P (.mul (two (.add (.v 31) (.v 32))) (.v 50))))
  (.seq (.loop 50 (.v 31) (P (.bxor (.bxor carryE (etaE 5)) (etaE 1))))
  (.loop 50 (.v 31) (P (.bxor (.bxor carryE (cellE (.k 0) (.k 0) (.k 0) (.k 0) (.k 1))) (etaE 6))))))))))))))))

theorem bankGP_spec (hP : PrinterSpec G P wd) (l : Routing.Layout) (s : FS) (hl : LV l s) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N)
    (hN : 16 * 2 ^ l.q + 2 * l.k ≤ G.N) :
    Em LW s (evalS G (bankGP P) s) (natWord (Routing.globalBank l).length ++ (Routing.globalBank l).flatMap wd) := by
  have hK8 : 8 ≤ G.K := by omega
  have hkm := two_k_lt l
  have hm5 : 5 ≤ l.m := by have := l.k_pos; unfold Routing.Layout.m; omega
  have hkℓ : l.k + l.ell + l.q + 4 = l.m := rfl
  have hfit := l.stages_fit
  -- the length
  have hpm : 2 ^ l.m = 16 * (2 ^ l.k * (2 ^ l.ell * 2 ^ l.q)) := by
    rw [← hkℓ, pow_add, pow_add, pow_add]; ring
  have hA := Nat.lt_two_pow_self (n := l.k)
  have hCq := Nat.lt_two_pow_self (n := l.q)
  have hB : 2 ≤ 2 ^ l.ell := by have := l.k_pos; omega
  have hlen : (Routing.globalBank l).length < 2 ^ l.m := by
    rw [globalBank_length, hpm]
    generalize 2 ^ l.k = A at hA
    generalize 2 ^ l.ell = B at hB
    generalize 2 ^ l.q = C at hCq
    have hAC : A ≤ A * C := Nat.le_mul_of_pos_right _ (by omega)
    have hCA : C ≤ A * C := Nat.le_mul_of_pos_left _ (by omega)
    have hABC : 2 * (A * C) ≤ A * (B * C) := by nlinarith
    omega
  have elen : evalE G s bankLenE = (Routing.globalBank l).length := by
    have hlen' := hlen
    rw [globalBank_length] at hlen'
    rw [globalBank_length]
    have hq : 16 * 2 ^ l.q < 2 ^ l.m := by
      rw [hpm]
      generalize 2 ^ l.k = A at hA
      generalize 2 ^ l.ell = B at hB
      generalize 2 ^ l.q = C at hCq
      have h1 : 2 * C ≤ B * C := Nat.mul_le_mul_right C hB
      have h2 : B * C ≤ A * (B * C) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hk2 : 2 * l.k - 1 < 2 ^ l.m := by omega
    unfold bankLenE
    have e1 : evalE G s (.mul (.k 2) (.v 31)) = 2 * l.k :=
      eE_mul (k_val hK (small_lt_m l (by norm_num))) (by rw [eE_v, hl.k]) (cap_ge_m hK hkm)
    have e2 : evalE G s (.mul (.k 2) (.sub (.mul (.k 2) (.v 31)) (.k 1))) = 2 * (2 * l.k - 1) :=
      eE_mul (k_val hK (small_lt_m l (by norm_num))) (eE_sub e1 (k_val hK (small_lt_m l (by norm_num))))
        (cap_ge_m hK (by omega))
    have e3 : evalE G s (.mul (.k 4) (.v 31)) = 4 * l.k :=
      eE_mul (k_val hK (small_lt_m l (by norm_num))) (by rw [eE_v, hl.k]) (cap_ge_m hK (by omega))
    have e4 : evalE G s (.mul (.k 16) (two (.v 34))) = 16 * 2 ^ l.q :=
      eE_mul (k_val hK (small_lt_m l (by norm_num))) (eE_two (by rw [eE_v, hl.q]) (by omega)) (cap_ge_m hK hq)
    rw [eE_add (eE_add (eE_add (k_val hK (small_lt_m l (by norm_num))) e2 (cap_ge_m hK (by omega))) e3
      (cap_ge_m hK (by omega))) (eE_add (by rw [eE_v, hl.q]) e4 (cap_ge_m hK (by omega))) (cap_ge_m hK (by omega))]
    ring
  have agLW : ∀ {u v : FS}, (∀ i : Var, i ∉ LW → u.env i = s.env i) → (∀ i : Var, i ∉ LW → v.env i = u.env i) →
      ∀ i : Var, i ∉ LW → v.env i = s.env i := fun hu hv i hi => (hv i hi).trans (hu i hi)
  have N1 : 2 * l.k - 1 ≤ G.N := by omega
  have N2 : l.k ≤ G.N := by omega
  have N3 : l.q ≤ G.N := by have : l.q < 2 ^ l.q := Nat.lt_two_pow_self; omega
  have N4 : 16 * 2 ^ l.q ≤ G.N := by omega
  have hsw : Routing.switchCount l.k = 2 * l.k - 1 := rfl
  have hC : l.C = 2 ^ l.q := rfl
  suffices H : Em LW s (evalS G (bankGP P) s) (natWord (evalE G s bankLenE) ++ (wd 0 ++
      ((List.range (2 * l.k - 1)).flatMap (fun j => wd (Routing.stageDelta l j)) ++
      ((List.range (2 * l.k - 1)).flatMap (fun j => wd (Routing.stageDelta l j ^^^ 2 ^ Routing.dimension l.k j)) ++
      ((List.range l.k).flatMap (fun j => wd (2 ^ j)) ++
      (wd (Routing.eta l 1) ++ (wd (Routing.eta l 2) ++ (wd (Routing.eta l 3 ^^^ Routing.eta l 1) ++
      (wd (Routing.eta l 4 ^^^ Routing.eta l 1) ++
      ((List.range l.k).flatMap (fun j => wd (Routing.eta l 4 ^^^ Routing.eta l 1 ^^^ 2 ^ j)) ++
      ((List.range l.q).flatMap (fun j => wd (Routing.columnCarry l j)) ++
      ((List.range (16 * 2 ^ l.q)).flatMap (fun j => wd (2 ^ (l.k + l.ell) * j)) ++
      ((List.range l.k).flatMap (fun j => wd (Routing.laneCarry j ^^^ Routing.eta l 5 ^^^ Routing.eta l 1)) ++
      (List.range l.k).flatMap (fun j => wd (Routing.laneCarry j ^^^ Routing.areaMask l ^^^ Routing.eta l 6))))))))))))))) by
    convert H using 2
    · rw [elen]
    · simp [Routing.globalBank, Routing.routingBank, List.flatMap_append, hsw, hC, Function.comp_def, List.flatMap_map]
  have hm1 : 1 < 2 ^ l.m := one_lt_m l
  -- states agreeing with `s` outside `LW` carry the layout; at pass `j` of a loop
  have LVa : ∀ {u : FS}, (∀ i : Var, i ∉ LW → u.env i = s.env i) → LV l u := fun hu => lv_of hl hu
  have LVj : ∀ {u : FS}, (∀ i : Var, i ∉ LW → u.env i = s.env i) → ∀ j, LV l (u.setv 50 j) := fun hu j =>
    lv_of hl (fun i hi => by
      simp only [FS.setv_env, Function.update_apply]
      rw [if_neg (show i ≠ 50 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]; exact hu i hi)
  have e2k1 : ∀ {u : FS}, LV l u → evalE G u (.sub (.mul (.k 2) (.v 31)) (.k 1)) = 2 * l.k - 1 := fun hu =>
    eE_sub (eE_mul (k_val hK (small_lt_m l (by norm_num))) (by rw [eE_v, hu.k]) (cap_ge_m hK hkm))
      (k_val hK (small_lt_m l (by norm_num)))
  have hj1 : ∀ j, j < 2 * l.k - 1 → j + 1 < 2 ^ l.ell := fun j hj => by omega
  have hkm' : l.k < l.m := by unfold Routing.Layout.m; omega
  have hqm : l.q + 1 < l.m := by unfold Routing.Layout.m; have := l.k_pos; omega
  have hkℓm : 2 ^ (l.k + l.ell) * (16 * 2 ^ l.q) = 2 ^ l.m := by rw [← hkℓ, pow_add, pow_add, pow_add]; ring
  -- P0: natWord |bank|
  refine Em_acc ((emitNatE_spec (G := G) s bankLenE (by rw [elen]; exact nbl_m hlen hK) hKN).mono SW_sub_LW)
    (fun t1 a1 => ?_)
  have u1 : ∀ i : Var, i ∉ LW → t1.env i = s.env i := a1.env
  -- P1: the identity offset `0`
  refine Em_acc (oneSpecG P wd hP t1 (.k 0) 0 (fun u _ _ _ => k0 (l := l) hK) (nbl_m (Nat.two_pow_pos _) hK) hK8 hKN)
    (fun t2 a2 => ?_)
  have u2 := agLW u1 a2.env
  -- P2: straight stage edges
  refine Em_acc (secSpecG P wd hP t2 _ (2 * l.k - 1) (by rw [e2k1 (LVa u2)]; exact min_eq_left N1) sdE (Routing.stageDelta l)
    (fun j hj u hu h50 _ _ => (sd_val (LVa (agLW u2 hu)) hK h50 (hj1 j hj)).1)
    (fun j hj => nbl_m (sd_val (LVj u2 j) hK (by simp) (hj1 j hj)).2 hK) hK8 hKN) (fun t3 a3 => ?_)
  have u3 := agLW u2 a3.env
  -- Crossed stage edges
  refine Em_acc (secSpecG P wd hP t3 _ (2 * l.k - 1) (by rw [e2k1 (LVa u3)]; exact min_eq_left N1) (.bxor sdE (two dimE))
    (fun j => Routing.stageDelta l j ^^^ 2 ^ Routing.dimension l.k j)
    (fun j hj u hu h50 _ _ => by
      have lu := LVa (agLW u3 hu)
      obtain ⟨e1, l1⟩ := sd_val lu hK h50 (hj1 j hj)
      have hd : Routing.dimension l.k j < l.k := by unfold Routing.dimension; omega
      exact eE_bxor e1 (eE_two (dim_val lu hK h50 hj) (by omega)) (lt_K_of_m hK l1)
        (lt_K_of_m hK (Nat.pow_lt_pow_right (by norm_num) (by omega))))
    (fun j hj => nbl_m (Nat.xor_lt_two_pow (sd_val (LVj u3 j) hK (by simp) (hj1 j hj)).2
      (Nat.pow_lt_pow_right (by norm_num) (by unfold Routing.dimension; omega))) hK) hK8 hKN) (fun t4 a4 => ?_)
  have u4 := agLW u3 a4.env
  -- pure bounds
  have eta_lt : ∀ r, r < 8 → Routing.eta l r < 2 ^ l.m := fun r hr => (eta_val hl hK r hr).2
  have area_lt : Routing.areaMask l < 2 ^ l.m := (area_val hl hK).2
  have pow_lt : ∀ j, j < l.k → 2 ^ j < 2 ^ l.m := fun j hj => Nat.pow_lt_pow_right (by norm_num) (by omega)
  have lane_lt : ∀ j, j < l.k → Routing.laneCarry j < 2 ^ l.m := fun j hj => by
    unfold Routing.laneCarry
    have : 2 ^ (j + 1) ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.one_le_two_pow (n := j + 1); omega
  have x2 : ∀ {a b : ℕ}, a < 2 ^ l.m → b < 2 ^ l.m → a ^^^ b < 2 ^ l.m := fun ha hb => Nat.xor_lt_two_pow ha hb
  have eK : ∀ {u : FS}, LV l u → evalE G u (.v 31) = l.k := fun hu => by rw [eE_v, hu.k]
  -- Same-stage lane partners `2^d`
  refine Em_acc (secSpecG P wd hP t4 (.v 31) l.k (by rw [eK (LVa u4)]; exact min_eq_left N2) (two (.v 50)) (fun j => 2 ^ j)
    (fun j hj u hu h50 _ _ => (two_val hK h50 (by omega)).1) (fun j hj => nbl_m (pow_lt j hj) hK) hK8 hKN)
    (fun t5 a5 => ?_)
  have u5 := agLW u4 a5.env
  -- P5–P8: the four role translations
  refine Em_acc (oneSpecG P wd hP t5 (etaE 1) (Routing.eta l 1) (fun u hu _ _ => (eta_val (LVa (agLW u5 (fun i hi =>
    hu i (fun h => hi (SW_sub_LW i h))))) hK 1 (by norm_num)).1) (nbl_m (eta_lt 1 (by norm_num)) hK) hK8 hKN)
    (fun t6 a6 => ?_)
  have u6 := agLW u5 a6.env
  refine Em_acc (oneSpecG P wd hP t6 (etaE 2) (Routing.eta l 2) (fun u hu _ _ => (eta_val (LVa (agLW u6 (fun i hi =>
    hu i (fun h => hi (SW_sub_LW i h))))) hK 2 (by norm_num)).1) (nbl_m (eta_lt 2 (by norm_num)) hK) hK8 hKN)
    (fun t7 a7 => ?_)
  have u7 := agLW u6 a7.env
  refine Em_acc (oneSpecG P wd hP t7 (.bxor (etaE 3) (etaE 1)) (Routing.eta l 3 ^^^ Routing.eta l 1) (fun u hu _ _ => by
      have lu := LVa (agLW u7 (fun i hi => hu i (fun h => hi (SW_sub_LW i h))))
      exact eE_bxor (eta_val lu hK 3 (by norm_num)).1 (eta_val lu hK 1 (by norm_num)).1
        (lt_K_of_m hK (eta_lt 3 (by norm_num))) (lt_K_of_m hK (eta_lt 1 (by norm_num))))
    (nbl_m (x2 (eta_lt 3 (by norm_num)) (eta_lt 1 (by norm_num))) hK) hK8 hKN) (fun t8 a8 => ?_)
  have u8 := agLW u7 a8.env
  refine Em_acc (oneSpecG P wd hP t8 (.bxor (etaE 4) (etaE 1)) (Routing.eta l 4 ^^^ Routing.eta l 1) (fun u hu _ _ => by
      have lu := LVa (agLW u8 (fun i hi => hu i (fun h => hi (SW_sub_LW i h))))
      exact eE_bxor (eta_val lu hK 4 (by norm_num)).1 (eta_val lu hK 1 (by norm_num)).1
        (lt_K_of_m hK (eta_lt 4 (by norm_num))) (lt_K_of_m hK (eta_lt 1 (by norm_num))))
    (nbl_m (x2 (eta_lt 4 (by norm_num)) (eta_lt 1 (by norm_num))) hK) hK8 hKN) (fun t9 a9 => ?_)
  have u9 := agLW u8 a9.env
  -- P9: pair-coherence partners
  refine Em_acc (secSpecG P wd hP t9 (.v 31) l.k (by rw [eK (LVa u9)]; exact min_eq_left N2)
    (.bxor (.bxor (etaE 4) (etaE 1)) (two (.v 50))) (fun j => Routing.eta l 4 ^^^ Routing.eta l 1 ^^^ 2 ^ j)
    (fun j hj u hu h50 _ _ => by
      have lu := LVa (agLW u9 hu)
      exact eE_bxor (eE_bxor (eta_val lu hK 4 (by norm_num)).1 (eta_val lu hK 1 (by norm_num)).1
        (lt_K_of_m hK (eta_lt 4 (by norm_num))) (lt_K_of_m hK (eta_lt 1 (by norm_num)))) (two_val hK h50 (by omega)).1
        (lt_K_of_m hK (x2 (eta_lt 4 (by norm_num)) (eta_lt 1 (by norm_num)))) (lt_K_of_m hK (pow_lt j hj)))
    (fun j hj => nbl_m (x2 (x2 (eta_lt 4 (by norm_num)) (eta_lt 1 (by norm_num))) (pow_lt j hj)) hK) hK8 hKN)
    (fun t10 a10 => ?_)
  have u10 := agLW u9 a10.env
  -- P10: column successors
  have col : ∀ j, j < l.q → ∀ {u : FS}, LV l u → u.env 50 = j →
      evalE G u (cellE (.k 0) (.k 0) carryE (.k 0) (.k 0)) = Routing.columnCarry l j ∧
        Routing.columnCarry l j < 2 ^ l.m := fun j hj u lu h50 => by
    have hc : 2 ^ (j + 1) - 1 < l.C := by
      show 2 ^ (j + 1) - 1 < 2 ^ l.q
      have : 2 ^ (j + 1) ≤ 2 ^ l.q := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.one_le_two_pow (n := j + 1); omega
    exact cell_val lu hK (k0 hK) (carry_val hK h50 (by omega)) (k0 hK) 0 (.k 0) (k0 hK)
      ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, hc, by norm_num, by norm_num⟩
  refine Em_acc (secSpecG P wd hP t10 (.v 34) l.q (by rw [eE_v, (LVa u10).q]; exact min_eq_left N3)
    (cellE (.k 0) (.k 0) carryE (.k 0) (.k 0)) (Routing.columnCarry l)
    (fun j hj u hu h50 _ _ => (col j hj (LVa (agLW u10 hu)) h50).1)
    (fun j hj => nbl_m (col j hj (LVj u10 j) (by simp)).2 hK) hK8 hKN) (fun t11 a11 => ?_)
  have u11 := agLW u10 a11.env
  -- P11: the `16C` local offsets
  have e16 : ∀ {u : FS}, LV l u → evalE G u (.mul (.k 16) (two (.v 34))) = 16 * 2 ^ l.q := fun lu =>
    eE_mul (k_val hK (small_lt_m l (by norm_num))) (eE_two (by rw [eE_v, lu.q]) (by omega)) (cap_ge_m hK (by
      rw [hpm]
      have h1 : 2 * 2 ^ l.q ≤ 2 ^ l.ell * 2 ^ l.q := Nat.mul_le_mul_right _ hB
      have h2 : 2 ^ l.ell * 2 ^ l.q ≤ 2 ^ l.k * (2 ^ l.ell * 2 ^ l.q) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      omega))
  have loc_lt : ∀ j, j < 16 * 2 ^ l.q → 2 ^ (l.k + l.ell) * j < 2 ^ l.m := fun j hj => by
    rw [← hkℓm]; exact Nat.mul_lt_mul_of_pos_left hj (Nat.two_pow_pos _)
  refine Em_acc (secSpecG P wd hP t11 (.mul (.k 16) (two (.v 34))) (16 * 2 ^ l.q) (by rw [e16 (LVa u11)]; exact min_eq_left N4)
    (.mul (two (.add (.v 31) (.v 32))) (.v 50)) (fun j => 2 ^ (l.k + l.ell) * j)
    (fun j hj u hu h50 _ _ => by
      have lu := LVa (agLW u11 hu)
      exact eE_mul (eE_two (eE_add (by rw [eE_v, lu.k]) (by rw [eE_v, lu.ell]) (cap_ge_m hK (by
        have := Nat.lt_two_pow_self (n := l.k + l.ell)
        have : 2 ^ (l.k + l.ell) ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega))) (by omega)) (by rw [eE_v, h50]) (cap_ge_m hK (loc_lt j hj)))
    (fun j hj => nbl_m (loc_lt j hj) hK) hK8 hKN) (fun t12 a12 => ?_)
  have u12 := agLW u11 a12.env
  -- P12, P13: the two predecessor families
  refine Em_acc (secSpecG P wd hP t12 (.v 31) l.k (by rw [eK (LVa u12)]; exact min_eq_left N2)
    (.bxor (.bxor carryE (etaE 5)) (etaE 1)) (fun j => Routing.laneCarry j ^^^ Routing.eta l 5 ^^^ Routing.eta l 1)
    (fun j hj u hu h50 _ _ => by
      have lu := LVa (agLW u12 hu)
      exact eE_bxor (eE_bxor (carry_val hK h50 (by omega)) (eta_val lu hK 5 (by norm_num)).1
        (lt_K_of_m hK (lane_lt j hj)) (lt_K_of_m hK (eta_lt 5 (by norm_num)))) (eta_val lu hK 1 (by norm_num)).1
        (lt_K_of_m hK (x2 (lane_lt j hj) (eta_lt 5 (by norm_num)))) (lt_K_of_m hK (eta_lt 1 (by norm_num))))
    (fun j hj => nbl_m (x2 (x2 (lane_lt j hj) (eta_lt 5 (by norm_num))) (eta_lt 1 (by norm_num))) hK) hK8 hKN)
    (fun t13 a13 => ?_)
  have u13 := agLW u12 a13.env
  exact secSpecG P wd hP t13 (.v 31) l.k (by rw [eK (LVa u13)]; exact min_eq_left N2)
    (.bxor (.bxor carryE (cellE (.k 0) (.k 0) (.k 0) (.k 0) (.k 1))) (etaE 6))
    (fun j => Routing.laneCarry j ^^^ Routing.areaMask l ^^^ Routing.eta l 6)
    (fun j hj u hu h50 _ _ => by
      have lu := LVa (agLW u13 hu)
      exact eE_bxor (eE_bxor (carry_val hK h50 (by omega)) (area_val lu hK).1
        (lt_K_of_m hK (lane_lt j hj)) (lt_K_of_m hK area_lt)) (eta_val lu hK 6 (by norm_num)).1
        (lt_K_of_m hK (x2 (lane_lt j hj) area_lt)) (lt_K_of_m hK (eta_lt 6 (by norm_num))))
    (fun j hj => nbl_m (x2 (x2 (lane_lt j hj) area_lt) (eta_lt 6 (by norm_num))) hK) hK8 hKN

end Generic

/-! ## The neighbor bank (pairs `(1, b)`) -/

theorem pairPrinter : PrinterSpec G pairP nbrWord := fun s g b hg hb hK hN => pairP_spec s g b hg hb hK hN

/-- **The neighbor bank printer.** -/
def bankPairP : S := bankGP pairP

theorem bankWord_eq (l : Routing.Layout) :
    listWord ACSP.Affine.Instance.pairWord ((Routing.globalBank l).map (fun b => (1, b))) =
      natWord (Routing.globalBank l).length ++ (Routing.globalBank l).flatMap nbrWord := by
  simp [listWord, List.flatMap, List.map_map, Function.comp_def]

theorem bankPairP_spec (l : Routing.Layout) (s : FS) (hl : LV l s) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N)
    (hN : 16 * 2 ^ l.q + 2 * l.k ≤ G.N) :
    Em LW s (evalS G bankPairP s)
      (listWord ACSP.Affine.Instance.pairWord ((Routing.globalBank l).map (fun b => (1, b)))) := by
  rw [bankWord_eq]
  exact bankGP_spec pairP nbrWord pairPrinter l s hl hK hKN hN

end NearCubicGates.Adapters.RAMACSP.Gen
