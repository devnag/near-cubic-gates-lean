import Proof.Gates.Succinct.Field

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

variable {ns nr : ℕ}

/-- The guarded field reader (paper lem:succinct-verifier, stage (2)). Registers: `R .flag` flag, `R .cnt` count, `R .val` value,
`R .pw` power, `R .tmp` temp, `R .gc`/`R .hc` guard copies, `R .zg` guard flag, `R .cd` position counter; `b` the bound. -/
def fieldW (i : Fin (ns + 1)) (R : FReg → Fin nr) (b : Fin nr) : WM ns nr :=
  .seq (.seq (.inc (R .flag)) (.whr (R .flag) (unaryBody false i (R .flag) (R .cnt))))
  (.seq (addTo (R .cnt) (R .cd) (R .tmp)) (.seq (addTo (R .cnt) (R .cd) (R .tmp)) (.seq (.inc (R .cd))
  (.seq (addTo (R .cnt) (R .gc) (R .tmp)) (.seq (addTo b (R .hc) (R .tmp))
  (.seq (.whr (R .gc) (.seq (.dec (R .gc)) (.ifr (R .hc) (.dec (R .hc)) (WM.setF (R .zg)))))
  (.seq (WM.clear (R .hc))
  (.ifr (R .zg) (skipPairs false i (R .cnt))
    (.seq (.inc (R .pw)) (.seq (.whr (R .cnt) (.seq (.dec (R .cnt)) (bitBody false i (R .val) (R .pw) (R .tmp))))
      (WM.clear (R .pw))))))))))))

/-- The cost class of one field read (paper lem:succinct-verifier, stage (2)). -/
def fieldCost (L lb : ℕ) : ℕ := 400 * (L + lb + 2) * (2 ^ lb + 1)

theorem stp_false : stp false = 1 := rfl
theorem off_false : off false = 0 := rfl

theorem freg_cases (R : FReg → Fin nr) (j : Fin nr) : (∃ a, j = R a) ∨ ∀ a, j ≠ R a := by
  by_cases h : ∃ a, j = R a
  · exact Or.inl h
  · exact Or.inr fun a ha => h ⟨a, ha⟩

/-- The unary prefix: `c := L`, the head moves past the field's `0`. -/
theorem unary_step (cap : ℕ) (i : Fin (ns + 1)) (f c : Fin nr) (hfc : f ≠ c) (σ : WState ns nr)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hcap : ones (σ.st i) (σ.sh i) + 1 ≤ cap) :
    WExec cap (.seq (.inc f) (.whr f (unaryBody false i f c))) σ
      ((σ.seth i (σ.sh i + ones (σ.st i) (σ.sh i) + 1)).setv c (ones (σ.st i) (σ.sh i)))
      (10 * ones (σ.st i) (σ.sh i) + 13) := by
  have e1 := WExec.inc (cap := cap) f σ (by omega)
  have e2 := unary_loop cap false i f c hfc (by omega) (ones (σ.st i) (σ.sh i)) (σ.setv f (σ.val f + 1))
    (by simp [hf])
    (fun k hk => by
      simp only [WState.setv_st, WState.setv_sh, stp_false, off_false, Nat.add_zero, one_mul]
      exact ones_true _ _ k hk)
    (by
      simp only [WState.setv_st, WState.setv_sh, stp_false, off_false, Nat.add_zero, one_mul]
      exact ones_false _ _)
    (by simp [Function.update_apply, Ne.symm hfc, hc]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · simp [stp_false]
  · rfl
  · funext j
    simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases hjf : j = f
    · subst hjf; simp [hfc, hf]
    · by_cases hjc : j = c
      · subst hjc; simp [hjf, hc]
      · simp [hjf, hjc]
  · rfl

/-- The guard loop: `z := [lb < L]`, `g := 0`, `h := lb − L`. -/
theorem guard_step (cap : ℕ) (g h z : Fin nr) (hgh : g ≠ h) (hgz : g ≠ z) (hhz : h ≠ z) (σ : WState ns nr)
    (L lb : ℕ) (hg : σ.val g = L) (hh : σ.val h = lb) (hz : σ.val z = 0) (hcap : L + lb + 1 ≤ cap) :
    WExec cap (.whr g (.seq (.dec g) (.ifr h (.dec h) (WM.setF z)))) σ
      (((σ.setv g 0).setv h (lb - L)).setv z (if lb < L then 1 else 0)) (L * 9 + 1) := by
  let S : ℕ → WState ns nr := fun k => ((σ.setv g (L - k)).setv h (lb - k)).setv z (if lb < k then 1 else 0)
  have hS0 : S 0 = σ := by
    refine WState.eq rfl rfl ?_ rfl
    funext j
    simp only [S, WState.setv_val, Function.update_apply]
    by_cases hjz : j = z
    · subst hjz; simp [hz]
    · by_cases hjh : j = h
      · subst hjh; simp [hjz, hh]
      · by_cases hjg : j = g
        · subst hjg; simp [hjz, hjh, hg]
        · simp [hjz, hjh, hjg]
  have hSL : S L = ((σ.setv g 0).setv h (lb - L)).setv z (if lb < L then 1 else 0) := by
    simp only [S, Nat.sub_self]
  have e := UnionMachine.Round.wloop cap g (.ifr h (.dec h) (WM.setF z)) 5 L S
    (fun k _ => by simp [S, Function.update_apply, hgh, hgz]) (by omega)
    (fun k hk => by
      have hv6 : ((S k).setv g (L - k - 1)).val h = lb - k := by
        simp [S, Function.update_apply, hhz, Ne.symm hgh]
      have hv7 : ((S k).setv g (L - k - 1)).val z = if lb < k then 1 else 0 := by
        simp [S, Function.update_apply, Ne.symm hgz]
      by_cases hk' : k < lb
      · have hd := WExec.dec (cap := cap) h ((S k).setv g (L - k - 1)) (by rw [hv6]; omega)
        refine WExec.cast cap (WExec.ifrT (by rw [hv6]; omega) hd) ?_ (by omega)
        refine WState.eq rfl rfl ?_ rfl
        funext j
        simp only [S, WState.setv_val, Function.update_apply]
        by_cases hjz : j = z
        · subst hjz; simp [Ne.symm hhz, Ne.symm hgz, show ¬ lb < k by omega, show ¬ lb < k + 1 by omega]
        · by_cases hjh : j = h
          · subst hjh; simp [hjz, Ne.symm hgh]; omega
          · by_cases hjg : j = g
            · subst hjg; simp [hjz, hjh]; omega
            · simp [hjz, hjh, hjg]
      · have hf := wsetF_spec cap z ((S k).setv g (L - k - 1)) (by rw [hv7]; split_ifs <;> omega) (by omega)
        refine WExec.cast cap (WExec.ifrF (by rw [hv6]; omega) hf) ?_ (by omega)
        refine WState.eq rfl rfl ?_ rfl
        funext j
        simp only [S, WState.setv_val, Function.update_apply]
        by_cases hjz : j = z
        · subst hjz; simp [show lb < k + 1 by omega]
        · by_cases hjh : j = h
          · subst hjh; simp [hjz, Ne.symm hgh]; omega
          · by_cases hjg : j = g
            · subst hjg; simp [hjz, hjh]; omega
            · simp [hjz, hjh, hjg])
  rw [hS0, hSL] at e
  exact WExec.mono e (by ring_nf; omega)

/-- A state that differs from `σ` only in the head of stream `i` and in its registers. -/
def regState (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (V : Fin nr → ℕ) : WState ns nr :=
  ⟨Function.update σ.sh i h, σ.st, V, σ.cell⟩

@[simp] theorem regState_val (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (V : Fin nr → ℕ) :
    (regState σ i h V).val = V := rfl
@[simp] theorem regState_st (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (V : Fin nr → ℕ) :
    (regState σ i h V).st = σ.st := rfl
@[simp] theorem regState_cell (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (V : Fin nr → ℕ) :
    (regState σ i h V).cell = σ.cell := rfl
@[simp] theorem regState_sh_self (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (V : Fin nr → ℕ) :
    (regState σ i h V).sh i = h := by simp [regState]
theorem regState_setv (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (V : Fin nr → ℕ) (r : Fin nr) (x : ℕ) :
    (regState σ i h V).setv r x = regState σ i h (Function.update V r x) := rfl
theorem regState_seth (σ : WState ns nr) (i : Fin (ns + 1)) (h h' : ℕ) (V : Fin nr → ℕ) :
    (regState σ i h V).seth i h' = regState σ i h' V := by
  simp [regState, WState.seth]
theorem regState_self (σ : WState ns nr) (i : Fin (ns + 1)) : regState σ i (σ.sh i) σ.val = σ := by
  simp [regState]
theorem seth_setv_regState (σ : WState ns nr) (i : Fin (ns + 1)) (h : ℕ) (r s : Fin nr) (x y : ℕ) :
    ((σ.seth i h).setv r x).setv s y = regState σ i h (Function.update (Function.update σ.val r x) s y) := rfl

/-- **The guarded field reader** (paper lem:succinct-verifier, stage (2) and item (ii)), on every stream content. -/
theorem fieldW_spec (cap : ℕ) (i : Fin (ns + 1)) (R : FReg → Fin nr) (hR : Function.Injective R) (b : Fin nr)
    (hb : ∀ j, R j ≠ b) (σ : WState ns nr)
    (h0 : σ.val (R .flag) = 0) (h1 : σ.val (R .cnt) = 0) (h3 : σ.val (R .pw) = 0) (h4 : σ.val (R .tmp) = 0)
    (h5 : σ.val (R .gc) = 0) (h6 : σ.val (R .hc) = 0) (h7 : σ.val (R .zg) = 0)
    (hcap : σ.val (R .cd) + σ.val (R .val) + 2 * ones (σ.st i) (σ.sh i) + 2 * σ.val b + 2 ^ (σ.val b + 1) + 4 ≤ cap) :
    WExec cap (fieldW i R b) σ
      ((((σ.seth i (fieldEnd (σ.st i) (σ.sh i))).setv (R .val) (σ.val (R .val) + fieldVal (σ.st i) (σ.sh i) (σ.val b))).setv
        (R .cd) (σ.val (R .cd) + 2 * ones (σ.st i) (σ.sh i) + 1)).setv (R .zg)
        (if σ.val b < ones (σ.st i) (σ.sh i) then 1 else 0))
      (fieldCost (ones (σ.st i) (σ.sh i)) (σ.val b)) := by
  have hb' : ∀ j, b ≠ R j := fun j h => hb j h.symm
  have hne : ∀ a c : FReg, a ≠ c → R a ≠ R c := fun a c h => hR.ne h
  rw [seth_setv_regState, regState_setv]
  generalize hd : σ.st i = d at hcap ⊢
  generalize hpos : σ.sh i = pos at hcap ⊢
  generalize hL : ones d pos = L at hcap ⊢
  generalize hlb : σ.val b = lb at hcap ⊢
  generalize hv₀ : σ.val (R .val) = v₀ at hcap ⊢
  generalize hcd : σ.val (R .cd) = cd at hcap ⊢
  have hpow1 : 1 ≤ 2 ^ lb := Nat.one_le_two_pow
  have hpowS : 2 ^ (lb + 1) = 2 * 2 ^ lb := by rw [pow_succ]; ring
  -- 1. the unary prefix
  set V1 := Function.update σ.val (R .cnt) L with hV1
  set h1' := pos + L + 1 with hh1'
  have e1 : WExec cap (.seq (.inc (R .flag)) (.whr (R .flag) (unaryBody false i (R .flag) (R .cnt)))) σ (regState σ i h1' V1)
      (10 * L + 13) :=
    WExec.cast cap (unary_step cap i (R .flag) (R .cnt) (hne .flag .cnt (by decide)) σ h0 h1 (by rw [hd, hpos, hL]; omega))
      (by rw [hd, hpos, hL]; rfl) (by rw [hd, hpos, hL])
  -- 2. the position counter `R .cd += 2L + 1`
  set V2 := Function.update V1 (R .cd) (cd + L) with hV2
  set V3 := Function.update V2 (R .cd) (cd + 2 * L) with hV3
  set V4 := Function.update V3 (R .cd) (cd + 2 * L + 1) with hV4
  set V5 := Function.update V4 (R .gc) L with hV5
  set V6 := Function.update V5 (R .hc) lb with hV6
  set V8 := Function.update (Function.update (Function.update V6 (R .gc) 0) (R .hc) (lb - L)) (R .zg)
    (if lb < L then 1 else 0) with hV8
  set V9 := Function.update V8 (R .hc) 0 with hV9
  have e3 : WExec cap (addTo (R .cnt) (R .cd) (R .tmp)) (regState σ i h1' V1) (regState σ i h1' V2) (18 * L + 3) :=
    WExec.cast cap (addTo_spec cap (R .cnt) (R .cd) (R .tmp) (hne .cnt .cd (by decide)) (hne .cnt .tmp (by decide))
      (hne .cd .tmp (by decide)) (regState σ i h1' V1) (by simp [hV1, Function.update_apply, hR.eq_iff, h4])
      (by simp [hV1]; omega) (by simp [hV1, Function.update_apply, hR.eq_iff, hcd]; omega))
      (by rw [regState_setv]; congr 2; simp [hV1, Function.update_apply, hR.eq_iff, hcd])
      (by simp [hV1])
  have e4 : WExec cap (addTo (R .cnt) (R .cd) (R .tmp)) (regState σ i h1' V2) (regState σ i h1' V3) (18 * L + 3) :=
    WExec.cast cap (addTo_spec cap (R .cnt) (R .cd) (R .tmp) (hne .cnt .cd (by decide)) (hne .cnt .tmp (by decide))
      (hne .cd .tmp (by decide)) (regState σ i h1' V2) (by simp [hV2, hV1, Function.update_apply, hR.eq_iff, h4])
      (by simp [hV2, hV1, Function.update_apply, hR.eq_iff]; omega)
      (by simp [hV2, hV1, Function.update_apply, hR.eq_iff]; omega))
      (by rw [regState_setv]; congr 2; simp [hV2, hV1, Function.update_apply, hR.eq_iff]; ring)
      (by simp [hV2, hV1, Function.update_apply, hR.eq_iff])
  have e5 : WExec cap (WM.inc (R .cd)) (regState σ i h1' V3) (regState σ i h1' V4) 3 :=
    WExec.cast cap (WExec.inc (cap := cap) (R .cd) (regState σ i h1' V3)
      (by simp [hV3, Function.update_apply, hR.eq_iff]; omega))
      (by rw [regState_setv]; congr 2; simp [hV3]) le_rfl
  -- 3. the guard copies `R .gc := L`, `R .hc := lb`
  have e6 : WExec cap (addTo (R .cnt) (R .gc) (R .tmp)) (regState σ i h1' V4) (regState σ i h1' V5) (18 * L + 3) :=
    WExec.cast cap (addTo_spec cap (R .cnt) (R .gc) (R .tmp) (hne .cnt .gc (by decide)) (hne .cnt .tmp (by decide))
      (hne .gc .tmp (by decide)) (regState σ i h1' V4)
      (by simp [hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h4])
      (by simp [hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff]; omega)
      (by simp [hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h5]; omega))
      (by rw [regState_setv]; congr 2; simp [hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h5])
      (by simp [hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff])
  have e7 : WExec cap (addTo b (R .hc) (R .tmp)) (regState σ i h1' V5) (regState σ i h1' V6) (18 * lb + 3) :=
    WExec.cast cap (addTo_spec cap b (R .hc) (R .tmp) (hb' .hc) (hb' .tmp) (hne .hc .tmp (by decide))
      (regState σ i h1' V5) (by simp [hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h4])
      (by simp [hV5, hV4, hV3, hV2, hV1, Function.update_apply, hb', hlb]; omega)
      (by simp [hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, hb', h6, hlb]; omega))
      (by rw [regState_setv]; congr 2; simp [hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, hb', h6, hlb])
      (by simp [hV5, hV4, hV3, hV2, hV1, Function.update_apply, hb', hlb])
  -- 4. the guard loop and clearing the bound copy
  have e8 : WExec cap (.whr (R .gc) (.seq (.dec (R .gc)) (.ifr (R .hc) (.dec (R .hc)) (WM.setF (R .zg)))))
      (regState σ i h1' V6) (regState σ i h1' V8) (L * 9 + 1) :=
    WExec.cast cap (guard_step cap (R .gc) (R .hc) (R .zg) (hne .gc .hc (by decide)) (hne .gc .zg (by decide))
      (hne .hc .zg (by decide)) (regState σ i h1' V6) L lb (by simp [hV6, hV5, Function.update_apply, hR.eq_iff])
      (by simp [hV6]) (by simp [hV6, hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h7]) (by omega))
      (by rw [regState_setv, regState_setv, regState_setv]) le_rfl
  have e9 : WExec cap (WM.clear (R .hc)) (regState σ i h1' V8) (regState σ i h1' V9) (3 * (lb - L) + 1) :=
    WExec.cast cap (wclear_spec cap (R .hc) (lb - L) (regState σ i h1' V8)
      (by simp [hV8, Function.update_apply, hR.eq_iff]) (by simp [hV8, Function.update_apply, hR.eq_iff]; omega))
      (by rw [regState_setv]) le_rfl
  have hV9_1 : V9 (R .cnt) = L := by simp [hV9, hV8, hV6, hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff]
  have hV9_2 : V9 (R .val) = v₀ := by
    simp [hV9, hV8, hV6, hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, hv₀]
  have hV9_3 : V9 (R .pw) = 0 := by
    simp [hV9, hV8, hV6, hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h3]
  have hV9_4 : V9 (R .tmp) = 0 := by
    simp [hV9, hV8, hV6, hV5, hV4, hV3, hV2, hV1, Function.update_apply, hR.eq_iff, h4]
  have hV9_7 : V9 (R .zg) = if lb < L then 1 else 0 := by simp [hV9, hV8, Function.update_apply, hR.eq_iff]

  have hfinal : ∀ (W : Fin nr → ℕ), W (R .cnt) = 0 → W (R .pw) = 0 → W (R .zg) = (if lb < L then 1 else 0) →
      (∀ j, j ≠ R .cnt → j ≠ R .pw → j ≠ R .zg → j ≠ R .val → W j = V9 j) →
      W (R .val) = v₀ + fieldVal d pos lb →
      Function.update (Function.update (Function.update σ.val (R .val) (v₀ + fieldVal d pos lb)) (R .cd)
        (cd + 2 * L + 1)) (R .zg) (if lb < L then 1 else 0) = W := by
    intro W hW1 hW3 hW7 hW hW2
    funext j
    rcases freg_cases R j with ⟨a, rfl⟩ | hj
    · by_cases ha1 : a = .cnt
      · subst ha1; simp [Function.update_apply, hR.eq_iff, hW1, h1]
      by_cases ha3 : a = .pw
      · subst ha3; simp [Function.update_apply, hR.eq_iff, hW3, h3]
      by_cases ha7 : a = .zg
      · subst ha7; simp [Function.update_apply, hR.eq_iff, hW7]
      by_cases ha2 : a = .val
      · subst ha2; simp [Function.update_apply, hR.eq_iff, hW2]
      rw [hW _ (hne a .cnt ha1) (hne a .pw ha3) (hne a .zg ha7) (hne a .val ha2)]
      cases a <;>
        first
        | (exfalso; exact ha1 rfl) | (exfalso; exact ha3 rfl) | (exfalso; exact ha7 rfl) | (exfalso; exact ha2 rfl)
        | simp [Function.update_apply, hR.eq_iff, hV9, hV8, hV6, hV5, hV4, hV3, hV2, hV1, h5, h6]
    · rw [hW j (hj .cnt) (hj .pw) (hj .zg) (hj .val)]
      simp [Function.update_apply, hj, hV9, hV8, hV6, hV5, hV4, hV3, hV2, hV1]
  by_cases hg : lb < L
  · -- 5a. over the guard: skip the payload, the value is `0`
    have hv7 : (regState σ i h1' V9).val (R .zg) ≠ 0 := by simp [hV9_7, hg]
    have es := skipPairs_spec cap false i (R .cnt) L (regState σ i h1' V9) (by simp [hV9_1])
      (by simp [hV9_1]; omega)
    rw [regState_setv, regState_seth, regState_sh_self, stp_false] at es
    have hall := WExec.seq e1 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
      (WExec.seq e8 (WExec.seq e9 (WExec.ifrT (Q := .seq (.inc (R .pw)) (.seq (.whr (R .cnt) (.seq (.dec (R .cnt))
        (bitBody false i (R .val) (R .pw) (R .tmp)))) (WM.clear (R .pw)))) hv7 es))))))))
    have hfe : fieldEnd d pos = pos + L + 1 + 1 * L := by unfold fieldEnd; rw [hL]; ring
    have hfv : fieldVal d pos lb = 0 := by unfold fieldVal; rw [hL, if_neg (by omega)]
    refine WExec.cast cap hall ?_ ?_
    · rw [hfe, hfinal]
      · simp
      · simp [Function.update_apply, hR.eq_iff, hV9_3]
      · simp [Function.update_apply, hR.eq_iff, hV9_7]
      · intro j hj1 hj3 hj7 hj2; simp [Function.update_apply, hj1]
      · simp [Function.update_apply, hR.eq_iff, hV9_2, hfv]
    · unfold fieldCost
      have e2' : 400 * (L + lb + 2) * (2 ^ lb + 1) =
          400 * (L * 2 ^ lb) + 400 * (lb * 2 ^ lb) + 800 * 2 ^ lb + 400 * L + 400 * lb + 800 := by ring
      rw [e2']
      omega
  · -- 5b. within the guard: read the payload
    have hLlb : L ≤ lb := by omega
    have hv7 : (regState σ i h1' V9).val (R .zg) = 0 := by simp [hV9_7, hg]
    have ei := WExec.inc (cap := cap) (R .pw) (regState σ i h1' V9) (by simp [hV9_3]; omega)
    rw [regState_setv] at ei
    set Vb := Function.update V9 (R .pw) ((regState σ i h1' V9).val (R .pw) + 1) with hVb
    set σb := regState σ i (pos + L + 1) Vb with hσb
    set bs := payload d (pos + L + 1) L with hbs
    have hbsl : bs.length = L := payload_length _ _ _
    have hσb1 : σb.val (R .cnt) = L := by simp [σb, hVb, Function.update_apply, hR.eq_iff, hV9_1]
    have hσb3 : σb.val (R .pw) = 1 := by simp [σb, hVb, hV9_3]
    have hσb2 : σb.val (R .val) = v₀ := by simp [σb, hVb, Function.update_apply, hR.eq_iff, hV9_2]
    have hσb4 : σb.val (R .tmp) = 0 := by simp [σb, hVb, Function.update_apply, hR.eq_iff, hV9_4]
    have hσbsh : σb.sh i = pos + L + 1 := by simp [σb]
    have hσbst : σb.st i = d := by simp [σb, hd]
    have h0p : payState false σb i (R .cnt) (R .val) (R .pw) L v₀ bs 0 = σb := by
      apply WState.eq
      · rw [hσb]; simp [payState, regState]
      · simp [payState]
      · funext j
        simp only [payState, WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs with h3' h2' h1'
        · rw [h3', hσb3]; rfl
        · rw [h2', hσb2]; simp [CanonicalBinary.bitsValue]
        · rw [h1', hσb1]; rfl
        · rfl
      · simp [payState]
    have hreadP : ∀ m < L, readTapeBit (σb.st i) (σb.sh i + stp false * m + off false) = bs.getD m false := by
      intro m hm
      rw [hσbst, hσbsh, stp_false, off_false, one_mul, Nat.add_zero, List.getD_eq_getElem _ _ (by omega)]
      simp [bs, payload]
    have hvalk : ∀ k ≤ L, CanonicalBinary.bitsValue (bs.take k) < 2 ^ k := by
      intro k hk
      have h := bitsValue_lt (bs.take k)
      rwa [List.length_take_of_le (by omega)] at h
    have hpowL : 2 ^ L ≤ 2 ^ lb := Nat.pow_le_pow_right (by norm_num) hLlb
    have hpowL1 : 2 ^ (L + 1) ≤ 2 ^ (lb + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hloop := UnionMachine.Round.wloop cap (R .cnt) (bitBody false i (R .val) (R .pw) (R .tmp)) (36 * 2 ^ L + 12) L
      (payState false σb i (R .cnt) (R .val) (R .pw) L v₀ bs)
      (fun k _ => by simp [payState, Function.update_apply, hR.eq_iff])
      (by omega)
      (fun k hk => bitRound_spec cap false i (R .cnt) (R .val) (R .pw) (R .tmp) (hne .cnt .val (by decide)) (hne .cnt .pw (by decide))
        (hne .cnt .tmp (by decide)) (hne .pw .val (by decide)) (hne .pw .tmp (by decide)) (hne .val .tmp (by decide)) σb L v₀ bs hbsl hσb4
        hreadP (by omega) hvalk k hk)
    rw [h0p] at hloop
    have hσc3 : (payState false σb i (R .cnt) (R .val) (R .pw) L v₀ bs L).val (R .pw) = 2 ^ L := by simp [payState]
    have ec := wclear_spec cap (R .pw) (2 ^ L) _ hσc3 (by rw [hσc3]; omega)
    have hall := WExec.seq e1 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
      (WExec.seq e8 (WExec.seq e9 (WExec.ifrF (P := skipPairs false i (R .cnt)) hv7
        (WExec.seq ei (WExec.seq hloop ec))))))))))
    have hval : CanonicalBinary.bitsValue (bs.take L) = fieldVal d pos lb := by
      rw [← hbsl, List.take_length]; unfold fieldVal; rw [hL, if_pos hLlb]
    have hfe : fieldEnd d pos = pos + L + 1 + stp false * L := by unfold fieldEnd; rw [hL, stp_false]; ring
    refine WExec.cast cap hall ?_ ?_
    · have hst : (payState false σb i (R .cnt) (R .val) (R .pw) L v₀ bs L).setv (R .pw) 0 =
          regState σ i (fieldEnd d pos) (Function.update (Function.update (Function.update Vb (R .cnt) 0) (R .val)
            (v₀ + fieldVal d pos lb)) (R .pw) 0) := by
        rw [hfe]
        simp only [payState, σb, regState_seth, regState_sh_self, regState_setv, Nat.sub_self, hval]
        congr 1
        funext j
        simp only [Function.update_apply]
        split_ifs <;> rfl
      rw [hst, hfinal]
      · simp [hR.eq_iff]
      · simp
      · simp [Function.update_apply, hR.eq_iff, hVb, hV9_7, hg]
      · intro j hj1 hj3 hj7 hj2; simp [Function.update_apply, hj1, hj3, hj2, hVb]
      · simp [Function.update_apply, hR.eq_iff]
    · unfold fieldCost
      have hA : L * 2 ^ L ≤ L * 2 ^ lb := Nat.mul_le_mul_left _ hpowL
      have hC : lb * 1 ≤ lb * 2 ^ lb := Nat.mul_le_mul_left _ hpow1
      have e1' : L * (36 * 2 ^ L + 12 + 4) = 36 * (L * 2 ^ L) + 16 * L := by ring
      have e2' : 400 * (L + lb + 2) * (2 ^ lb + 1) =
          400 * (L * 2 ^ lb) + 400 * (lb * 2 ^ lb) + 800 * 2 ^ lb + 400 * L + 400 * lb + 800 := by ring
      rw [e1', e2']
      generalize L * 2 ^ L = A at *
      generalize L * 2 ^ lb = B at *
      generalize lb * 2 ^ lb = C at *
      generalize 2 ^ L = Q at *
      generalize 2 ^ lb = P at *
      omega

end NearCubicGates.Close.Succinct
