import SourceAdapters.Joins.FieldCells
import Proof.Gates.Cells.Arith

/-!
# Join FieldCells, proved: field macros of the cell language

Proof of `Joins.FieldCells` (proof of `thm:short-pcp-ours`, "each field operation takes poly(f) steps"): the sum `fxorS`, the
product `fmulS`, the power `fpowS` and the inverse `finvS` of `𝔽₂[X]/(p)` on words `< 2^ℓ`, as programs of the
released cell language (`L/Proof/Gates/Cells/Lang.lean`), with their specifications in the Hoare layer `Hs`.

* The sum is a bit loop (`ℓ` passes) with the invariant `z = (x ⊕ y) mod 2^k` (`xor_step`).
* The product follows the released reference `GF.mulStep` pass by pass (`L/Proof/Wire_3_5/GFRef.lean`):
  the invariant is `GF.mulStep_fold`, the LFSR step `GF.lfsr_spec`; the result is `GF2.fmulShift`, the field product
  by `GF.fmulShift_spec`.
* The power is square-and-multiply over the bits of the exponent (`size e` passes, `Nat.size` as the measure).
* The inverse is the power `2^ℓ − 2`; `x^(2^ℓ − 2) · x = 1` for `x ≠ 0` is `FiniteField.pow_card_sub_one_eq_one`
  on `AdjoinRoot (toPoly p)` (a field when `p` is irreducible, with `2^ℓ` elements by `GF.encEquiv`).

-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace NearCubicGates.Adapters.ShortPCP.Machines

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.FieldCells

/-! ## Variables -/

theorem vr_val {i : ℕ} (h : i < VV) : (vr i).val = i := Nat.mod_eq_of_lt h

theorem vr_ne {i j : ℕ} (hij : i ≠ j) (hi : i < VV) (hj : j < VV) : vr i ≠ vr j := by
  intro h; have := congrArg Fin.val h; rw [vr_val hi, vr_val hj] at this; exact hij this

theorem out_ne {s k i : ℕ} {x : Fin VV} (hx : Out s k x) (hi : i < k) (hs : s + k ≤ VV) : x ≠ vr (s + i) := by
  intro h; have := congrArg Fin.val h; rw [vr_val (by omega)] at this; unfold Out at hx; omega

theorem out_sub {s k s' k' : ℕ} {x : Fin VV} (hx : Out s k x) (h1 : s ≤ s') (h2 : s' + k' ≤ s + k) : Out s' k' x := by
  unfold Out at *; omega

theorem out_vr {s k i : ℕ} (h : i < s ∨ s + k ≤ i) (hi : i < VV) : Out s k (vr i) := by
  unfold Out; rw [vr_val hi]; exact h

theorem mem_blk {s k : ℕ} (y : Fin VV) (hs : s + k ≤ VV) : y ∈ blk s k ↔ s ≤ y.val ∧ y.val < s + k := by
  unfold blk
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; rw [vr_val (by omega)]; omega
  · intro h; refine ⟨y.val - s, by omega, ?_⟩; apply Fin.ext; rw [vr_val (by omega)]; omega

theorem vr_mem_blk {s k i : ℕ} (hi : i < k) (hs : s + k ≤ VV) : vr (s + i) ∈ blk s k := by
  rw [mem_blk _ hs, vr_val (by omega)]; omega

theorem vr_mem_blk0 {s k : ℕ} (hk : 0 < k) (hs : s + k ≤ VV) : vr s ∈ blk s k := by
  simpa using vr_mem_blk (s := s) hk hs

/-- A frame inside a sub-block is a frame in the block. -/
theorem fr_blk {a b : DS VV MM} {z : Fin VV} {s k s' k' : ℕ} (h : Fr a b (z :: blk s' k')) (h1 : s ≤ s')
    (h2 : s' + k' ≤ s + k) (hs : s + k ≤ VV) (z' : Fin VV) (hz : z = z' ∨ z ∈ blk s k) :
    Fr a b (z' :: blk s k) := by
  refine Fr.weaken h (fun y hy => ?_)
  rcases List.mem_cons.mp hy with rfl | hy
  · rcases hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hz
  · rw [mem_blk _ (by omega)] at hy
    exact List.mem_cons_of_mem _ ((mem_blk _ hs).mpr (by omega))

theorem fr_sub {a b : DS VV MM} {T T' : List (Fin VV)} (h : Fr a b T) (hT : ∀ y ∈ T, y ∈ T') : Fr a b T' :=
  Fr.weaken h hT

theorem sh_set (a : DS VV MM) (x : Fin VV) (v : ℕ) : (a.set x v).sh = a.sh := rfl

/-- Sequencing with a cost target. -/
theorem hseq {C : Ctx} {s u : St VV MM} {a : DS VV MM} {t1 t2 t : ℕ} {R1 R2 : DS VV MM → Prop} (h1 : Hs C s a t1 R1)
    (h2 : ∀ b, R1 b → Hs C u b t2 R2) (ht : t1 + t2 + 1 ≤ t) : Hs C (.seq s u) a t R2 :=
  Hs.mono (Hs.seq h1 h2) ht (fun _ h => h)

/-! ## Bits -/

variable (C : Ctx)

theorem bitS_spec (u bu : Fin VV) (h : u ≠ bu) (e : DS VV MM) :
    Hs C (bitS u bu) e 7 (fun f => f.env u = e.env u / 2 ∧ f.env bu = e.env u % 2 ∧ f.sh = e.sh ∧
      Fr e f [u, bu]) := by
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_copy C bu u e (Ne.symm h)) (fun e1 he1 => ?_)
  subst he1
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_half C u _) (fun e2 he2 => ?_)
  subst he2
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C bu u _ (Ne.symm h) ?_) (fun e3 he3 => ?_)
  · simp only [DS.set_env_self, DS.set_env_ne _ _ h, DS.set_env_ne _ _ (Ne.symm h)]; exact Nat.div_le_self _ _
  subst he3
  refine Hs.mono (hs_sub C bu u _ (Ne.symm h) ?_) le_rfl ?_
  · simp only [DS.set_env_self, DS.set_env_ne _ _ h, DS.set_env_ne _ _ (Ne.symm h)]; omega
  rintro f rfl
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp only [DS.set_env_ne _ _ h, DS.set_env_self, DS.set_env_ne _ _ (Ne.symm h)]
  · simp only [DS.set_env_self, DS.set_env_ne _ _ h, DS.set_env_ne _ _ (Ne.symm h)]; omega
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [DS.set_env_ne _ _ hy.1, DS.set_env_ne _ _ hy.2]


theorem out_ne0 {s k : ℕ} {x : Fin VV} (hx : Out s k x) (hk : 0 < k) (hs : s + k ≤ VV) : x ≠ vr s := by
  simpa using out_ne (i := 0) hx hk hs

/-- Distinctness of two variables: by hypothesis, by an `Out` fact, or by their numbers. -/
macro "vne" : tactic => `(tactic| first
  | assumption
  | exact Ne.symm (by assumption)
  | (apply vr_ne; omega; omega; omega)
  | (apply out_ne; assumption; omega; omega)
  | (apply out_ne0; assumption; omega; omega)
  | (apply Ne.symm; apply out_ne; assumption; omega; omega)
  | (apply Ne.symm; apply out_ne0; assumption; omega; omega)
  | (rw [show vr _ = vr (_ + 0) from rfl]; apply vr_ne; omega; omega; omega))

/-- Read a variable through `set`s. -/
macro "rd" : tactic => `(tactic| simp (disch := vne) only [DS.set_env_ne, DS.set_env_self])

theorem nm2 {y a b : Fin VV} (h1 : y ≠ a) (h2 : y ≠ b) : y ∉ [a, b] := by simp [h1, h2]

theorem div2_pow (X k : ℕ) : X / 2 ^ k / 2 = X / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]

theorem xor_step (A B k : ℕ) : (A ^^^ B) % 2 ^ (k + 1) =
    (A ^^^ B) % 2 ^ k + (if A / 2 ^ k % 2 = B / 2 ^ k % 2 then 0 else 2 ^ k) := by
  rw [Nat.mod_pow_succ, Nat.xor_div_two_pow]
  have key : ∀ P Q : ℕ, (P ^^^ Q) % 2 = if P % 2 = Q % 2 then 0 else 1 := by
    intro P Q
    have h := Nat.testBit_xor P Q 0
    simp only [Nat.testBit_zero] at h
    rcases Nat.mod_two_eq_zero_or_one P with hp | hp <;> rcases Nat.mod_two_eq_zero_or_one Q with hq | hq <;>
      rcases Nat.mod_two_eq_zero_or_one (P ^^^ Q) with hr | hr <;> simp [hp, hq, hr] at h ⊢
  rw [key]; split_ifs <;> ring

/-- The invariant of the sum after `k` passes. -/
def XorInv (a : DS VV MM) (z t : Fin VV) (s ℓ X Y k : ℕ) (e : DS VV MM) : Prop :=
  e.env (vr s) = X / 2 ^ k ∧ e.env (vr (s + 1)) = Y / 2 ^ k ∧ e.env (vr (s + 2)) = 2 ^ k ∧
    e.env z = (X ^^^ Y) % 2 ^ k ∧ e.env t = 2 ^ ℓ ∧ e.sh = a.sh ∧ Fr a e (z :: blk s 5)

theorem frSet {a e : DS VV MM} {T : List (Fin VV)} {y : Fin VV} (v : ℕ) (hy : y ∈ T) (h : Fr a e T) :
    Fr a (e.set y v) T := Fr.trans h (Fr.set e v hy)

theorem mem_zblk {z : Fin VV} {s k i : ℕ} (hi : i < k) (hs : s + k ≤ VV) : vr (s + i) ∈ z :: blk s k :=
  List.mem_cons_of_mem _ (vr_mem_blk hi hs)

theorem mem_zblk0 {z : Fin VV} {s k : ℕ} (hk : 0 < k) (hs : s + k ≤ VV) : vr s ∈ z :: blk s k :=
  List.mem_cons_of_mem _ (vr_mem_blk0 hk hs)

/-- One pass of the sum. -/
theorem xorPass (z t : Fin VV) (s ℓ X Y k : ℕ) (a e : DS VV MM) (hs : s + 5 ≤ VV) (hz : Out s 5 z)
    (ht : Out s 5 t) (hzt : z ≠ t) (hk : k < ℓ) (hW : ℓ + 1 ≤ C.Wd) (hI : XorInv a z t s ℓ X Y k e) :
    Hs C (xorBody z s) e 20 (XorInv a z t s ℓ X Y (k + 1)) := by
  have hs' : s + 5 ≤ 128 := hs
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  have hWl : 2 ^ ℓ < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hk1 : 2 ^ (k + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk
  unfold xorBody
  refine hseq (t2 := 12) (bitS_spec C (vr s) (vr (s + 3)) (by vne) e) (fun e1 ⟨j1, j2, j3, j4⟩ => ?_) (by omega)
  refine hseq (t2 := 4) (bitS_spec C (vr (s + 1)) (vr (s + 4)) (by vne) e1) (fun e2 ⟨k1, k2, k3, k4⟩ => ?_)
    (by omega)
  have hu : e2.env (vr s) = X / 2 ^ (k + 1) := by
    rw [k4 _ (nm2 (by vne) (by vne)), j1, i1, div2_pow]
  have hbu : e2.env (vr (s + 3)) = X / 2 ^ k % 2 := by rw [k4 _ (nm2 (by vne) (by vne)), j2, i1]
  have hv : e2.env (vr (s + 1)) = Y / 2 ^ (k + 1) := by
    rw [k1, j4 _ (nm2 (by vne) (by vne)), i2, div2_pow]
  have hbv : e2.env (vr (s + 4)) = Y / 2 ^ k % 2 := by rw [k2, j4 _ (nm2 (by vne) (by vne)), i2]
  have hw : e2.env (vr (s + 2)) = 2 ^ k := by
    rw [k4 _ (nm2 (by vne) (by vne)), j4 _ (nm2 (by vne) (by vne)), i3]
  have hzz : e2.env z = (X ^^^ Y) % 2 ^ k := by
    rw [k4 _ (nm2 (by vne) (by vne)), j4 _ (nm2 (by vne) (by vne)), i4]
  have htt : e2.env t = 2 ^ ℓ := by
    rw [k4 _ (nm2 (by vne) (by vne)), j4 _ (nm2 (by vne) (by vne)), i5]
  have hsh : e2.sh = a.sh := by rw [k3, j3, i6]
  have hf2 : Fr a e2 (z :: blk s 5) := Fr.trans i7 (Fr.trans (Fr.weaken j4 (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact mem_zblk0 (by norm_num) hs
    · exact mem_zblk (i := 3) (by norm_num) hs)) (Fr.weaken k4 (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact mem_zblk (i := 1) (by norm_num) hs
    · exact mem_zblk (i := 4) (by norm_num) hs)))
  have hstep := xor_step X Y k
  have hlt : (X ^^^ Y) % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  let R : DS VV MM → Prop := fun b => b.env z = (X ^^^ Y) % 2 ^ (k + 1) ∧ b.env (vr s) = X / 2 ^ (k + 1) ∧
    b.env (vr (s + 1)) = Y / 2 ^ (k + 1) ∧ b.env (vr (s + 2)) = 2 ^ k ∧ b.env t = 2 ^ ℓ ∧ b.sh = a.sh ∧
    Fr a b (z :: blk s 5)
  refine hseq (t1 := 2) (t2 := 1) (R1 := R) (Hs.ite (by show vr (s + 3) ≠ vr (s + 4); vne) (fun hc => ?_)
    (fun hc => ?_)) (fun e3 hR => ?_) (by omega)
  · simp only [Cnd.eval, hbu, hbv, decide_eq_true_eq] at hc
    refine Hs.mono (hs_zero C (vr (s + 3)) e2) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, by rw [sh_set, hsh], frSet _ (mem_zblk (i := 3) (by norm_num) hs) hf2⟩
    · rd; rw [hzz, hstep, if_pos hc, add_zero]
    · rd; rw [hu]
    · rd; rw [hv]
    · rd; rw [hw]
    · rd; rw [htt]
  · simp only [Cnd.eval, hbu, hbv, decide_eq_false_iff_not] at hc
    refine Hs.mono (hs_add C z (vr (s + 2)) e2 (by vne) (by rw [hzz, hw]; rw [pow_succ] at hk1; omega)) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, by rw [sh_set, hsh], frSet _ List.mem_cons_self hf2⟩
    · rw [DS.set_env_self, hzz, hw, hstep, if_neg hc]
    · rd; rw [hu]
    · rd; rw [hv]
    · rd; rw [hw]
    · rd; rw [htt]
  · obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hR
    refine Hs.mono (hs_shl C (vr (s + 2)) e3 (by rw [r4, ← pow_succ']; omega)) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, by rw [sh_set, r6], frSet _ (mem_zblk (i := 2) (by norm_num) hs) r7⟩
    · rd; rw [r2]
    · rd; rw [r3]
    · rw [DS.set_env_self, r4, pow_succ]; ring
    · rd; rw [r1]
    · rd; rw [r5]

/-- **The sum** (`FieldCells` conjunct 1). -/
theorem fxorS_spec (x y z t : Fin VV) (s ℓ : ℕ) (a : DS VV MM) (hs : s + 5 ≤ VV) (hx : Out s 5 x)
    (hy : Out s 5 y) (hz : Out s 5 z) (ht : Out s 5 t) (hzx : z ≠ x) (hzy : z ≠ y) (hzt : z ≠ t)
    (hta : a.env t = 2 ^ ℓ) (hW : ℓ + 1 ≤ C.Wd) :
    Hs C (fxorS x y z t s) a (xorCost ℓ)
      (fun b => b.env z = (a.env x ^^^ a.env y) % 2 ^ ℓ ∧ b.sh = a.sh ∧ Fr a b (z :: blk s 5)) := by
  have hs' : s + 5 ≤ 128 := hs
  have hz' := hz
  have ht' := ht
  set X := a.env x
  set Y := a.env y
  unfold fxorS xorCost
  refine hseq (t2 := 22 * ℓ + 10) (hs_copy C (vr s) x a (by vne)) (fun e1 he1 => ?_) (by omega)
  subst he1
  refine hseq (t2 := 22 * ℓ + 8) (hs_copy C (vr (s + 1)) y _ (by vne)) (fun e2 he2 => ?_) (by omega)
  subst he2
  refine hseq (t2 := 22 * ℓ + 6) (hs_zero C z _) (fun e3 he3 => ?_) (by omega)
  subst he3
  refine hseq (t2 := 22 * ℓ + 4) (hs_zero C (vr (s + 2)) _) (fun e4 he4 => ?_) (by omega)
  subst he4
  refine hseq (t2 := 22 * ℓ + 2) (hs_inc C (vr (s + 2)) _ (by rd; exact Nat.one_lt_two_pow (by omega)))
    (fun e5 he5 => ?_) (by omega)
  subst he5
  have h0 : XorInv a z t s ℓ X Y 0 ((((((a.set (vr s) X).set (vr (s + 1)) ((a.set (vr s) X).env y)).set z 0).set
      (vr (s + 2)) 0).set (vr (s + 2)) ((((((a.set (vr s) X).set (vr (s + 1)) ((a.set (vr s) X).env y)).set z 0).set
      (vr (s + 2)) 0)).env (vr (s + 2)) + 1))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rd; simp
    · rd; simp [Y]
    · rd; simp
    · rd; rw [pow_zero, Nat.mod_one]
    · rd; exact hta
    · exact frSet _ (mem_zblk (i := 2) (by norm_num) hs) (frSet _ (mem_zblk (i := 2) (by norm_num) hs)
        (frSet _ List.mem_cons_self (frSet _ (mem_zblk (i := 1) (by norm_num) hs)
        (frSet _ (mem_zblk0 (by norm_num) hs) (Fr.refl _ _)))))
  have hl := Hs.loopN (C := C) (c := .lt (vr (s + 2)) t) (s := xorBody z s) (by show vr (s + 2) ≠ t; vne)
    (XorInv a z t s ℓ X Y) ℓ 20 (fun k hk e hI => ⟨by
      obtain ⟨_, _, i3, _, i5, _, _⟩ := hI
      simp only [Cnd.eval, i3, i5, decide_eq_true_eq]; exact Nat.pow_lt_pow_right (by norm_num) hk,
      xorPass C z t s ℓ X Y k a e hs hz' ht' hzt hk hW hI⟩) (fun e hI => by
      obtain ⟨_, _, i3, _, i5, _, _⟩ := hI
      simp [Cnd.eval, i3, i5]) _ h0
  refine Hs.mono hl (by ring_nf; omega) ?_
  rintro b ⟨_, _, _, h4, _, h6, h7⟩
  exact ⟨h4, h6, h7⟩

/-! ## Product -/

theorem nmb {y w : Fin VV} {s k : ℕ} (h1 : y ≠ w) (h2 : Out s k y) (hs : s + k ≤ VV) : y ∉ w :: blk s k := by
  intro hy
  rcases List.mem_cons.mp hy with h | h
  · exact h1 h
  · rw [mem_blk _ hs] at h; unfold Out at h2; omega

theorem frIn {a e : DS VV MM} {z w : Fin VV} {s k s' k' : ℕ} (h : Fr a e (z :: blk s k)) (hs : s + k ≤ VV)
    (h1 : s ≤ s') (h2 : s' + k' ≤ s + k) (hw : w ∈ z :: blk s k) {f : DS VV MM} (h' : Fr e f (w :: blk s' k')) :
    Fr a f (z :: blk s k) := by
  refine Fr.trans h (Fr.weaken h' (fun y hy => ?_))
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hw
  · rw [mem_blk _ (by omega)] at hy
    exact List.mem_cons_of_mem _ ((mem_blk _ hs).mpr (by omega))

/-- The state of the shift-and-xor product after `k` passes (`GF.mulStep`). -/
abbrev mst (pv ℓ X Y k : ℕ) : ℕ × ℕ := (List.range k).foldl (GF.mulStep pv ℓ Y) (0, X)

/-- The invariant of the product after `k` passes. -/
def MulInv (a : DS VV MM) (z t p : Fin VV) (s ℓ pv X Y k : ℕ) (e : DS VV MM) : Prop :=
  e.env z = (mst pv ℓ X Y k).1 ∧ e.env (vr s) = (mst pv ℓ X Y k).2 ∧ e.env (vr (s + 1)) = Y / 2 ^ k ∧
    e.env (vr (s + 2)) = 2 ^ k ∧ e.env (vr (s + 4)) = 0 ∧ e.env t = 2 ^ ℓ ∧ e.env p = pv ∧ e.sh = a.sh ∧
    Fr a e (z :: blk s 11)

theorem mst_succ (pv ℓ X Y k : ℕ) : mst pv ℓ X Y (k + 1) = GF.mulStep pv ℓ Y (mst pv ℓ X Y k) k := by
  simp [mst, List.range_succ, List.foldl_append]

/-- One pass of the product. -/
theorem mulPass (z t p : Fin VV) (s ℓ pv X Y k : ℕ) (a e : DS VV MM) (hs : s + 11 ≤ VV) (hz : Out s 11 z)
    (ht : Out s 11 t) (hp : Out s 11 p) (hzt : z ≠ t) (hzp : z ≠ p) (hk : k < ℓ) (hW : ℓ + 1 ≤ C.Wd)
    (hpv : GF.ModulusOk pv ℓ) (hX : X < 2 ^ ℓ) (hI : MulInv a z t p s ℓ pv X Y k e) :
    Hs C (mulBody z t p s) e (2 * xorCost ℓ + 19) (MulInv a z t p s ℓ pv X Y (k + 1)) := by
  have hs' : s + 11 ≤ 128 := hs
  have hz' := hz
  have ht' := ht
  have hp' := hp
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hI
  obtain ⟨f1, f2, _, _⟩ := GF.mulStep_fold pv ℓ X Y hpv hX k
  have hWl : 2 ^ ℓ < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hk1 : 2 ^ (k + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk
  set A := (mst pv ℓ X Y k).2
  set Z := (mst pv ℓ X Y k).1
  unfold mulBody
  refine hseq (t2 := 2 * xorCost ℓ + 11) (bitS_spec C (vr (s + 1)) (vr (s + 3)) (by vne) e)
    (fun e1 ⟨j1, j2, j3, j4⟩ => ?_) (by omega)
  have hbt : e1.env (vr (s + 3)) = Y / 2 ^ k % 2 := by rw [j2, i3]
  have hzr : e1.env (vr (s + 4)) = 0 := by rw [j4 _ (nm2 (by vne) (by vne)), i5]
  have hz1 : e1.env z = Z := by rw [j4 _ (nm2 (by vne) (by vne)), i1]
  have ha1 : e1.env (vr s) = A := by rw [j4 _ (nm2 (by vne) (by vne)), i2]
  have hf1 : Fr a e1 (z :: blk s 11) := Fr.trans i9 (Fr.weaken j4 (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact mem_zblk (i := 1) (by norm_num) hs
    · exact mem_zblk (i := 3) (by norm_num) hs))
  have hzst : (GF.mulStep pv ℓ Y (mst pv ℓ X Y k) k).1 = if Y.testBit k then Z ^^^ A else Z := rfl
  have hast : (GF.mulStep pv ℓ Y (mst pv ℓ X Y k) k).2 = GF2.lfsr pv ℓ A := rfl
  have htb : Y.testBit k = decide (Y / 2 ^ k % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  -- the common state after the first test
  let R1 : DS VV MM → Prop := fun b => b.env z = (GF.mulStep pv ℓ Y (mst pv ℓ X Y k) k).1 ∧ b.env (vr s) = A ∧
    b.env (vr (s + 1)) = Y / 2 ^ (k + 1) ∧ b.env (vr (s + 2)) = 2 ^ k ∧ b.env (vr (s + 4)) = 0 ∧
    b.env t = 2 ^ ℓ ∧ b.env p = pv ∧ b.sh = a.sh ∧ Fr a b (z :: blk s 11)
  have hv1 : e1.env (vr (s + 1)) = Y / 2 ^ (k + 1) := by rw [j1, i3, div2_pow]
  have hw1 : e1.env (vr (s + 2)) = 2 ^ k := by rw [j4 _ (nm2 (by vne) (by vne)), i4]
  have ht1 : e1.env t = 2 ^ ℓ := by rw [j4 _ (nm2 (by vne) (by vne)), i6]
  have hp1 : e1.env p = pv := by rw [j4 _ (nm2 (by vne) (by vne)), i7]
  have hsh1 : e1.sh = a.sh := by rw [j3, i8]
  refine hseq (t1 := xorCost ℓ + 3) (t2 := xorCost ℓ + 7) (R1 := R1)
    (Hs.ite (by show vr (s + 3) ≠ vr (s + 4); vne) (fun hc => ?_) (fun hc => ?_)) (fun e2 hR => ?_) (by omega)
  · simp only [Cnd.eval, hbt, hzr, decide_eq_true_eq] at hc
    refine Hs.mono (hs_zero C (vr (s + 5)) e1) (by omega) ?_
    rintro b rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, hsh1], frSet _ (mem_zblk (i := 5) (by norm_num) hs) hf1⟩
    · rd; rw [hz1, hzst, htb, hc]; rfl
    · rd; rw [ha1]
    · rd; rw [hv1]
    · rd; rw [hw1]
    · rd; rw [hzr]
    · rd; rw [ht1]
    · rd; rw [hp1]
  · simp only [Cnd.eval, hbt, hzr, decide_eq_false_iff_not] at hc
    have hb1 : Y / 2 ^ k % 2 = 1 := by omega
    refine hseq (t2 := 1) (fxorS_spec C z (vr s) (vr (s + 5)) t (s + 6) ℓ e1 (by omega)
      (out_sub hz' (by omega) (by omega)) (out_vr (by omega) (by omega)) (out_vr (by omega) (by omega))
      (out_sub ht' (by omega) (by omega)) (by vne) (by vne) (by vne) ht1 hW) (fun e3 ⟨x1, x2, x3⟩ => ?_) (by omega)
    have hxv : e3.env (vr (s + 5)) = Z ^^^ A := by
      rw [x1, hz1, ha1, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow f1 f2)]
    refine Hs.mono (hs_copy C z (vr (s + 5)) e3 (by vne)) le_rfl ?_
    rintro b rfl
    have hfr3 : Fr a e3 (z :: blk s 11) := frIn hf1 hs (s' := s + 6) (k' := 5) (by omega) (by omega)
      (mem_zblk (i := 5) (by norm_num) hs) x3
    have rd3 : ∀ y, y ≠ vr (s + 5) → Out (s + 6) 5 y → e3.env y = e1.env y := fun y h1 h2 =>
      x3 y (nmb h1 h2 (by omega))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, x2, hsh1], frSet _ List.mem_cons_self hfr3⟩
    · rw [DS.set_env_self, hxv, hzst, htb, hb1]; rfl
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), ha1]
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), hv1]
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), hw1]
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), hzr]
    · rd; rw [rd3 _ (by vne) (out_sub ht' (by omega) (by omega)), ht1]
    · rd; rw [rd3 _ (by vne) (out_sub hp' (by omega) (by omega)), hp1]
  · obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hR
    have h2A : 2 * A < 2 ^ (ℓ + 1) := by rw [pow_succ]; omega
    have hWl1 : 2 ^ (ℓ + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
    obtain ⟨l1, _⟩ := GF.lfsr_spec pv ℓ A hpv f2
    refine hseq (t2 := xorCost ℓ + 5) (hs_shl C (vr s) e2 (by rw [r2]; omega)) (fun e4 he4 => ?_) (by omega)
    subst he4
    have ha4 : (e2.set (vr s) (2 * e2.env (vr s))).env (vr s) = 2 * A := by rw [DS.set_env_self, r2]
    have ht4 : (e2.set (vr s) (2 * e2.env (vr s))).env t = 2 ^ ℓ := by rd; rw [r6]
    have hp4 : (e2.set (vr s) (2 * e2.env (vr s))).env p = pv := by rd; rw [r7]
    have hf4 : Fr a (e2.set (vr s) (2 * e2.env (vr s))) (z :: blk s 11) := frSet _ (mem_zblk0 (by norm_num) hs) r9
    have hsh4 : (e2.set (vr s) (2 * e2.env (vr s))).sh = a.sh := by rw [sh_set, r8]
    let R2 : DS VV MM → Prop := fun b => b.env z = (GF.mulStep pv ℓ Y (mst pv ℓ X Y k) k).1 ∧
      b.env (vr s) = GF2.lfsr pv ℓ A ∧ b.env (vr (s + 1)) = Y / 2 ^ (k + 1) ∧ b.env (vr (s + 2)) = 2 ^ k ∧
      b.env (vr (s + 4)) = 0 ∧ b.env t = 2 ^ ℓ ∧ b.env p = pv ∧ b.sh = a.sh ∧ Fr a b (z :: blk s 11)
    refine hseq (t1 := xorCost ℓ + 3) (t2 := 1) (R1 := R2)
      (Hs.ite (by show vr s ≠ t; vne) (fun hc => ?_) (fun hc => ?_)) (fun e6 hR6 => ?_) (by omega)
    · simp only [Cnd.eval, ha4, ht4, decide_eq_true_eq] at hc
      have hl : GF2.lfsr pv ℓ A = 2 * A := by
        unfold GF2.lfsr; rw [Nat.testBit_lt_two_pow hc]; rfl
      refine Hs.mono (hs_zero C (vr (s + 5)) _) (by omega) ?_
      rintro b rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, hsh4], frSet _ (mem_zblk (i := 5) (by norm_num) hs) hf4⟩
      · rd; rw [r1]
      · rd; rw [hl, r2]
      · rd; rw [r3]
      · rd; rw [r4]
      · rd; rw [r5]
      · rd; rw [r6]
      · rd; rw [r7]
    · simp only [Cnd.eval, ha4, ht4, decide_eq_false_iff_not, not_lt] at hc
      have hl : GF2.lfsr pv ℓ A = 2 * A ^^^ pv := by
        unfold GF2.lfsr; rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hc h2A]; rfl
      refine hseq (t2 := 1) (fxorS_spec C (vr s) p (vr (s + 5)) t (s + 6) ℓ _ (by omega)
        (out_vr (by omega) (by omega)) (out_sub hp' (by omega) (by omega)) (out_vr (by omega) (by omega))
        (out_sub ht' (by omega) (by omega)) (by vne) (by vne) (by vne) ht4 hW) (fun e5 ⟨x1, x2, x3⟩ => ?_)
        (by omega)
      have hxv : e5.env (vr (s + 5)) = GF2.lfsr pv ℓ A := by
        rw [x1, ha4, hp4, ← hl, Nat.mod_eq_of_lt l1]
      have rd5 : ∀ y, y ≠ vr (s + 5) → Out (s + 6) 5 y → e5.env y = (e2.set (vr s) (2 * e2.env (vr s))).env y :=
        fun y h1 h2 => x3 y (nmb h1 h2 (by omega))
      have hfr5 := frIn hf4 hs (s' := s + 6) (k' := 5) (by omega) (by omega) (mem_zblk (i := 5) (by norm_num) hs) x3
      refine Hs.mono (hs_copy C (vr s) (vr (s + 5)) e5 (by vne)) le_rfl ?_
      rintro b rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, x2, hsh4], frSet _ (mem_zblk0 (by norm_num) hs) hfr5⟩
      · rd; rw [rd5 _ (by vne) (out_sub hz' (by omega) (by omega))]; rd; rw [r1]
      · rw [DS.set_env_self, hxv]
      · rd; rw [rd5 _ (by vne) (out_vr (by omega) (by omega))]; rd; rw [r3]
      · rd; rw [rd5 _ (by vne) (out_vr (by omega) (by omega))]; rd; rw [r4]
      · rd; rw [rd5 _ (by vne) (out_vr (by omega) (by omega))]; rd; rw [r5]
      · rd; rw [rd5 _ (by vne) (out_sub ht' (by omega) (by omega)), ht4]
      · rd; rw [rd5 _ (by vne) (out_sub hp' (by omega) (by omega)), hp4]
    · obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hR6
      refine Hs.mono (hs_shl C (vr (s + 2)) e6 (by rw [q4, ← pow_succ']; omega)) le_rfl ?_
      rintro b rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, q8], frSet _ (mem_zblk (i := 2) (by norm_num) hs) q9⟩
      · rd; rw [q1, mst_succ]
      · rd; rw [q2, mst_succ]; rfl
      · rd; rw [q3]
      · rw [DS.set_env_self, q4, pow_succ]; ring
      · rd; rw [q5]
      · rd; rw [q6]
      · rd; rw [q7]

/-- **The product** (`FieldCells` conjunct 2). -/
theorem fmulS_spec (x y z t p : Fin VV) (s ℓ pv : ℕ) (a : DS VV MM) (hs : s + 11 ≤ VV) (hx : Out s 11 x)
    (hy : Out s 11 y) (hz : Out s 11 z) (ht : Out s 11 t) (hp : Out s 11 p) (hzx : z ≠ x) (hzy : z ≠ y)
    (hzt : z ≠ t) (hzp : z ≠ p) (hta : a.env t = 2 ^ ℓ) (hpa : a.env p = pv) (hpv : GF.ModulusOk pv ℓ)
    (hW : ℓ + 1 ≤ C.Wd) (hX : a.env x < 2 ^ ℓ) (hY : a.env y < 2 ^ ℓ) :
    Hs C (fmulS x y z t p s) a (mulCost ℓ)
      (fun b => b.env z = GF2.fmulShift pv ℓ (a.env x) (a.env y) ∧ b.env z < 2 ^ ℓ ∧
        GF.rep pv (b.env z) = GF.rep pv (a.env x) * GF.rep pv (a.env y) ∧ b.sh = a.sh ∧ Fr a b (z :: blk s 11)) := by
  have hs' : s + 11 ≤ 128 := hs
  have hz' := hz
  have ht' := ht
  have hp' := hp
  set X := a.env x
  set Y := a.env y
  set B := ℓ * (2 * xorCost ℓ + 21) + 2
  unfold fmulS mulCost
  refine hseq (t2 := B + 10) (hs_copy C (vr s) x a (by vne)) (fun e1 he1 => ?_) (by omega)
  subst he1
  refine hseq (t2 := B + 8) (hs_copy C (vr (s + 1)) y _ (by vne)) (fun e2 he2 => ?_) (by omega)
  subst he2
  refine hseq (t2 := B + 6) (hs_zero C z _) (fun e3 he3 => ?_) (by omega)
  subst he3
  refine hseq (t2 := B + 4) (hs_zero C (vr (s + 4)) _) (fun e4 he4 => ?_) (by omega)
  subst he4
  refine hseq (t2 := B + 2) (hs_zero C (vr (s + 2)) _) (fun e4 he4 => ?_) (by omega)
  subst he4
  refine hseq (t2 := B) (hs_inc C (vr (s + 2)) _ (by rd; exact Nat.one_lt_two_pow (by omega)))
    (fun e5 he5 => ?_) (by omega)
  subst he5
  refine Hs.mono (Hs.loopN (C := C) (c := .lt (vr (s + 2)) t) (s := mulBody z t p s) (by show vr (s + 2) ≠ t; vne)
    (MulInv a z t p s ℓ pv X Y) ℓ (2 * xorCost ℓ + 19) (fun k hk e hI => ⟨by
      obtain ⟨_, _, _, i4, _, i6, _, _, _⟩ := hI
      simp only [Cnd.eval, i4, i6, decide_eq_true_eq]; exact Nat.pow_lt_pow_right (by norm_num) hk,
      mulPass C z t p s ℓ pv X Y k a e hs hz' ht' hp' hzt hzp hk hW hpv hX hI⟩) (fun e hI => by
      obtain ⟨_, _, _, i4, _, i6, _, _, _⟩ := hI
      simp [Cnd.eval, i4, i6]) _ ?_) (le_of_eq (by simp only [B])) ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rd; simp [mst]
    · rd; simp [mst, X]
    · rd; simp [Y]
    · rd; simp
    · rd
    · rd; exact hta
    · rd; exact hpa
    · exact frSet _ (mem_zblk (i := 2) (by norm_num) hs) (frSet _ (mem_zblk (i := 2) (by norm_num) hs)
        (frSet _ (mem_zblk (i := 4) (by norm_num) hs) (frSet _ List.mem_cons_self
        (frSet _ (mem_zblk (i := 1) (by norm_num) hs) (frSet _ (mem_zblk0 (by norm_num) hs) (Fr.refl _ _))))))
  · rintro b ⟨h1, _, _, _, _, _, _, h8, h9⟩
    obtain ⟨g1, g2⟩ := GF.fmulShift_spec pv ℓ X Y hpv hX hY
    have hf : b.env z = GF2.fmulShift pv ℓ X Y := by rw [h1, GF.fmulShift_eq]
    exact ⟨hf, hf ▸ g1, hf ▸ g2, h8, h9⟩

/-! ## Power -/

/-- The invariant of the power: `rep z · (rep b)^ee = (rep x)^E`. -/
def PowInv (a : DS VV MM) (z t p : Fin VV) (s ℓ pv X E : ℕ) (e : DS VV MM) : Prop :=
  e.env z < 2 ^ ℓ ∧ e.env (vr s) < 2 ^ ℓ ∧
    GF.rep pv (e.env z) * GF.rep pv (e.env (vr s)) ^ e.env (vr (s + 1)) = GF.rep pv X ^ E ∧
    e.env (vr (s + 3)) = 0 ∧ e.env t = 2 ^ ℓ ∧ e.env p = pv ∧ e.sh = a.sh ∧ Fr a e (z :: blk s 16)

theorem pow_half {R : Type} [CommRing R] (z b : R) (N : ℕ) :
    z * (b * b) ^ (N / 2) * (if N % 2 = 0 then 1 else b) = z * b ^ N := by
  conv_rhs => rw [← Nat.div_add_mod N 2]
  rw [pow_add, pow_mul, sq]
  rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h] <;> ring

/-- One pass of the power. -/
theorem powPass (z t p : Fin VV) (s ℓ pv X E : ℕ) (a e : DS VV MM) (hs : s + 16 ≤ VV) (hz : Out s 16 z)
    (ht : Out s 16 t) (hp : Out s 16 p) (hzt : z ≠ t) (hzp : z ≠ p) (hW : ℓ + 1 ≤ C.Wd)
    (hpv : GF.ModulusOk pv ℓ) (hI : PowInv a z t p s ℓ pv X E e) (hpos : 0 < e.env (vr (s + 1))) :
    Hs C (powBody z t p s) e (2 * mulCost ℓ + 14)
      (fun b => PowInv a z t p s ℓ pv X E b ∧ Nat.size (b.env (vr (s + 1))) < Nat.size (e.env (vr (s + 1)))) := by
  have hs' : s + 16 ≤ 128 := hs
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI
  set Z := e.env z
  set B := e.env (vr s)
  set N := e.env (vr (s + 1))
  have hsz := size_succ N hpos
  unfold powBody
  refine hseq (t2 := 2 * mulCost ℓ + 6) (bitS_spec C (vr (s + 1)) (vr (s + 2)) (by vne) e)
    (fun e1 ⟨j1, j2, j3, j4⟩ => ?_) (by omega)
  have hbt : e1.env (vr (s + 2)) = N % 2 := j2
  have hzr : e1.env (vr (s + 3)) = 0 := by rw [j4 _ (nm2 (by vne) (by vne)), i4]
  have hz1 : e1.env z = Z := j4 _ (nm2 (by vne) (by vne))
  have hb1 : e1.env (vr s) = B := j4 _ (nm2 (by vne) (by vne))
  have ht1 : e1.env t = 2 ^ ℓ := by rw [j4 _ (nm2 (by vne) (by vne)), i5]
  have hp1 : e1.env p = pv := by rw [j4 _ (nm2 (by vne) (by vne)), i6]
  have hsh1 : e1.sh = a.sh := by rw [j3, i7]
  have hf1 : Fr a e1 (z :: blk s 16) := Fr.trans i8 (Fr.weaken j4 (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact mem_zblk (i := 1) (by norm_num) hs
    · exact mem_zblk (i := 2) (by norm_num) hs))
  -- after the conditional product
  let R1 : DS VV MM → Prop := fun b => b.env z < 2 ^ ℓ ∧
    GF.rep pv (b.env z) = GF.rep pv Z * (if N % 2 = 0 then 1 else GF.rep pv B) ∧ b.env (vr s) = B ∧
    b.env (vr (s + 1)) = N / 2 ∧ b.env (vr (s + 3)) = 0 ∧ b.env t = 2 ^ ℓ ∧ b.env p = pv ∧ b.sh = a.sh ∧
    Fr a b (z :: blk s 16)
  refine hseq (t1 := mulCost ℓ + 3) (t2 := mulCost ℓ + 2) (R1 := R1)
    (Hs.ite (by show vr (s + 2) ≠ vr (s + 3); vne) (fun hc => ?_) (fun hc => ?_)) (fun e2 hR => ?_) (by omega)
  · simp only [Cnd.eval, hbt, hzr, decide_eq_true_eq] at hc
    refine Hs.mono (hs_zero C (vr (s + 4)) e1) (by omega) ?_
    rintro b rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, hsh1], frSet _ (mem_zblk (i := 4) (by norm_num) hs) hf1⟩
    · rd; rw [hz1]; exact i1
    · rd; rw [hz1, if_pos hc, mul_one]
    · rd; rw [hb1]
    · rd; rw [j1]
    · rd; rw [hzr]
    · rd; rw [ht1]
    · rd; rw [hp1]
  · simp only [Cnd.eval, hbt, hzr, decide_eq_false_iff_not] at hc
    refine hseq (t2 := 1) (fmulS_spec C z (vr s) (vr (s + 4)) t p (s + 5) ℓ pv e1 (by omega)
      (out_sub hz (by omega) (by omega)) (out_vr (by omega) (by omega)) (out_vr (by omega) (by omega))
      (out_sub ht (by omega) (by omega)) (out_sub hp (by omega) (by omega)) (by vne) (by vne) (by vne) (by vne)
      ht1 hp1 hpv hW (by rw [hz1]; exact i1) (by rw [hb1]; exact i2)) (fun e3 ⟨_, x2, x3, x4, x5⟩ => ?_) (by omega)
    have rd3 : ∀ y, y ≠ vr (s + 4) → Out (s + 5) 11 y → e3.env y = e1.env y := fun y h1 h2 =>
      x5 y (nmb h1 h2 (by omega))
    have hfr3 := frIn hf1 hs (s' := s + 5) (k' := 11) (by omega) (by omega) (mem_zblk (i := 4) (by norm_num) hs) x5
    refine Hs.mono (hs_copy C z (vr (s + 4)) e3 (by vne)) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, x4, hsh1], frSet _ List.mem_cons_self hfr3⟩
    · rw [DS.set_env_self]; exact x2
    · rw [DS.set_env_self, x3, hz1, hb1, if_neg hc]
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), hb1]
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), j1]
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), hzr]
    · rd; rw [rd3 _ (by vne) (out_sub ht (by omega) (by omega)), ht1]
    · rd; rw [rd3 _ (by vne) (out_sub hp (by omega) (by omega)), hp1]
  · obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hR
    refine hseq (t2 := 1) (fmulS_spec C (vr s) (vr s) (vr (s + 4)) t p (s + 5) ℓ pv e2 (by omega)
      (out_vr (by omega) (by omega)) (out_vr (by omega) (by omega)) (out_vr (by omega) (by omega))
      (out_sub ht (by omega) (by omega)) (out_sub hp (by omega) (by omega)) (by vne) (by vne) (by vne) (by vne)
      r6 r7 hpv hW (by rw [r3]; exact i2) (by rw [r3]; exact i2)) (fun e3 ⟨_, x2, x3, x4, x5⟩ => ?_) (by omega)
    have rd3 : ∀ y, y ≠ vr (s + 4) → Out (s + 5) 11 y → e3.env y = e2.env y := fun y h1 h2 =>
      x5 y (nmb h1 h2 (by omega))
    have hfr3 := frIn r9 hs (s' := s + 5) (k' := 11) (by omega) (by omega) (mem_zblk (i := 4) (by norm_num) hs) x5
    refine Hs.mono (hs_copy C (vr s) (vr (s + 4)) e3 (by vne)) le_rfl ?_
    rintro b rfl
    have hz3 : e3.env z = e2.env z := rd3 _ (by vne) (out_sub hz (by omega) (by omega))
    have hn3 : e3.env (vr (s + 1)) = N / 2 := by rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), r4]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [sh_set, x4, r8], frSet _ (mem_zblk0 (by norm_num) hs) hfr3⟩, ?_⟩
    · rd; rw [hz3]; exact r1
    · rw [DS.set_env_self]; exact x2
    · rd; rw [hz3, hn3, x3, r2, r3, ← i3, ← pow_half (GF.rep pv Z) (GF.rep pv B) N]; ring
    · rd; rw [rd3 _ (by vne) (out_vr (by omega) (by omega)), r5]
    · rd; rw [rd3 _ (by vne) (out_sub ht (by omega) (by omega)), r6]
    · rd; rw [rd3 _ (by vne) (out_sub hp (by omega) (by omega)), r7]
    · rd; rw [hn3]; omega

theorem rep_one (pv : ℕ) : GF.rep pv 1 = 1 := by simpa using GF.rep_two_pow pv 0

/-- **The power** (`FieldCells` conjunct 3). -/
theorem fpowS_spec (x e z t p : Fin VV) (s ℓ pv : ℕ) (a : DS VV MM) (hs : s + 16 ≤ VV) (hx : Out s 16 x)
    (he : Out s 16 e) (hz : Out s 16 z) (ht : Out s 16 t) (hp : Out s 16 p) (hzx : z ≠ x) (hze : z ≠ e)
    (hzt : z ≠ t) (hzp : z ≠ p) (hta : a.env t = 2 ^ ℓ) (hpa : a.env p = pv) (hpv : GF.ModulusOk pv ℓ)
    (hℓ : 1 ≤ ℓ) (hW : ℓ + 1 ≤ C.Wd) (hX : a.env x < 2 ^ ℓ) :
    Hs C (fpowS x e z t p s) a (powCost ℓ (a.env e))
      (fun b => b.env z < 2 ^ ℓ ∧ GF.rep pv (b.env z) = GF.rep pv (a.env x) ^ a.env e ∧ b.sh = a.sh ∧
        Fr a b (z :: blk s 16)) := by
  have hs' : s + 16 ≤ 128 := hs
  set X := a.env x
  set E := a.env e
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hWl : 2 ^ ℓ < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set B := Nat.size E * (2 * mulCost ℓ + 16) + 2
  unfold fpowS powCost
  refine hseq (t2 := B + 8) (hs_copy C (vr s) x a (by vne)) (fun e1 he1 => ?_) (by omega)
  subst he1
  refine hseq (t2 := B + 6) (hs_copy C (vr (s + 1)) e _ (by vne)) (fun e2 he2 => ?_) (by omega)
  subst he2
  refine hseq (t2 := B + 4) (hs_zero C (vr (s + 3)) _) (fun e3 he3 => ?_) (by omega)
  subst he3
  refine hseq (t2 := B + 2) (hs_zero C z _) (fun e4 he4 => ?_) (by omega)
  subst he4
  refine hseq (t2 := B) (hs_inc C z _ (by rd; omega)) (fun e5 he5 => ?_) (by omega)
  subst he5
  refine Hs.mono (Hs.loopM (C := C) (c := .lt (vr (s + 3)) (vr (s + 1))) (s := powBody z t p s)
    (by show vr (s + 3) ≠ vr (s + 1); vne) (PowInv a z t p s ℓ pv X E) (fun b => Nat.size (b.env (vr (s + 1))))
    (2 * mulCost ℓ + 14) (fun b hI hc => by
      have hpos : 0 < b.env (vr (s + 1)) := by
        obtain ⟨_, _, _, i4, _, _, _, _⟩ := hI
        simpa [Cnd.eval, i4] using hc
      exact powPass C z t p s ℓ pv X E a b hs hz ht hp hzt hzp hW hpv hI hpos) _ ?_) ?_ ?_
  rotate_left
  · rd; simp only [B, E]; apply le_of_eq; ring
  · rintro b ⟨⟨h1, _, h3, h4, _, _, h7, h8⟩, h9⟩
    have h0 : b.env (vr (s + 1)) = 0 := by simpa [Cnd.eval, h4] using h9
    rw [h0, pow_zero, mul_one] at h3
    exact ⟨h1, h3, h7, h8⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rd; omega
    · rd; exact hX
    · rd; rw [rep_one, one_mul]
    · rd
    · rd; exact hta
    · rd; exact hpa
    · exact frSet _ List.mem_cons_self (frSet _ List.mem_cons_self (frSet _ (mem_zblk (i := 3) (by norm_num) hs)
        (frSet _ (mem_zblk (i := 1) (by norm_num) hs) (frSet _ (mem_zblk0 (by norm_num) hs) (Fr.refl _ _)))))

/-! ## Inverse -/

/-- `x^(2^ℓ − 2) · x = 1` for `x ≠ 0` in `𝔽₂[X]/(p)`, `p` irreducible of degree `ℓ` (a field with `2^ℓ`
elements, `FiniteField.pow_card_sub_one_eq_one`). -/
theorem inv_of_pow (pv ℓ X : ℕ) (hpv : GF.ModulusOk pv ℓ) (hℓ : 1 ≤ ℓ) (hirr : Irreducible (GF.toPoly pv))
    (hX : X < 2 ^ ℓ) (hX0 : X ≠ 0) : GF.rep pv X ^ (2 ^ ℓ - 2) * GF.rep pv X = 1 := by
  haveI : Fact (Irreducible (GF.toPoly pv)) := ⟨hirr⟩
  letI : Fintype (AdjoinRoot (GF.toPoly pv)) := Fintype.ofEquiv (Fin (2 ^ ℓ)) (GF.encEquiv pv ℓ hpv)
  have hcard : Fintype.card (AdjoinRoot (GF.toPoly pv)) = 2 ^ ℓ := by
    rw [Fintype.card_congr (GF.encEquiv pv ℓ hpv).symm, Fintype.card_fin]
  have hne : GF.rep pv X ≠ 0 := by
    intro h
    have h0 : GF.rep pv 0 = 0 := by
      unfold GF.rep; rw [show GF.toPoly 0 = 0 by simp [GF.toPoly], map_zero]
    exact hX0 (GF.rep_injOn pv ℓ X 0 hpv hX (Nat.two_pow_pos ℓ) (h.trans h0.symm))
  have h1 := FiniteField.pow_card_sub_one_eq_one (GF.rep pv X) hne
  rw [hcard] at h1
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  rw [← pow_succ, show 2 ^ ℓ - 2 + 1 = 2 ^ ℓ - 1 by omega, h1]

theorem size_lt_pow (ℓ : ℕ) (h : 1 ≤ ℓ) : Nat.size (2 ^ ℓ - 2) ≤ ℓ := by
  rw [Nat.size_le]; have := Nat.one_lt_two_pow (show ℓ ≠ 0 by omega); omega

/-- **The inverse** (`FieldCells` conjunct 4). -/
theorem finvS_spec (x z t p : Fin VV) (s ℓ pv : ℕ) (a : DS VV MM) (hs : s + 18 ≤ VV) (hx : Out s 18 x)
    (hz : Out s 18 z) (ht : Out s 18 t) (hp : Out s 18 p) (hzx : z ≠ x) (hzt : z ≠ t) (hzp : z ≠ p)
    (hta : a.env t = 2 ^ ℓ) (hpa : a.env p = pv) (hpv : GF.ModulusOk pv ℓ) (hℓ : 1 ≤ ℓ) (hW : ℓ + 1 ≤ C.Wd)
    (hX : a.env x < 2 ^ ℓ) :
    Hs C (finvS x z t p s) a (invCost ℓ)
      (fun b => b.env z < 2 ^ ℓ ∧ GF.rep pv (b.env z) = GF.rep pv (a.env x) ^ (2 ^ ℓ - 2) ∧
        (Irreducible (GF.toPoly pv) → a.env x ≠ 0 → GF.rep pv (b.env z) * GF.rep pv (a.env x) = 1) ∧
        b.sh = a.sh ∧ Fr a b (z :: blk s 18)) := by
  have hs' : s + 18 ≤ 128 := hs
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hWl : 2 ^ ℓ < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsz := size_lt_pow ℓ hℓ
  have hM : powCost ℓ (2 ^ ℓ - 2) ≤ ℓ * (2 * mulCost ℓ + 16) + 12 := by
    unfold powCost; have := Nat.mul_le_mul_right (2 * mulCost ℓ + 16) hsz; omega
  unfold finvS invCost
  have st : ∀ (b d : DS VV MM) (y : Fin VV) (v : ℕ), b = d.set y v →
      b.env y = v ∧ (∀ w, w ≠ y → b.env w = d.env w) ∧ b.sh = d.sh := by
    rintro b d y v rfl; exact ⟨DS.set_env_self _ _ _, fun w hw => DS.set_env_ne _ _ hw, rfl⟩
  refine hseq (t2 := ℓ * (2 * mulCost ℓ + 16) + 22) (hs_copy C (vr s) t a (by vne)) (fun e1 he1 => ?_) (by omega)
  obtain ⟨a1, f1, s1⟩ := st _ _ _ _ he1
  refine hseq (t2 := ℓ * (2 * mulCost ℓ + 16) + 20) (hs_zero C (vr (s + 1)) _) (fun e2 he2 => ?_) (by omega)
  obtain ⟨a2, f2, s2⟩ := st _ _ _ _ he2
  refine hseq (t2 := ℓ * (2 * mulCost ℓ + 16) + 18) (hs_inc C (vr (s + 1)) _ (by rw [a2]; omega))
    (fun e3 he3 => ?_) (by omega)
  obtain ⟨a3, f3, s3⟩ := st _ _ _ _ he3
  refine hseq (t2 := ℓ * (2 * mulCost ℓ + 16) + 16) (hs_inc C (vr (s + 1)) _ (by rw [a3, a2]; omega))
    (fun e4 he4 => ?_) (by omega)
  obtain ⟨a4, f4, s4⟩ := st _ _ _ _ he4
  have hv4 : e4.env (vr (s + 1)) = 2 := by rw [a4, a3, a2]
  have hu4 : e4.env (vr s) = 2 ^ ℓ := by rw [f4 _ (by vne), f3 _ (by vne), f2 _ (by vne), a1, hta]
  refine hseq (t2 := ℓ * (2 * mulCost ℓ + 16) + 14) (hs_sub C (vr s) (vr (s + 1)) _ (by vne)
    (by rw [hv4, hu4]; exact h2)) (fun e5 he5 => ?_) (by omega)
  obtain ⟨a5, f5, s5⟩ := st _ _ _ _ he5
  have rd5 : ∀ w, w ≠ vr s → w ≠ vr (s + 1) → e5.env w = a.env w := fun w h1 h2 => by
    rw [f5 _ h1, f4 _ h2, f3 _ h2, f2 _ h2, f1 _ h1]
  have hfr5 : Fr a e5 (z :: blk s 18) := fun w hw => by
    rw [List.mem_cons, not_or] at hw
    exact rd5 w (fun h => hw.2 (h ▸ vr_mem_blk0 (by norm_num) hs))
      (fun h => hw.2 (h ▸ vr_mem_blk (i := 1) (by norm_num) hs))
  have hE : e5.env (vr s) = 2 ^ ℓ - 2 := by rw [a5, hu4, hv4]
  have hx5 : e5.env x = a.env x := rd5 _ (by vne) (by vne)
  refine Hs.mono (fpowS_spec C x (vr s) z t p (s + 2) ℓ pv e5 (by omega) (out_sub hx (by omega) (by omega))
    (out_vr (by omega) (by omega)) (out_sub hz (by omega) (by omega)) (out_sub ht (by omega) (by omega))
    (out_sub hp (by omega) (by omega)) hzx (by vne) hzt hzp (by rw [rd5 _ (by vne) (by vne), hta])
    (by rw [rd5 _ (by vne) (by vne), hpa]) hpv hℓ hW (by rw [hx5]; exact hX)) (by rw [hE]; omega) ?_
  rintro b ⟨h1, h2, h3, h4⟩
  rw [hE, hx5] at h2
  refine ⟨h1, h2, fun hirr hx0 => by rw [h2]; exact inv_of_pow pv ℓ (a.env x) hpv hℓ hirr hX hx0,
    by rw [h3, s5, s4, s3, s2, s1], ?_⟩
  exact Fr.trans hfr5 (fr_blk h4 (by omega) (by omega) hs z (Or.inl rfl))

/-! ## The join -/

theorem fieldCosts (ℓ : ℕ) : xorCost ℓ ≤ 34 * (ℓ + 1) ∧ mulCost ℓ ≤ 100 * (ℓ + 1) ^ 2 ∧
    invCost ℓ ≤ 250 * (ℓ + 1) ^ 3 ∧ ∀ e, powCost ℓ e ≤ 250 * (Nat.size e + 1) * (ℓ + 1) ^ 2 := by
  have hm : mulCost ℓ = 44 * ℓ ^ 2 + 45 * ℓ + 14 := by unfold mulCost xorCost; ring
  refine ⟨by unfold xorCost; omega, by rw [hm]; nlinarith, ?_, fun e => ?_⟩
  · unfold invCost; rw [hm]; nlinarith [sq_nonneg ℓ, pow_two_nonneg ℓ]
  · unfold powCost; rw [hm]
    have h1 : Nat.size e * (2 * (44 * ℓ ^ 2 + 45 * ℓ + 14) + 16) ≤ Nat.size e * (250 * (ℓ + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : 12 ≤ 250 * (ℓ + 1) ^ 2 := by nlinarith
    nlinarith

/-- **Join FieldCells, proved.** -/
theorem fieldCells : FieldCells :=
  ⟨fun C x y z t s ℓ a hs hx hy hz ht hzx hzy hzt hta hW =>
      fxorS_spec C x y z t s ℓ a hs hx hy hz ht hzx hzy hzt hta hW,
    fun C x y z t p s ℓ pv a hs hx hy hz ht hp hzx hzy hzt hzp hta hpa hpv hW hX hY =>
      fmulS_spec C x y z t p s ℓ pv a hs hx hy hz ht hp hzx hzy hzt hzp hta hpa hpv hW hX hY,
    fun C x e z t p s ℓ pv a hs hx he hz ht hp hzx hze hzt hzp hta hpa hpv hℓ hW hX =>
      fpowS_spec C x e z t p s ℓ pv a hs hx he hz ht hp hzx hze hzt hzp hta hpa hpv hℓ hW hX,
    fun C x z t p s ℓ pv a hs hx hz ht hp hzx hzt hzp hta hpa hpv hℓ hW hX =>
      finvS_spec C x z t p s ℓ pv a hs hx hz ht hp hzx hzt hzp hta hpa hpv hℓ hW hX,
    fieldCosts⟩

end NearCubicGates.Adapters.ShortPCP.Machines
