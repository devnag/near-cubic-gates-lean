import Proof.Gates.Cells.Idx

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

def aw0 : Fin VV := ⟨100, by decide⟩
def a1 : Fin VV := ⟨101, by decide⟩
def a2 : Fin VV := ⟨102, by decide⟩

theorem size_succ (x : ℕ) (h : 0 < x) : Nat.size x = Nat.size (x / 2) + 1 := by
  have h1 : Nat.size x ≤ Nat.size (x / 2) + 1 := by
    rw [Nat.size_le]
    have := Nat.lt_size_self (x / 2)
    rw [Nat.pow_succ]; omega
  have h2 : Nat.size (x / 2) + 1 ≤ Nat.size x := by
    rcases Nat.eq_zero_or_pos (x / 2) with h0 | h0
    · rw [h0, Nat.size_zero]; exact Nat.size_pos.mpr h
    · have hp := Nat.size_pos.mpr h0
      have h4 : 2 ^ (Nat.size (x / 2) - 1) ≤ x / 2 := by
        by_contra hc
        have : Nat.size (x / 2) ≤ Nat.size (x / 2) - 1 := Nat.size_le.mpr (by omega)
        omega
      by_contra hc
      have h5 : x < 2 ^ Nat.size (x / 2) := Nat.size_le.mp (by omega)
      have : 2 ^ (Nat.size (x / 2) - 1) * 2 = 2 ^ Nat.size (x / 2) := by
        rw [← Nat.pow_succ]; congr 1; omega
      omega
  omega

/-- `d := Nat.size x` (scratch `aw0`). -/
def sizeP (x d : Fin VV) : St VV MM :=
  .seq (.op (.copy aw0 x)) (.seq (.op (.zero d)) (.loop (.lt vZ aw0) (.seq (.op (.half aw0)) (.op (.inc d)))))

theorem sizeP_spec (x d : Fin VV) (hx : x ≠ aw0) (hd : d ≠ aw0) (hdZ : d ≠ vZ) (a : DS VV MM) (hc : Cst a)
    (hW : Nat.size (a.env x) < 2 ^ C.Wd) :
    Hs C (sizeP x d) a (5 * Nat.size (a.env x) + 8) (fun b => b.env d = Nat.size (a.env x) ∧ b.sh = a.sh ∧
      Fr a b [aw0, d]) := by
  set v := a.env x
  refine Hs.mono (Hs.seq (t2 := 1 + (Nat.size v * (3 + 2) + 2) + 1) (hs_copy C aw0 x a (Ne.symm hx))
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  refine Hs.seq (t2 := Nat.size v * (3 + 2) + 2) (hs_zero C d _) (fun b2 hb2 => ?_)
  subst hb2
  let I : DS VV MM → Prop := fun e => e.env aw0 + 2 ^ 0 = e.env aw0 + 1 ∧ Nat.size (e.env aw0) + e.env d = Nat.size v ∧
    e.sh = a.sh ∧ Fr a e [aw0, d] ∧ e.env vZ = 0
  have h0 : I (((a.set aw0 (a.env x)).set d 0)) := by
    refine ⟨by simp, by vsimp [Ne.symm hd]; rfl, rfl, ?_, ?_⟩
    · exact Fr.trans (Fr.set a _ (by simp)) (Fr.set _ _ (by simp))
    · rw [DS.set_env_ne _ _ (Ne.symm hdZ), DS.set_env_ne _ _ (by decide)]; exact hc.z
  have hl := Hs.loopM (C := C) (c := .lt vZ aw0) (s := .seq (.op (.half aw0)) (.op (.inc d)))
    (show vZ ≠ aw0 by decide) I
    (fun e => Nat.size (e.env aw0)) 3 (fun e he hev => by
      obtain ⟨_, h2, h3, h4, h5⟩ := he
      simp only [Cnd.eval, h5, decide_eq_true_eq] at hev
      have hs := size_succ _ hev
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_half C aw0 e) (fun f hf => ?_)
      subst hf
      refine Hs.mono (hs_inc C d _ (by
        rw [DS.set_env_ne _ _ hd]; have : e.env d ≤ Nat.size v := by omega
        omega)) le_rfl ?_
      rintro g rfl
      have g1 : ((e.set aw0 (e.env aw0 / 2)).set d ((e.set aw0 (e.env aw0 / 2)).env d + 1)).env aw0 = e.env aw0 / 2 := by
        rw [DS.set_env_ne _ _ (Ne.symm hd), DS.set_env_self]
      have g2 : ((e.set aw0 (e.env aw0 / 2)).set d ((e.set aw0 (e.env aw0 / 2)).env d + 1)).env d = e.env d + 1 := by
        rw [DS.set_env_self, DS.set_env_ne _ _ hd]
      refine ⟨⟨by simp, ?_, by simp [h3], Fr.trans h4 (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp))), ?_⟩, ?_⟩
      · rw [g1, g2]; omega
      · rw [DS.set_env_ne _ _ (Ne.symm hdZ), DS.set_env_ne _ _ (by decide)]; exact h5
      · rw [g1]; omega) _ h0
  refine Hs.mono hl ?_ ?_
  · simp only [DS.set_env_self, DS.set_env_ne _ _ (Ne.symm hd)]; nlinarith
  · rintro e ⟨⟨_, h2, h3, h4, h5⟩, h6⟩
    simp only [Cnd.eval, h5, decide_eq_false_iff_not, not_lt, Nat.le_zero] at h6
    rw [h6, Nat.size_zero, zero_add] at h2
    exact ⟨h2, h3, h4⟩

/-- `d := b^e` (scratch `a1`, counter `c4`). -/
def powP (b e d : Fin VV) : St VV MM :=
  .seq (.op (.zero d)) (.seq (.op (.inc d)) (forS c4 e (.seq (.op (.mul d b a1)) (.op (.copy d a1)))))

theorem powP_spec (b e d : Fin VV) (hR : [b, e, d, a1, c4].Nodup) (a : DS VV MM)
    (hW : ∀ k ≤ a.env e, a.env b ^ k < 2 ^ C.Wd) (he : a.env e < 2 ^ C.Wd) (h1 : 1 < 2 ^ C.Wd) :
    Hs C (powP b e d) a (1 + (1 + ((a.env e) * (3 + 4) + 4) + 1) + 1)
      (fun r => r.env d = a.env b ^ a.env e ∧ r.sh = a.sh ∧ Fr a r [d, a1, c4]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨hbe, hbd, hba, hbc⟩, ⟨hed, hea, hec⟩, ⟨hda, hdc⟩, hac⟩ := hR
  set E := a.env e
  set B := a.env b
  refine Hs.seq (hs_zero C d a) (fun r1 hr1 => ?_)
  subst hr1
  refine Hs.seq (hs_inc C d _ (by rw [DS.set_env_self]; omega)) (fun r2 hr2 => ?_)
  subst hr2
  set s0 := (a.set d 0).set d ((a.set d 0).env d + 1) with hs0
  have s0d : s0.env d = 1 := by simp [s0]
  have s0b : s0.env b = B := by simp only [s0]; rw [DS.set_env_ne _ _ hbd, DS.set_env_ne _ _ hbd]
  have s0e : s0.env e = E := by simp only [s0]; rw [DS.set_env_ne _ _ hed, DS.set_env_ne _ _ hed]
  let I : ℕ → DS VV MM → Prop := fun k r => r.env d = B ^ k ∧ r.env b = B ∧ r.sh = a.sh ∧ Fr a r [d, a1, c4]
  have hl := forS_spec' (C := C) c4 e (Ne.symm hec) (.seq (.op (.mul d b a1)) (.op (.copy d a1))) s0 E he I 3
    (fun k r v ⟨i1, i2, i3, i4⟩ => ⟨by rw [DS.set_env_ne _ _ hdc]; exact i1,
      by rw [DS.set_env_ne _ _ hbc]; exact i2, by simp [i3], Fr.trans i4 (Fr.set r v (by simp))⟩)
    ⟨by rw [s0d, pow_zero], s0b, by simp [s0], Fr.trans (Fr.set a _ (by simp)) (Fr.set _ _ (by simp))⟩ s0e ?_
  · refine Hs.mono hl le_rfl ?_
    rintro r ⟨⟨i1, _, i3, i4⟩, _, _⟩
    exact ⟨i1, i3, i4⟩
  · intro k hk r ⟨i1, i2, i3, i4⟩ hrk hre
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_mul C d b a1 r (Ne.symm hbd) hda hba (by
      rw [i1, i2, ← pow_succ]; exact hW (k + 1) (by omega))) (fun r2 hr2 => ?_)
    subst hr2
    refine Hs.mono (hs_copy C d a1 _ hda) le_rfl ?_
    rintro r3 rfl
    refine ⟨⟨by rw [DS.set_env_self, DS.set_env_self, i1, i2, pow_succ], ?_, by simp [i3], ?_⟩, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ hbd, DS.set_env_ne _ _ hba, i2]
    · exact Fr.trans i4 (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))
    · rw [DS.set_env_ne _ _ (Ne.symm hdc), DS.set_env_ne _ _ (Ne.symm hac)]; exact hrk
    · rw [DS.set_env_ne _ _ hed, DS.set_env_ne _ _ hea, hre]

/-! ## Reading one record of the cell tables -/

open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem binary_getD : ∀ (W x k : ℕ), k < W → (binary W x).getD k false = x.testBit k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | W + 1, x, 0, _ => by
    simp only [binary, List.getD_cons_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  | W + 1, x, k + 1, h => by
    simp only [binary, List.getD_cons_succ]
    rw [binary_getD W (x / 2) k (by omega), Nat.testBit_succ]

theorem frame_getD_even (u : List Bool) (k : ℕ) : (RepairOrdinary.frame u).getD (2 * k) false = decide (k < u.length) := by
  induction u generalizing k with
  | nil => cases k <;> simp [RepairOrdinary.frame]
  | cons b u ih =>
    cases k with
    | zero => simp [RepairOrdinary.frame]
    | succ k =>
      have := ih k
      simp only [RepairOrdinary.frame, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.getD_cons_succ,
        List.length_cons] at this ⊢
      simpa using this

theorem frame_getD_odd (u : List Bool) (k : ℕ) : (RepairOrdinary.frame u).getD (2 * k + 1) false = u.getD k false := by
  induction u generalizing k with
  | nil => cases k <;> simp [RepairOrdinary.frame]
  | cons b u ih =>
    cases k with
    | zero => simp [RepairOrdinary.frame]
    | succ k =>
      have := ih k
      simp only [RepairOrdinary.frame, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, List.getD_cons_succ] at this ⊢
      exact this

theorem frame_length' (u : List Bool) : (RepairOrdinary.frame u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [RepairOrdinary.frame, ih]; ring

/-- Read one record `frame (binary W x)` at the entry cursor into `t3` (scratch `t0 t1`). -/
def rdRec : St VV MM :=
  .seq (.op (.zero t3)) (.seq (.op (.copy t1 v1)) (.seq (.op (.rdI t0))
    (.loop (.eq t0 v1) (.seq (.op (.rdI t0)) (.seq (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS)
      (.seq (.op (.shl t1)) (.op (.rdI t0))))))))

theorem rdRec_spec (a : DS VV MM) (hc : Cst a) (W x : ℕ) (rest : List Bool)
    (hcw : C.inp.drop a.ip = RepairOrdinary.frame (binary W x) ++ rest) (hx : x < 2 ^ W) (hW : W + 2 ≤ C.Wd) :
    Hs C rdRec a (12 * W + 12) (fun b => b.env t3 = x ∧ b.ip = a.ip + (2 * W + 1) ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) = (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Fr a b [t0, t1, t3, vJ]) := by
  have hflen : (RepairOrdinary.frame (binary W x)).length = 2 * W + 1 := by
    rw [frame_length', binary_length]
  have hrd : ∀ q, q < 2 * W + 1 → bitOf C.inp (a.ip + q) = ((RepairOrdinary.frame (binary W x)).getD q false).toNat :=
    fun q hq => bitOf_drop hcw q (by omega)
  have hlt : ∀ q, q < 2 * W + 1 → a.ip + q < C.inp.length := fun q hq => lt_of_drop hcw q (by omega)
  have hpw : 2 ^ (W + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hv1 := hc.one
  let I : ℕ → DS VV MM → Prop := fun k b => b.env t3 = x % 2 ^ k ∧ b.env t1 = 2 ^ k ∧
    b.env t0 = bitOf C.inp (a.ip + 2 * k) ∧ b.ip = a.ip + 2 * k + 1 ∧
    (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) = (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Fr a b [t0, t1, t3, vJ]
  have hloop : ∀ b, I 0 b → Hs C (.loop (.eq t0 v1) (.seq (.op (.rdI t0)) (.seq (.ite (.eq t0 v1) (.op (.add t3 t1))
      skipS) (.seq (.op (.shl t1)) (.op (.rdI t0)))))) b (W * (10 + 2) + 2) (I W) := by
    refine Hs.loopN (c := .eq t0 v1) (show t0 ≠ v1 by decide) I W 10 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hv1
      refine ⟨?_, ?_⟩
      · simp only [Cnd.eval, h3, bv1, decide_eq_true_eq]
        rw [hrd (2 * k) (by omega), frame_getD_even]; simp [hk]
      · refine Hs.mono (Hs.seq (t1 := 1) (t2 := 2 + (1 + 1 + 1) + 1) (hs_rdI C t0 b (by
          rw [h4]; have := hlt (2 * k + 1) (by omega); omega)) (fun d hd => ?_)) (by norm_num) (fun _ h => h)
        subst hd
        set d := { b.set t0 (bitOf C.inp b.ip) with ip := b.ip + 1 } with hd
        have hbit : d.env t0 = (x.testBit k).toNat := by
          show bitOf C.inp b.ip = _
          rw [h4, show a.ip + 2 * k + 1 = a.ip + (2 * k + 1) by ring, hrd _ (by omega), frame_getD_odd,
            binary_getD W x k hk]
        have dt3 : d.env t3 = x % 2 ^ k := by rw [hd]; vsimp [h1]
        have dt1 : d.env t1 = 2 ^ k := by rw [hd]; vsimp [h2]
        have dv1 : d.env v1 = 1 := by rw [hd]; vsimp [bv1]
        have hmod : x % 2 ^ (k + 1) = x % 2 ^ k + (x.testBit k).toNat * 2 ^ k := by
          rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
          rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with hm | hm <;> simp [hm] <;> ring
        have hpk : 2 ^ (k + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hk
        have hsum : x % 2 ^ k + 2 ^ k < 2 ^ C.Wd := by
          have := Nat.mod_lt x (show 0 < 2 ^ k by positivity)
          have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
          omega
        have step2 : Hs C (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS) d 2 (fun e => e.env t3 = x % 2 ^ (k + 1) ∧
            e.ip = d.ip ∧ (e.out, e.ram, e.rc, e.kin, e.kout, e.kc) = (d.out, d.ram, d.rc, d.kin, d.kout, d.kc) ∧
            Fr d e [t3, vJ]) := by
          refine Hs.ite (c := .eq t0 v1) (show t0 ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
          · have hb : x.testBit k = true := by
              revert he; simp only [Cnd.eval, hbit, dv1]; cases x.testBit k <;> simp
            refine Hs.mono (hs_add C t3 t1 d (by decide) (by rw [dt3, dt1]; exact hsum)) le_rfl ?_
            rintro e rfl
            exact ⟨by vsimp [dt3, dt1, hmod, hb], rfl, rfl, Fr.set d _ (by decide)⟩
          · have hb : x.testBit k = false := by
              revert he; simp only [Cnd.eval, hbit, dv1]; cases x.testBit k <;> simp
            refine Hs.mono (skip_spec d) le_rfl ?_
            rintro e rfl
            exact ⟨by vsimp [dt3, hmod, hb], rfl, rfl, Fr.set d _ (by decide)⟩
        refine Hs.seq step2 (fun e ⟨e1, e2, e3, e5⟩ => ?_)
        have et1 : e.env t1 = 2 ^ k := by rw [e5 t1 (by decide), dt1]
        have hsh : 2 * e.env t1 < 2 ^ C.Wd := by rw [et1, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]; omega
        refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (hs_shl C t1 e hsh) (fun f hf => ?_)) (by norm_num) (fun _ h => h)
        subst hf
        refine Hs.mono (hs_rdI C t0 _ (by
          show e.ip < _; rw [e2]; show b.ip + 1 < _; rw [h4]; have := hlt (2 * k + 2) (by omega); omega))
          le_rfl ?_
        rintro g rfl
        refine ⟨by vsimp [e1], by vsimp [et1]; ring, ?_, ?_, ?_, ?_⟩
        · show bitOf C.inp (e.ip) = _; rw [e2]; show bitOf C.inp (b.ip + 1) = _; rw [h4]; ring_nf
        · show e.ip + 1 = _; rw [e2]; show b.ip + 1 + 1 = _; rw [h4]; ring
        · simp only [Prod.mk.injEq] at e3 h5 ⊢
          simp [DS.set, e3, h5, hd]
        · refine Fr.trans h6 (Fr.trans ?_ (Fr.trans (Fr.weaken e5 (by decide)) (Fr.trans (Fr.set e _ (by decide))
            (Fr.set _ _ (by decide)))))
          intro y hy; rw [hd]; exact DS.set_env_ne b _ (fun h => hy (by rw [h]; decide))
    · intro b ⟨_, _, h3, _, _, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hv1
      simp only [Cnd.eval, h3, bv1, decide_eq_false_iff_not]
      rw [hrd (2 * W) (by omega), frame_getD_even]; simp
  -- the whole
  refine Hs.mono (Hs.seq (hs_zero C t3 a) (fun b1 hb1 => ?_)) (show 1 + (1 + (1 + (W * (10 + 2) + 2) + 1) + 1) + 1 ≤
    12 * W + 12 by omega) (fun _ h => h)
  subst hb1
  refine Hs.seq (hs_copy C t1 v1 _ (by decide)) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (hs_rdI C t0 _ (by simpa using hlt 0 (by omega))) (fun b3 hb3 => ?_)
  subst hb3
  refine Hs.mono (hloop _ ⟨by vsimp [Nat.mod_one], by vsimp [hv1], by vsimp [], by simp [DS.set], by simp [DS.set],
    ?_⟩) le_rfl ?_
  · refine Fr.trans (Fr.set a (x := t3) (T := [t0, t1, t3, vJ]) 0 (by decide))
      (Fr.trans (Fr.set (a.set t3 0) (x := t1) (T := [t0, t1, t3, vJ]) ((a.set t3 0).env v1) (by decide)) ?_)
    intro y hy; exact DS.set_env_ne _ _ (fun h => hy (by rw [h]; decide))
  · rintro r ⟨r1, _, _, r4, r5, r6⟩
    refine ⟨by rw [r1, Nat.mod_eq_of_lt hx], by rw [r4]; ring, r5, r6⟩

end NearCubicGates.Close.Cells
