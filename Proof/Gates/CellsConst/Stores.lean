import Proof.Gates.CellsConst.Prog

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

def prBody : St VV MM :=
  .seq (.op (.rdM sN kX)) (.seq (.op (.copy kP v1)) (.seq (CellTablesProg.powP kP kX kI kQ kT1) (.op (.add kAc kP))))

def prA : St VV MM :=
  .seq (.op (.copy kE gJ)) (.seq (.op (.inc kE)) (.seq (.op (.mul gRC kE kQ)) (.seq (.op (.zero kAc))
  (.seq (seekP sN vIPr) (forS kU vNP prBody)))))

def prT : List (Fin VV) := [kE, kQ, kAc, c0, vJ, kU, kX, kP, kI, kT1]

theorem getD_map_pow (Q : List ℕ) (m u : ℕ) (hu : u < Q.length) :
    (Q.map (· ^ m)).getD u 0 = (Q.getD u 0) ^ m := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getD_eq_getElem _ _ hu]; simp

theorem prA_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (L Q R : List ℕ) (i0 J Rr : ℕ) (hN : a.ram sN = L)
    (hrc : a.rc sN ≤ L.length) (hI : a.env vIPr = i0) (hQ : L.drop i0 = Q ++ R) (hnp : a.env vNP = Q.length)
    (hi0 : i0 ≤ L.length) (hJ : a.env gJ = J) (hR : a.env gRC = Rr) (hLW : L.length < 2 ^ C.Wd)
    (hm : Rr * (J + 1) + J + 1 < 2 ^ C.Wd) (hS : (Q.map (· ^ (Rr * (J + 1)))).sum < 2 ^ C.Wd) :
    Hs C prA a (6 * L.length + Q.length * (7 * (Rr * (J + 1)) + 14) + 30) (fun e =>
      e.env kAc = (Q.map (· ^ (Rr * (J + 1)))).sum ∧ e.env kQ = Rr * (J + 1) ∧ e.ram = a.ram ∧
      e.rc sN ≤ L.length ∧ AgN a e prT) := by
  have hiQ := le_of_drop hQ hi0
  obtain ⟨m, hmd⟩ : ∃ m, m = Rr * (J + 1) := ⟨_, rfl⟩
  rw [← hmd] at hm hS ⊢
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kE gJ a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 prT := Fr.weaken f1 (by decide)
  rw [hJ] at e1
  refine Hs.then (Hs.setx (hs_inc C kE b1 (by rw [e1]; omega))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  rw [e1] at e2
  refine Hs.then (Hs.setx (hs_mul C gRC kE kQ b2 (by decide) (by decide) (by decide)
    (by rw [e2, F2 gRC (by decide), hR, ← hmd]; omega))) (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  rw [e2, F2 gRC (by decide), hR, ← hmd] at e3
  refine Hs.then (Hs.setx (hs_zero C kAc b3)) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  have s4a : b4.sh = a.sh := by rw [s4, s3, s2, s1]
  simp only [DS.sh, Prod.mk.injEq] at s4a
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := s4a
  have b4I : b4.env vIPr = i0 := by rw [F4 vIPr (by decide), hI]
  refine Hs.then (seekP_spec sN vIPr (by decide) (by decide) b4 (by rw [b4I, q3, hN]; exact hi0)
    (by rw [b4I]; omega)) (fun b5 ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ n5 hn5 => ?_)
  have F5 := frA F4 r8 (by decide)
  rw [b4I] at r2
  have b5Q : b5.env kQ = m := by rw [r8 kQ (by decide), f4 kQ (by decide), e3]
  let I : ℕ → DS VV MM → Prop := fun u e => e.env kAc = ((Q.map (· ^ m)).take u).sum ∧ e.env kQ = m ∧
    e.ram = a.ram ∧ e.rc = Function.update a.rc sN (i0 + u) ∧ e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧
    e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e prT
  have h0 : I 0 b5 := ⟨by rw [r8 kAc (by decide), e4]; simp, b5Q, by rw [r1, q3], by rw [r2, q4, Nat.add_zero],
    by rw [r3, q1], by rw [r4, q2], by rw [r5, q5], by rw [r6, q6], by rw [r7, q7], F5⟩
  refine Hs.last (forS_spec' (C := C) kU vNP (by decide) _ b5 Q.length (by omega) I (7 * m + 10)
    (fun u e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i2, i3, i4, i5, i6, i7, i8, i9,
      Fr.trans i10 (Fr.set e v (by decide))⟩) h0
    (by rw [F5 vNP (by decide), hnp]) ?_) (fun b6 ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩, _, w6⟩ n6 hn6 => ?_)
  · intro u hu e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ heu hem
    have hrcu : e.rc sN = i0 + u := by rw [i4]; simp
    have hlt : e.rc sN < (e.ram sN).length := by rw [hrcu, i3, hN]; omega
    have hrd : (e.ram sN).getD (e.rc sN) 0 = Q.getD u 0 := by rw [i3, hN, hrcu]; exact getD_of_drop hQ u hu
    have hstep := sum_take_step (Q.map (· ^ m)) u (by simpa using hu)
    have hle := sum_take_le (Q.map (· ^ m)) (u + 1)
    rw [getD_map_pow Q m u hu] at hstep
    have hone : e.env v1 = 1 := by rw [i10 v1 (by decide)]; exact hc.one
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (7 * m + 4 + 1 + 1) + 1) (hs_rdM C sN kX e hlt)
      (fun f hf => ?_)) (by omega) (fun _ h => h)
    subst hf
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = (e.set kX ((e.ram sN).getD (e.rc sN) 0)).adv sN := ⟨_, rfl⟩
    rw [← hf0]
    have f0X : f0.env kX = Q.getD u 0 := by rw [hf0]; simp only [DS.adv]; rw [DS.set_env_self, hrd]
    have f0o : ∀ y, y ≠ kX → f0.env y = e.env y := fun y hy => by
      rw [hf0]; simp only [DS.adv]; rw [DS.set_env_ne _ _ hy]
    have f0sh : f0.ram = e.ram ∧ f0.rc = Function.update e.rc sN (e.rc sN + 1) ∧ f0.ip = e.ip ∧ f0.out = e.out ∧
        f0.kin = e.kin ∧ f0.kout = e.kout ∧ f0.kc = e.kc := by
      rw [hf0]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine Hs.seq (t1 := 1) (t2 := 7 * m + 4 + 1 + 1) (Hs.setx (hs_copy C kP v1 f0 (by decide)))
      (fun f1 ⟨g1, s1, r1⟩ => ?_)
    rw [f0o v1 (by decide), hone] at g1
    have f1X : f1.env kX = Q.getD u 0 := by rw [r1 kX (by decide), f0X]
    have f1Q : f1.env kQ = m := by rw [r1 kQ (by decide), f0o kQ (by decide), i2]
    have hqm : 1 * Q.getD u 0 ^ m < 2 ^ C.Wd := by rw [one_mul]; omega
    refine Hs.seq (t1 := 7 * m + 4) (t2 := 1) (CellTablesProg.powP_spec C kP kX kI kQ kT1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) f1 m 1 (Q.getD u 0) f1Q g1 f1X
      (by omega) hqm) (fun f2 ⟨g2, s2, r2⟩ => ?_)
    rw [one_mul] at g2
    have f2A : f2.env kAc = ((Q.map (· ^ m)).take u).sum := by
      rw [r2 kAc (by decide), r1 kAc (by decide), f0o kAc (by decide), i1]
    refine Hs.mono (Hs.setx (hs_add C kAc kP f2 (by decide) (by rw [f2A, g2]; omega))) le_rfl ?_
    rintro d ⟨g3, s3, r3⟩
    have dsh : d.sh = f0.sh := by rw [s3, s2, s1]
    simp only [DS.sh, Prod.mk.injEq] at dsh
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := dsh
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := f0sh
    have dfr : Fr f0 d [kP, kI, kT1, kAc] :=
      Fr.trans (Fr.weaken r1 (by decide)) (Fr.trans (Fr.weaken r2 (by decide)) (Fr.weaken r3 (by decide)))
    refine ⟨⟨by rw [g3, f2A, g2, hstep], by rw [dfr kQ (by decide), f0o kQ (by decide), i2], by rw [d3, h1, i3],
      ?_, by rw [d1, h3, i5], by rw [d2, h4, i6], by rw [d5, h5, i7], by rw [d6, h6, i8], by rw [d7, h7, i9], ?_⟩,
      ?_, ?_⟩
    · rw [d4, h2, i4]; funext m'; by_cases hm' : m' = sN
      · subst hm'; simp; omega
      · simp [Function.update_of_ne hm']
    · intro y hy
      have hyX : y ≠ kX := fun h => hy (by rw [h]; decide)
      rw [(Fr.weaken dfr (show ∀ z ∈ [kP, kI, kT1, kAc], z ∈ prT by decide)) y hy, f0o y hyX]
      exact i10 y hy
    · rw [dfr kU (by decide), f0o kU (by decide)]; exact heu
    · rw [dfr vNP (by decide), f0o vNP (by decide)]; exact hem
  · have hq4 : b4.rc sN = a.rc sN := by rw [q4]
    have hcost : Q.length * (7 * m + 10 + 4) = Q.length * (7 * m + 14) := by ring
    refine ⟨⟨by rw [i1, List.take_of_length_le (by simp)], i2, i3, ?_, ?_⟩, by omega⟩
    · rw [i4]; simp; omega
    · exact ⟨i3, fun m' hm => by rw [i4, Function.update_of_ne hm], i5, i6, i7, i8, i9, i10⟩

/-! ## Parts and the moment requests -/

def prB : St VV MM :=
  .seq (.ite (.eq gKd v2) (.op (.shl kAc)) skipS) (.seq (.op (.add kAc kQ)) (.op (.copy pR kAc)))

theorem prB_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (kd S m : ℕ) (hk : a.env gKd = kd) (hS : a.env kAc = S)
    (hm : a.env kQ = m) (hW : 2 * S + m < 2 ^ C.Wd) :
    Hs C prB a 8 (fun e => e.env pR = (if kd = 2 then 2 * S else S) + m ∧ e.sh = a.sh ∧
      Fr a e [kAc, vJ, pR]) := by
  have step1 : Hs C (.ite (.eq gKd v2) (.op (.shl kAc)) skipS) a 2 (fun e =>
      e.env kAc = (if kd = 2 then 2 * S else S) ∧ e.sh = a.sh ∧ Fr a e [kAc, vJ, pR]) := by
    refine Hs.ite (c := .eq gKd v2) (show gKd ≠ v2 by decide) (fun ht => ?_) (fun hf => ?_)
    · simp only [Cnd.eval, decide_eq_true_eq, hk, hc.two] at ht
      refine Hs.mono (Hs.setx (hs_shl C kAc a (by rw [hS]; omega))) le_rfl (fun e ⟨e1, s1, f1⟩ => ?_)
      exact ⟨by rw [e1, hS, if_pos ht], s1, Fr.weaken f1 (by decide)⟩
    · simp only [Cnd.eval, decide_eq_false_iff_not, hk, hc.two] at hf
      refine Hs.mono (Hs.setx (skip_spec a)) le_rfl (fun e ⟨e1, s1, f1⟩ => ?_)
      exact ⟨by rw [f1 kAc (by decide), hS, if_neg hf], s1, Fr.weaken f1 (by decide)⟩
  have hle : (if kd = 2 then 2 * S else S) ≤ 2 * S := by split_ifs <;> omega
  apply Hx.hs
  refine Hs.then step1 (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  refine Hs.then (Hs.setx (hs_add C kAc kQ b1 (by decide) (by rw [e1, f1 kQ (by decide), hm]; omega)))
    (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  rw [e1, f1 kQ (by decide), hm] at e2
  refine Hs.last (Hs.setx (hs_copy C pR kAc b2 (by decide))) (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  rw [e2] at e3
  exact ⟨⟨e3, by rw [s3, s2, s1], frA (frA f1 f2 (by decide)) f3 (by decide)⟩, by omega⟩

end NearCubicGates.Close.CellsConst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

/-- The words agree. -/
structure Sm (e f : DS VV MM) : Prop where
  ip : f.ip = e.ip
  out : f.out = e.out
  kin : f.kin = e.kin
  kout : f.kout = e.kout
  kc : f.kc = e.kc

theorem Sm.refl (e : DS VV MM) : Sm e e := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem Sm.trans {e f g : DS VV MM} (h1 : Sm e f) (h2 : Sm f g) : Sm e g :=
  ⟨h2.ip.trans h1.ip, h2.out.trans h1.out, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩
theorem Sm.setr {e f : DS VV MM} (h : Sm e f) (x : Fin VV) (v : ℕ) : Sm e (f.set x v) :=
  ⟨h.ip, h.out, h.kin, h.kout, h.kc⟩
theorem Sm.of_sh {e f : DS VV MM} (h : f.sh = e.sh) : Sm e f := by
  simp only [DS.sh, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem ram_of_sh {e f : DS VV MM} (h : f.sh = e.sh) : f.ram = e.ram ∧ f.rc = e.rc := by
  simp only [DS.sh, Prod.mk.injEq] at h
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem hs_rdM' (m : Fin MM) (x : Fin VV) (e : DS VV MM) (h : e.rc m < (e.ram m).length) :
    Hs C (.op (.rdM m x)) e 1 (fun f => f.env x = (e.ram m).getD (e.rc m) 0 ∧ f.ram = e.ram ∧
      f.rc = Function.update e.rc m (e.rc m + 1) ∧ Sm e f ∧ Fr e f [x]) :=
  Hs.mono (hs_rdM C m x e h) le_rfl (by
    rintro f rfl
    exact ⟨by simp [DS.adv], rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun y hy => by
      simp only [DS.adv]; exact DS.set_env_ne _ _ (fun h' => hy (by rw [h']; simp))⟩)

theorem hs_wrM' (m : Fin MM) (x : Fin VV) (e : DS VV MM) (h : e.rc m ≤ (e.ram m).length) :
    Hs C (.op (.wrM m x)) e 1 (fun f => f.ram = Function.update e.ram m (putAt (e.ram m) (e.rc m) (e.env x)) ∧
      f.rc = Function.update e.rc m (e.rc m + 1) ∧ Sm e f ∧ f.env = e.env) :=
  Hs.mono (hs_wrM C m x e h) le_rfl (by rintro f rfl; exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩)

theorem seekP' (m : Fin MM) (x : Fin VV) (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (e : DS VV MM)
    (hle : e.env x ≤ (e.ram m).length) (hW : e.env x < 2 ^ C.Wd) :
    Hs C (seekP m x) e (e.rc m + 5 * e.env x + 6) (fun f => f.ram = e.ram ∧
      f.rc = Function.update e.rc m (e.env x) ∧ Sm e f ∧ Fr e f [c0, vJ]) :=
  Hs.mono (seekP_spec m x hx0 hxJ e hle hW) le_rfl
    (fun _ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, ⟨h3, h4, h5, h6, h7⟩, h8⟩)

theorem putAt_end (l : List ℕ) (v : ℕ) : putAt l l.length v = l ++ [v] := by
  unfold putAt; simp

theorem putAt_end' (l : List ℕ) (i v : ℕ) (h : l.length = i) : putAt l i v = l ++ [v] := by
  subst h; exact putAt_end l v

/-! ## `sP`: the tail products -/

def tIn : St VV MM := .seq (.op (.rdM sN kX)) (.seq (.op (.mul kP kX kT1)) (.op (.copy kP kT1)))

/-- The tail product of the factor list `F` from `j`. -/
def tProd (F : List ℕ) (j : ℕ) : ℕ := ∏ t ∈ Finset.Ico j F.length, F.getD t 0

theorem tIn_loop (e : DS VV MM) (L F R : List ℕ) (g j N : ℕ) (hN : e.ram sN = L) (hF : L.drop (g + 1) = F ++ R)
    (hg1 : g + 1 ≤ L.length) (hjN : j + N = F.length) (hrc : e.rc sN = g + 1 + j) (hP : e.env kP = 1)
    (hNv : e.env kN = N) (hNW : N < 2 ^ C.Wd)
    (hprod : ∀ u, j ≤ u → u ≤ F.length → ∏ t ∈ Finset.Ico j u, F.getD t 0 < 2 ^ C.Wd) :
    Hs C (forS kU kN tIn) e (N * (5 + 4) + 4) (fun f => f.env kP = tProd F j ∧ f.ram = e.ram ∧
      f.rc = Function.update e.rc sN (g + 1 + j + N) ∧ Sm e f ∧ Fr e f [kU, kX, kT1, kP] ∧ f.env kN = N) := by
  have hgF := le_of_drop hF hg1
  let I : ℕ → DS VV MM → Prop := fun u f => f.env kP = ∏ t ∈ Finset.Ico j (j + u), F.getD t 0 ∧ f.ram = e.ram ∧
    f.rc = Function.update e.rc sN (g + 1 + j + u) ∧ Sm e f ∧ Fr e f [kU, kX, kT1, kP]
  have h0 : I 0 e := ⟨by rw [hP]; simp, rfl, by rw [← hrc]; simp, Sm.refl e, Fr.refl _ _⟩
  refine Hs.mono (forS_spec' (C := C) kU kN (by decide) tIn e N hNW I 5
    (fun u f v ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2, i3, i4.setr kU v,
      Fr.trans i5 (Fr.set f v (by decide))⟩) h0 hNv ?_) le_rfl ?_
  · intro u hu f ⟨i1, i2, i3, i4, i5⟩ hfu hfN
    have hrcu : f.rc sN = g + 1 + j + u := by rw [i3]; simp
    have hlt : f.rc sN < (f.ram sN).length := by rw [hrcu, i2, hN]; omega
    have hrd : (f.ram sN).getD (f.rc sN) 0 = F.getD (j + u) 0 := by
      rw [i2, hN, hrcu, show g + 1 + j + u = g + 1 + (j + u) by ring]; exact getD_of_drop hF (j + u) (by omega)
    have hsucc : ∏ t ∈ Finset.Ico j (j + (u + 1)), F.getD t 0 =
        (∏ t ∈ Finset.Ico j (j + u), F.getD t 0) * F.getD (j + u) 0 := by
      rw [show j + (u + 1) = j + u + 1 by ring, Finset.prod_Ico_succ_top (by omega)]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + 1 + 1) (hs_rdM' sN kX f hlt) (fun f1 ⟨g1, r1, c1, m1, q1⟩ => ?_))
      (by norm_num) (fun _ h => h)
    rw [hrd] at g1
    have f1P : f1.env kP = ∏ t ∈ Finset.Ico j (j + u), F.getD t 0 := by rw [q1 kP (by decide), i1]
    refine Hs.seq (t1 := 1) (t2 := 1) (Hs.setx (hs_mul C kP kX kT1 f1 (by decide) (by decide) (by decide)
      (by rw [f1P, g1, ← hsucc]; exact hprod _ (by omega) (by omega)))) (fun f2 ⟨g2, s2, r2⟩ => ?_)
    rw [f1P, g1, ← hsucc] at g2
    refine Hs.mono (Hs.setx (hs_copy C kP kT1 f2 (by decide))) le_rfl (fun f3 ⟨g3, s3, r3⟩ => ?_)
    have s31 : f3.sh = f1.sh := by rw [s3, s2]
    obtain ⟨w1, w2⟩ := ram_of_sh s31
    refine ⟨⟨by rw [g3, g2], by rw [w1, r1, i2], ?_, Sm.trans i4 (Sm.trans m1 (Sm.of_sh s31)),
      Fr.trans i5 (Fr.trans (Fr.weaken q1 (by decide)) (Fr.trans (Fr.weaken r2 (by decide))
      (Fr.weaken r3 (by decide))))⟩, ?_, ?_⟩
    · rw [w2, c1, i3]; funext m; by_cases hm : m = sN
      · subst hm; simp; omega
      · simp [Function.update_of_ne hm]
    · rw [r3 kU (by decide), r2 kU (by decide), q1 kU (by decide)]; exact hfu
    · rw [r3 kN (by decide), r2 kN (by decide), q1 kN (by decide)]; exact hfN
  · rintro f ⟨⟨i1, i2, i3, i4, i5⟩, _, w⟩
    exact ⟨by rw [i1, hjN]; rfl, i2, i3, i4, i5, w⟩

def tBody : St VV MM :=
  .seq (.op (.copy kPos gFS)) (.seq (.op (.inc kPos)) (.seq (.op (.add kPos kJ)) (.seq (seekP sN kPos)
  (.seq (.op (.copy kN wNF)) (.seq (.op (.sub kN kJ)) (.seq (.op (.copy kP v1))
  (.seq (forS kU kN tIn) (.op (.wrM sP kP)))))))))

def tailSP : St VV MM := forS kJ gJ tBody

def tT : List (Fin VV) := [kPos, c0, vJ, kN, kP, kU, kX, kT1, kJ]

/-- The invariant of the outer loop of `tailSP`. -/
structure TI (a : DS VV MM) (L F : List ℕ) (j : ℕ) (e : DS VV MM) : Prop where
  pv : e.ram sP = (List.range j).map (tProd F)
  pc : e.rc sP = j
  rm : ∀ m, m ≠ sP → e.ram m = a.ram m
  rcs : ∀ m, m ≠ sN → m ≠ sP → e.rc m = a.rc m
  rN : e.rc sN ≤ L.length
  sm : Sm a e
  fr : Fr a e tT

theorem tBody_spec (a : DS VV MM) (hc : Cst a) (L F R : List ℕ) (g j : ℕ) (hN : a.ram sN = L)
    (hF : L.drop (g + 1) = F ++ R) (hg1 : g + 1 ≤ L.length) (hj : j ≤ F.length) (hgv : a.env gFS = g)
    (hnf : a.env wNF = F.length) (hLW : L.length < 2 ^ C.Wd)
    (hprod : ∀ j u, j ≤ u → u ≤ F.length → ∏ t ∈ Finset.Ico j u, F.getD t 0 < 2 ^ C.Wd)
    (e : DS VV MM) (hI : TI a L F j e) (hej : e.env kJ = j) :
    Hs C tBody e (6 * L.length + 9 * F.length + 30) (fun f => TI a L F (j + 1) f ∧ f.env kJ = j ∧
      ∀ y, y ∉ tT → f.env y = e.env y) := by
  have hgF := le_of_drop hF hg1
  have esN : e.ram sN = L := by rw [hI.rm sN (by decide), hN]
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kPos gFS e (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  rw [hI.fr gFS (by decide), hgv] at e1
  refine Hs.then (Hs.setx (hs_inc C kPos b1 (by rw [e1]; omega))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  rw [e1] at e2
  have b2J : b2.env kJ = j := by rw [f2 kJ (by decide), f1 kJ (by decide), hej]
  refine Hs.then (Hs.setx (hs_add C kPos kJ b2 (by decide) (by rw [e2, b2J]; omega)))
    (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  rw [e2, b2J] at e3
  have s3e : b3.sh = e.sh := by rw [s3, s2, s1]
  obtain ⟨w3, w3c⟩ := ram_of_sh s3e
  refine Hs.then (seekP' sN kPos (by decide) (by decide) b3 (by rw [e3, w3, esN]; omega) (by rw [e3]; omega))
    (fun b4 ⟨r4, c4, m4, q4⟩ n4 hn4 => ?_)
  rw [e3] at c4
  have G3 : Fr e b3 [kPos] := Fr.trans (Fr.trans f1 f2) f3
  have G4 : Fr e b4 [kPos, c0, vJ] := Fr.trans (Fr.weaken G3 (by decide)) (Fr.weaken q4 (by decide))
  refine Hs.then (Hs.setx (hs_copy C kN wNF b4 (by decide))) (fun b5 ⟨e5, s5, f5⟩ n5 hn5 => ?_)
  rw [G4 wNF (by decide), hI.fr wNF (by decide), hnf] at e5
  refine Hs.then (Hs.setx (hs_sub C kN kJ b5 (by decide)
    (by rw [e5, f5 kJ (by decide), G4 kJ (by decide), hej]; exact hj))) (fun b6 ⟨e6, s6, f6⟩ n6 hn6 => ?_)
  rw [e5, f5 kJ (by decide), G4 kJ (by decide), hej] at e6
  refine Hs.then (Hs.setx (hs_copy C kP v1 b6 (by decide))) (fun b7 ⟨e7, s7, f7⟩ n7 hn7 => ?_)
  rw [f6 v1 (by decide), f5 v1 (by decide), G4 v1 (by decide), hI.fr v1 (by decide), hc.one] at e7
  have s74 : b7.sh = b4.sh := by rw [s7, s6, s5]
  obtain ⟨w7, w7c⟩ := ram_of_sh s74
  have G7 : Fr b4 b7 [kN, kP] := Fr.trans (Fr.trans (Fr.weaken f5 (by decide)) (Fr.weaken f6 (by decide)))
    (Fr.weaken f7 (by decide))
  refine Hs.then (tIn_loop b7 L F R g j (F.length - j) (by rw [w7, r4, w3, esN]) hF hg1 (by omega)
    (by rw [w7c, c4]; simp) e7 (by rw [f7 kN (by decide), e6]) (by omega) (hprod j))
    (fun b8 ⟨v8, r8, c8, m8, q8, _⟩ n8 hn8 => ?_)
  have rcP8 : b8.rc sP = j := by
    rw [c8, Function.update_of_ne (by decide), w7c, c4, Function.update_of_ne (by decide), w3c, hI.pc]
  have ramP8 : b8.ram sP = (List.range j).map (tProd F) := by rw [r8, w7, r4, w3, hI.pv]
  refine Hs.last (hs_wrM' sP kP b8 (by rw [rcP8, ramP8]; simp)) (fun b9 ⟨r9, c9, m9, q9⟩ n9 hn9 => ?_)
  have Ge : Fr e b9 tT := Fr.trans (Fr.weaken G4 (by decide)) (Fr.trans (Fr.weaken G7 (by decide))
    (Fr.trans (Fr.weaken q8 (by decide)) (fun y _ => by rw [q9])))
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, Sm.trans hI.sm (Sm.trans (Sm.of_sh s3e) (Sm.trans m4 (Sm.trans (Sm.of_sh s74)
    (Sm.trans m8 m9)))), Fr.trans hI.fr Ge⟩, ?_, fun y hy => Ge y hy⟩, ?_⟩
  · rw [r9, Function.update_self, rcP8, ramP8, v8, putAt_end' _ _ _ (by simp)]
    simp [List.range_succ]
  · rw [c9, Function.update_self, rcP8]
  · intro m hm
    rw [r9, Function.update_of_ne hm, r8, w7, r4, w3]; exact hI.rm m hm
  · intro m hm1 hm2
    rw [c9, Function.update_of_ne hm2, c8, Function.update_of_ne hm1, w7c, c4, Function.update_of_ne hm1, w3c]
    exact hI.rcs m hm1 hm2
  · rw [c9, Function.update_of_ne (by decide), c8]; simp; omega
  · rw [q9, q8 kJ (by decide), G7 kJ (by decide), G4 kJ (by decide), hej]
  · have : b3.rc sN = e.rc sN := by rw [w3c]
    have := hI.rN
    omega

theorem tailSP_spec (a : DS VV MM) (hc : Cst a) (L F R : List ℕ) (g J : ℕ) (hN : a.ram sN = L)
    (hrc : a.rc sN ≤ L.length) (hF : L.drop (g + 1) = F ++ R) (hg1 : g + 1 ≤ L.length) (hgv : a.env gFS = g)
    (hnf : a.env wNF = F.length) (hJv : a.env gJ = J) (hJF : J = F.length + 1) (hP0 : a.ram sP = [])
    (hPc : a.rc sP = 0) (hLW : L.length < 2 ^ C.Wd) (hJW : J < 2 ^ C.Wd)
    (hprod : ∀ j u, j ≤ u → u ≤ F.length → ∏ t ∈ Finset.Ico j u, F.getD t 0 < 2 ^ C.Wd) :
    Hs C tailSP a (J * (6 * L.length + 9 * F.length + 34) + 4) (fun f =>
      f.ram sP = (List.range J).map (tProd F) ∧ (∀ m, m ≠ sP → f.ram m = a.ram m) ∧
      (∀ m, m ≠ sN → m ≠ sP → f.rc m = a.rc m) ∧ f.rc sN ≤ L.length ∧ Sm a f ∧ Fr a f tT) := by
  have h0 : TI a L F 0 a := ⟨by rw [hP0]; simp, hPc, fun _ _ => rfl, fun _ _ _ => rfl, hrc, Sm.refl a,
    Fr.refl _ _⟩
  refine Hs.mono (forS_spec' (C := C) kJ gJ (by decide) tBody a J hJW (TI a L F) (6 * L.length + 9 * F.length + 30)
    (fun k e v hI => ⟨hI.pv, hI.pc, hI.rm, hI.rcs, hI.rN, hI.sm.setr kJ v, Fr.trans hI.fr (Fr.set e v (by decide))⟩) h0
    hJv ?_) (by rw [show 6 * L.length + 9 * F.length + 30 + 4 = 6 * L.length + 9 * F.length + 34 by ring])
    (fun f ⟨hI, _, _⟩ => ⟨hI.pv, hI.rm, hI.rcs, hI.rN, hI.sm, hI.fr⟩)
  intro j hj e hI hej hem
  refine Hs.mono (tBody_spec a hc L F R g j hN hF hg1 (by omega) hgv hnf hLW hprod e hI hej) le_rfl ?_
  rintro f ⟨hf, hfj, hfo⟩
  exact ⟨hf, hfj, by rw [hfo gJ (by decide)]; exact hem⟩

/-! ## `sR`: the membership vector of `I` -/

theorem mem_take_succ (Q : List ℕ) (u j : ℕ) (hu : u < Q.length) :
    j ∈ Q.take (u + 1) ↔ j ∈ Q.take u ∨ j = Q.getD u 0 := by
  rw [List.take_add_one, List.mem_append, List.getElem?_eq_getElem hu, List.getD_eq_getElem _ _ hu]; simp

def mIn : St VV MM := .seq (.op (.rdM sN kX)) (.ite (.eq kX kJ) (.op (.copy kF v1)) skipS)

theorem mIn_loop (e : DS VV MM) (hc1 : e.env v1 = 1) (L Q R : List ℕ) (p0 j : ℕ) (hN : e.ram sN = L)
    (hQ : L.drop p0 = Q ++ R) (hp0 : p0 ≤ L.length) (hrc : e.rc sN = p0) (hF : e.env kF = 0) (hJ : e.env kJ = j)
    (hQv : e.env wCo = Q.length) (hQW : Q.length < 2 ^ C.Wd) :
    Hs C (forS kU wCo mIn) e (Q.length * (4 + 4) + 4) (fun f => f.env kF = (if j ∈ Q then 1 else 0) ∧
      f.ram = e.ram ∧ f.rc = Function.update e.rc sN (p0 + Q.length) ∧ Sm e f ∧ Fr e f [kU, kX, kF, vJ]) := by
  have hpQ := le_of_drop hQ hp0
  let I : ℕ → DS VV MM → Prop := fun u f => f.env kF = (if j ∈ Q.take u then 1 else 0) ∧ f.ram = e.ram ∧
    f.rc = Function.update e.rc sN (p0 + u) ∧ Sm e f ∧ Fr e f [kU, kX, kF, vJ]
  have h0 : I 0 e := ⟨by rw [hF]; simp, rfl, by rw [← hrc]; simp, Sm.refl e, Fr.refl _ _⟩
  refine Hs.mono (forS_spec' (C := C) kU wCo (by decide) mIn e Q.length hQW I 4
    (fun u f v ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2, i3, i4.setr kU v,
      Fr.trans i5 (Fr.set f v (by decide))⟩) h0 hQv ?_) le_rfl ?_
  · intro u hu f ⟨i1, i2, i3, i4, i5⟩ hfu hfQ
    have hrcu : f.rc sN = p0 + u := by rw [i3]; simp
    have hlt : f.rc sN < (f.ram sN).length := by rw [hrcu, i2, hN]; omega
    have hrd : (f.ram sN).getD (f.rc sN) 0 = Q.getD u 0 := by rw [i2, hN, hrcu]; exact getD_of_drop hQ u hu
    have hmem := mem_take_succ Q u j hu
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + 1) (hs_rdM' sN kX f hlt) (fun f1 ⟨g1, r1, c1, m1, q1⟩ => ?_))
      (by norm_num) (fun _ h => h)
    rw [hrd] at g1
    have f1J : f1.env kJ = j := by rw [q1 kJ (by decide), i5 kJ (by decide), hJ]
    have f1F : f1.env kF = (if j ∈ Q.take u then 1 else 0) := by rw [q1 kF (by decide), i1]
    have hrc1 : f1.rc = Function.update e.rc sN (p0 + (u + 1)) := by
      rw [c1, i3]; funext m; by_cases hm : m = sN
      · subst hm; simp; omega
      · simp [Function.update_of_ne hm]
    refine Hs.ite (c := .eq kX kJ) (show kX ≠ kJ by decide) (fun ht => ?_) (fun hf => ?_)
    · simp only [Cnd.eval, decide_eq_true_eq, g1, f1J] at ht
      refine Hs.mono (Hs.setx (hs_copy C kF v1 f1 (by decide))) le_rfl (fun f2 ⟨g2, s2, r2⟩ => ?_)
      obtain ⟨w1, w2⟩ := ram_of_sh s2
      refine ⟨⟨?_, by rw [w1, r1, i2], by rw [w2, hrc1], Sm.trans i4 (Sm.trans m1 (Sm.of_sh s2)),
        Fr.trans i5 (Fr.trans (Fr.weaken q1 (by decide)) (Fr.weaken r2 (by decide)))⟩, ?_, ?_⟩
      · rw [g2, q1 v1 (by decide), i5 v1 (by decide), hc1, if_pos (hmem.mpr (Or.inr ht.symm))]
      · rw [r2 kU (by decide), q1 kU (by decide)]; exact hfu
      · rw [r2 wCo (by decide), q1 wCo (by decide)]; exact hfQ
    · simp only [Cnd.eval, decide_eq_false_iff_not, g1, f1J] at hf
      refine Hs.mono (Hs.setx (skip_spec f1)) le_rfl (fun f2 ⟨g2, s2, r2⟩ => ?_)
      obtain ⟨w1, w2⟩ := ram_of_sh s2
      have hiff : (j ∈ Q.take (u + 1)) ↔ j ∈ Q.take u := by
        rw [hmem]; exact ⟨fun h => h.resolve_right (fun h' => hf h'.symm), Or.inl⟩
      refine ⟨⟨?_, by rw [w1, r1, i2], by rw [w2, hrc1], Sm.trans i4 (Sm.trans m1 (Sm.of_sh s2)),
        Fr.trans i5 (Fr.trans (Fr.weaken q1 (by decide)) (Fr.weaken r2 (by decide)))⟩, ?_, ?_⟩
      · rw [r2 kF (by decide), f1F]; simp only [hiff]
      · rw [r2 kU (by decide), q1 kU (by decide)]; exact hfu
      · rw [r2 wCo (by decide), q1 wCo (by decide)]; exact hfQ
  · rintro f ⟨⟨i1, i2, i3, i4, i5⟩, _, _⟩
    exact ⟨by rw [i1, List.take_of_length_le le_rfl], i2, i3, i4, i5⟩

def mBody : St VV MM :=
  .seq (.op (.zero kF)) (.seq (seekP sN kPos) (.seq (forS kU wCo mIn) (.op (.wrM sR kF))))

def membP : St VV MM := .seq (.op (.copy kPos gWS)) (.seq (.op (.sub kPos wCo)) (forS kJ gN mBody))

def mT : List (Fin VV) := [kPos, kF, c0, vJ, kU, kX, kJ]

/-- The membership vector of the list `Q` on `0 … j−1`. -/
def mVec (Q : List ℕ) (j : ℕ) : List ℕ := (List.range j).map fun i => if i ∈ Q then 1 else 0

/-- The invariant of the outer loop of `membP`. -/
structure MI (a : DS VV MM) (L Q : List ℕ) (p0 j : ℕ) (e : DS VV MM) : Prop where
  rv : e.ram sR = mVec Q j
  rcv : e.rc sR = j
  rm : ∀ m, m ≠ sR → e.ram m = a.ram m
  rcs : ∀ m, m ≠ sN → m ≠ sR → e.rc m = a.rc m
  rN : e.rc sN ≤ L.length
  pos : e.env kPos = p0
  sm : Sm a e
  fr : Fr a e mT

theorem mBody_spec (a : DS VV MM) (hc : Cst a) (L Q R : List ℕ) (p0 j : ℕ) (hN : a.ram sN = L)
    (hQ : L.drop p0 = Q ++ R) (hp0 : p0 ≤ L.length) (hQv : a.env wCo = Q.length) (hLW : L.length < 2 ^ C.Wd)
    (e : DS VV MM) (hI : MI a L Q p0 j e) (hej : e.env kJ = j) :
    Hs C mBody e (6 * L.length + 8 * Q.length + 15) (fun f => MI a L Q p0 (j + 1) f ∧ f.env kJ = j ∧
      ∀ y, y ∉ mT → f.env y = e.env y) := by
  have hpQ := le_of_drop hQ hp0
  have esN : e.ram sN = L := by rw [hI.rm sN (by decide), hN]
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_zero C kF e)) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  obtain ⟨w1, w1c⟩ := ram_of_sh s1
  have b1P : b1.env kPos = p0 := by rw [f1 kPos (by decide), hI.pos]
  refine Hs.then (seekP' sN kPos (by decide) (by decide) b1 (by rw [b1P, w1, esN]; exact hp0)
    (by rw [b1P]; omega)) (fun b2 ⟨r2, c2, m2, q2⟩ n2 hn2 => ?_)
  rw [b1P] at c2
  have G2 : Fr e b2 [kF, c0, vJ] := Fr.trans (Fr.weaken f1 (by decide)) (Fr.weaken q2 (by decide))
  refine Hs.then (mIn_loop b2 (by rw [G2 v1 (by decide), hI.fr v1 (by decide), hc.one]) L Q R p0 j
    (by rw [r2, w1, esN]) hQ hp0 (by rw [c2]; simp) (by rw [q2 kF (by decide), e1])
    (by rw [G2 kJ (by decide), hej]) (by rw [G2 wCo (by decide), hI.fr wCo (by decide), hQv]) (by omega))
    (fun b3 ⟨v3, r3, c3, m3, q3⟩ n3 hn3 => ?_)
  have rcR3 : b3.rc sR = j := by
    rw [c3, Function.update_of_ne (by decide), c2, Function.update_of_ne (by decide), w1c, hI.rcv]
  have ramR3 : b3.ram sR = mVec Q j := by rw [r3, r2, w1, hI.rv]
  refine Hs.last (hs_wrM' sR kF b3 (by rw [rcR3, ramR3]; simp [mVec])) (fun b4 ⟨r4, c4, m4, q4⟩ n4 hn4 => ?_)
  have Ge : Fr e b4 mT := Fr.trans (Fr.weaken G2 (by decide)) (Fr.trans (Fr.weaken q3 (by decide))
    (fun y _ => by rw [q4]))
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Sm.trans hI.sm (Sm.trans (Sm.of_sh s1) (Sm.trans m2 (Sm.trans m3 m4))),
    Fr.trans hI.fr Ge⟩, by rw [q4, q3 kJ (by decide), G2 kJ (by decide), hej], fun y hy => Ge y hy⟩, ?_⟩
  · rw [r4, Function.update_self, rcR3, ramR3, v3, putAt_end' _ _ _ (by simp [mVec])]
    simp [mVec, List.range_succ]
  · rw [c4, Function.update_self, rcR3]
  · intro m hm
    rw [r4, Function.update_of_ne hm, r3, r2, w1]; exact hI.rm m hm
  · intro m hm1 hm2
    rw [c4, Function.update_of_ne hm2, c3, Function.update_of_ne hm1, c2, Function.update_of_ne hm1, w1c]
    exact hI.rcs m hm1 hm2
  · rw [c4, Function.update_of_ne (by decide), c3]; simp; omega
  · rw [q4, q3 kPos (by decide), G2 kPos (by decide), hI.pos]
  · have : b1.rc sN = e.rc sN := by rw [w1c]
    have := hI.rN
    omega

theorem membP_spec (a : DS VV MM) (hc : Cst a) (L Q R : List ℕ) (s0 n : ℕ) (hN : a.ram sN = L)
    (hrc : a.rc sN ≤ L.length) (hs : a.env gWS = s0) (hQv : a.env wCo = Q.length) (hQs : Q.length ≤ s0)
    (hQ : L.drop (s0 - Q.length) = Q ++ R) (hs0 : s0 ≤ L.length) (hn : a.env gN = n) (hR0 : a.ram sR = [])
    (hRc : a.rc sR = 0) (hLW : L.length < 2 ^ C.Wd) (hnW : n < 2 ^ C.Wd) :
    Hs C membP a (n * (6 * L.length + 8 * Q.length + 19) + 10) (fun f =>
      f.ram sR = mVec Q n ∧ (∀ m, m ≠ sR → f.ram m = a.ram m) ∧ (∀ m, m ≠ sN → m ≠ sR → f.rc m = a.rc m) ∧
      f.rc sN ≤ L.length ∧ Sm a f ∧ Fr a f mT) := by
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kPos gWS a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  rw [hs] at e1
  refine Hs.then (Hs.setx (hs_sub C kPos wCo b1 (by decide) (by rw [e1, f1 wCo (by decide), hQv]; exact hQs)))
    (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  rw [e1, f1 wCo (by decide), hQv] at e2
  have s2a : b2.sh = a.sh := by rw [s2, s1]
  obtain ⟨w2, w2c⟩ := ram_of_sh s2a
  have F2 : Fr a b2 mT := Fr.trans (Fr.weaken f1 (by decide)) (Fr.weaken f2 (by decide))
  have h0 : MI a L Q (s0 - Q.length) 0 b2 := ⟨by rw [w2, hR0]; rfl, by rw [w2c, hRc], fun m _ => by rw [w2],
    fun m _ _ => by rw [w2c], by rw [w2c]; exact hrc, e2, Sm.of_sh s2a, F2⟩
  refine Hs.last (forS_spec' (C := C) kJ gN (by decide) mBody b2 n hnW (MI a L Q (s0 - Q.length))
    (6 * L.length + 8 * Q.length + 15) (fun k e v hI => ⟨hI.rv, hI.rcv, hI.rm, hI.rcs, hI.rN,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hI.pos, hI.sm.setr kJ v, Fr.trans hI.fr (Fr.set e v (by decide))⟩)
    h0 (by rw [F2 gN (by decide), hn]) ?_) (fun b3 ⟨hI, _, _⟩ n3 hn3 => ?_)
  · intro j hj e hI hej hem
    refine Hs.mono (mBody_spec a hc L Q R (s0 - Q.length) j hN hQ (by omega) hQv hLW e hI hej) le_rfl ?_
    rintro f ⟨hf, hfj, hfo⟩
    exact ⟨hf, hfj, by rw [hfo gN (by decide)]; exact hem⟩
  · have : n * (6 * L.length + 8 * Q.length + 15 + 4) = n * (6 * L.length + 8 * Q.length + 19) := by ring
    exact ⟨⟨hI.rv, hI.rm, hI.rcs, hI.rN, hI.sm, hI.fr⟩, by omega⟩

end NearCubicGates.Close.CellsConst

