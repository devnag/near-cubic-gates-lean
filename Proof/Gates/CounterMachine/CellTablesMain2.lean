import Proof.Gates.CounterMachine.CellTablesMain
import Proof.Gates.Cells.Run

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN gKd gJ gRC gN gS gJR loadP loadCost LS loadP_spec Loaded)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem cstInit_spec (C : Ctx) (hW : 3 ≤ C.Wd) : Hs C cstInit (a0 : DS VV MM) 5 (fun e => Cst e ∧
    e.sh = (a0 : DS VV MM).sh ∧ Fr a0 e [v1, v2]) := by
  have h4 : 4 < 2 ^ C.Wd := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  unfold cstInit
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_inc C v1 a0 (by simp [a0]; omega)) (fun b1 hb1 => ?_); subst hb1
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C v2 _ (by vsimp [a0]; omega)) (fun b2 hb2 => ?_); subst hb2
  refine Hs.mono (hs_inc C v2 _ (by vsimp [a0]; omega)) le_rfl ?_
  rintro e rfl
  exact ⟨⟨by vsimp [a0], by vsimp [a0], by vsimp [a0]⟩, rfl, Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩

theorem start_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk : ℕ) (hW : wdNeed r ≤ Wd) :
    Hs (ctxK RK Wd (cellInput r) Lk Bk) startP (a0 : DS VV MM) (startCost r)
      (fun e => Started (ctxK RK Wd (cellInput r) Lk Bk) r e) := by
  set C := ctxK RK Wd (cellInput r) Lk Bk with hC
  set X := (cellInput r).length with hX
  have hspec := cellReq_spec r
  have hkn : r.p.k ≤ r.c.n := le_of_lt hspec.k_lt
  have hWc : r.p.W = r.c.W := hspec.W_eq
  have hWd : wdNeed r ≤ C.Wd := hW
  unfold wdNeed at hWd
  have hWX : 10 * X + 20 ≤ C.Wd := by omega
  have hWlt : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hD := dOf_le r
  have hJD : r.p.J ≤ dOf r.c r.p := by unfold dOf; have := roleCount_pos r.c.kind; nlinarith
  have hcl := cellN_len_le r
  have hcw : (cellN r.c r.p r.wt).flatMap natWord = cellInput r := cellN_word _ _ _
  unfold startP
  apply Hx.hs
  -- the constants 1, 2
  refine Hs.then (PrefixProg.Hs.valid (cstInit_spec C (by omega)) (a0_valid C) (by omega))
    (fun e1 ⟨⟨c1, s1, f1⟩, w1⟩ n1 hn1 => ?_)
  simp only [DS.sh, Prod.mk.injEq] at s1
  obtain ⟨i1, o1, m1, r1, k1, ko1, kc1⟩ := s1
  have h0 : LS (C := C) e1 e1 [] (cellN r.c r.p r.wt) [] := by
    refine ⟨⟨?_, ?_, by simp, rfl, rfl, rfl, rfl⟩, ?_, c1, ?_⟩
    · simp
    · rw [m1, r1]; funext m; simp only [Function.update_apply]; split_ifs <;> simp_all [a0]
    · rw [i1]; show (cellInput r).drop 0 = _; rw [← hcw]; simp
    · rw [m1, r1]; rfl
  have hJX : r.p.J ≤ 2 * X + 2 := hJD.trans hD
  refine Hs.then (PrefixProg.Hs.valid (loadP_spec (C := C) e1 r.c r.p r.wt [] X h0 (fun x hx => nbl_le_cellInput r x hx)
    (by omega) (by omega)) w1 (by omega)) (fun e2 ⟨⟨l2, g2N, g2K, g2S, g2J, g2RC, g2JR, f2⟩, w2⟩ n2 hn2 => ?_)
  obtain ⟨⟨lr2, lc2, li2, lo2, lk2, lko2, lkc2⟩, _, c2, _⟩ := l2
  have e2N : e2.ram sN = cellN r.c r.p r.wt := by rw [lr2, m1]; simp [a0]
  have e2Q : e2.ram sQ = [] := by rw [lr2, Function.update_of_ne (by decide), m1]; rfl
  have e2Qc : e2.rc sQ = 0 := by rw [lc2, Function.update_of_ne (by decide), r1]; rfl
  have hS : r.p.factors.sum < 2 ^ C.Wd :=
    lt_of_lt_of_le (factors_sum_lt r) (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hs.then (PrefixProg.Hs.valid (walk_spec C r.c r.p r.wt e2 e2N e2Q e2Qc g2S g2JR c2
    (lt_of_le_of_lt hcl (lt_of_lt_of_le (by omega) hWlt.le)) hS) w2 (by omega))
    (fun e3 ⟨⟨m3, r3, n3, v3, o3, ot3, c3, f3⟩, w3⟩ n3' hn3 => ?_)
  have hDB : deltaBound r.c r.p < 2 ^ C.Wd :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hs.last (PrefixProg.Hs.valid (cst_spec C r.c r.p e3 c3 v3 (by rw [f3 gN (by decide)]; exact g2N)
    (by rw [f3 gJ (by decide)]; exact g2J) (by rw [f3 gRC (by decide)]; exact g2RC) hWc hkn (by omega) hDB) w3
    (by omega)) (fun e4 ⟨⟨v4, s4, f4⟩, w4⟩ n4 hn4 => ?_)
  simp only [DS.sh, Prod.mk.injEq] at s4
  obtain ⟨i4, o4, m4, r4, k4, ko4, kc4⟩ := s4
  have g4 : ∀ y, y ∉ cstT → e4.env y = e3.env y := fun y hy => f4 y hy
  refine ⟨⟨⟨w4, cst_fr c3 f4 (by decide), by rw [m4, m3, Function.update_of_ne (by decide)]; exact e2N,
    by rw [g4 _ (by decide)]; exact n3, v4.s, v4.h1, v4.h0, v4.sh, v4.b2, v4.d, v4.vw2, v4.pad,
    by rw [k4, ot3.kin, lk2, k1]; rfl, ?_⟩, by rw [m4, m3]; simp, ?_, by rw [g4 _ (by decide)]; exact v3.np,
    by rw [g4 _ (by decide)]; exact v3.ex, by rw [g4 _ (by decide), f3 gKd (by decide)]; exact g2K,
    by rw [g4 _ (by decide), f3 gJ (by decide)]; exact g2J, by rw [g4 _ (by decide), f3 gRC (by decide)]; exact g2RC,
    v4.rw, by rw [o4, o3, lo2, o1]; rfl, ?_⟩, ?_⟩
  · rw [r4, m4, r3, m3, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), lc2, lr2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      r1, m1]; rfl
  · rw [r4, r3]; simp
  · rw [m4, m3, Function.update_of_ne (by decide), lr2, Function.update_of_ne (by decide), m1]; rfl
  · have hrc2 : e2.rc sN = (cellN r.c r.p r.wt).length := by rw [lc2, m1]; simp [a0]
    unfold startCost
    rw [← hX]
    rw [hrc2] at hn3
    omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
