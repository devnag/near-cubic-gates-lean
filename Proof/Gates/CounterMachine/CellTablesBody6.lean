import Proof.Gates.CounterMachine.CellTablesBody5

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem prime_le_P (r : CellReq B1 B2 cT) {q : ℕ} (hq : q ∈ r.p.primes) : q ≤ r.p.P ∧ Nat.Prime q := by
  have hs := cellReq_spec r
  have hq' : q ∈ dyadicPrimes r.p.P := by rw [← hs.primes_eq]; exact hq
  rw [mem_dyadicPrimes] at hq'
  exact ⟨hq'.1, hq'.2.1⟩

theorem lt_keyB (p : Params) (v : ℕ) (hv : v ≤ p.P) : v < 2 ^ keyBits p := by
  unfold keyBits
  exact lt_of_le_of_lt (by omega) (Nat.lt_size_self (p.P + p.J + 3))

theorem keyBits_le (c : Call) (p : Params) : keyBits p ≤ keyBits p * keyLen c p :=
  Nat.le_mul_of_pos_right _ (by unfold keyLen; omega)

theorem resHead_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (part : Option Bool) (q t : ℕ) (hF : Fit RK r Wd Lk Bk wb) (hP : Pre (ctxK RK Wd inp Lk Bk) r a)
    (hpart : part ∈ parts r.c) (hq : q ∈ r.p.primes) (hPC : a.env lPC = partCode part) (hQ : a.env lQ = q)
    (hQD : a.env lQD = q ^ dOf r.c r.p) :
    Hs (ctxK RK Wd inp Lk Bk) resHead a (200 * (cellInput r).length + 1000) (fun e =>
      e.kin = natWord 0 ++ natWord (partCode part) ++ natWord q ++ natWord (dOf r.c r.p) ∧
      e.env bKey = partCode part * 2 ^ keyBits r.p + q ∧ e.env bPw = q ^ dOf r.c r.p ∧ SameN a e ∧ Cst e ∧
      BF a e ∧ Valid (ctxK RK Wd inp Lk Bk) e) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  set X := (cellInput r).length with hX
  have hWd : 4 ≤ C.Wd := by have := hF.wd; show 4 ≤ Wd; omega
  obtain ⟨hqP, hqp⟩ := prime_le_P r hq
  have hq0 : 0 < q := hqp.pos
  have hpc : partCode part ≤ 2 := by cases part with | none => decide | some b => cases b <;> decide
  set x : TabCallReq B1 B2 cT := ⟨r, resId r.c r.p part q t, resId_mem r.c r.p part q t hpart hq hq0⟩ with hx
  have hLk : (tabCallInput x).length ≤ C.Lk := hF.lk x rfl
  have hRK : (tabCallInput x).length = (natWord 0).length + (natWord (partCode part)).length + (natWord q).length +
      (natWord (dOf r.c r.p)).length + ((digs q t (dOf r.c r.p)).flatMap natWord).length + X := by
    show ((descN (resId r.c r.p part q t)).flatMap natWord ++ cellInput r).length = _
    rw [descN_res]; simp only [List.length_append]; omega
  have hB : partCode part * 2 ^ keyBits r.p + q < 3 * 2 ^ keyBits r.p := by
    have := lt_keyB r.p q hqP; nlinarith
  have hBW : 4 * 2 ^ keyBits r.p ≤ 2 ^ C.Wd := by
    have h1 := keyBits_le r.c r.p
    have h2 := hF.wd
    unfold lamW at h2
    calc 4 * 2 ^ keyBits r.p = 2 ^ (keyBits r.p + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by show _ ≤ Wd; omega)
  have hnq := nbl_le_cellInput r q (prime_mem_cellN r hq)
  have hnD := (nbl_le_self (dOf r.c r.p)).trans (by have := dOf_le r; omega : dOf r.c r.p + 1 ≤ 2 * X + 3)
  have hnpc := (nbl_le_self (partCode part)).trans (by omega : partCode part + 1 ≤ 3)
  have hn0 : natBitLength 0 ≤ 1 := nbl_le_self 0
  apply Hx.hs
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C vZ (by decide) a hP.cst (by omega) 0 hP.cst.z (Nat.two_pow_pos _)
    (by rw [hP.kin]; simp only [List.length_nil, zero_add]; omega)) hP.valid (by omega))
    (fun e1 ⟨⟨k1, s1, c1, f1⟩, w1⟩ n1 hn1 => ?_)
  have e1pc : e1.env lPC = partCode part := by rw [f1 lPC (by decide)]; exact hPC
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C lPC (by decide) e1 c1 (by omega) _ e1pc
    (by rw [← e1pc]; exact w1.env_lt lPC) (by rw [k1, hP.kin]; simp only [List.nil_append]; omega)) w1 (by omega))
    (fun e2 ⟨⟨k2, s2, c2, f2⟩, w2⟩ n2 hn2 => ?_)
  have e2q : e2.env lQ = q := by rw [f2 lQ (by decide), f1 lQ (by decide)]; exact hQ
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C lQ (by decide) e2 c2 (by omega) _ e2q
    (by rw [← e2q]; exact w2.env_lt lQ) (by rw [k2, k1, hP.kin]; simp only [List.nil_append, List.length_append]; omega))
    w2 (by omega)) (fun e3 ⟨⟨k3, s3, c3, f3⟩, w3⟩ n3 hn3 => ?_)
  have e3D : e3.env kD = dOf r.c r.p := by rw [f3 kD (by decide), f2 kD (by decide), f1 kD (by decide)]; exact hP.d
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C kD (by decide) e3 c3 (by omega) _ e3D
    (by rw [← e3D]; exact w3.env_lt kD)
    (by rw [k3, k2, k1, hP.kin]; simp only [List.nil_append, List.length_append]; omega)) w3 (by omega))
    (fun e4 ⟨⟨k4, s4, c4, f4⟩, w4⟩ n4 hn4 => ?_)
  have g4 : ∀ y, y ∉ emT → e4.env y = a.env y := fun y hy => by
    rw [f4 y hy, f3 y hy, f2 y hy, f1 y hy]
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C bKey lPC e4 (by decide)) w4 (by omega))
    (fun e5 ⟨he5, w5⟩ n5 hn5 => ?_); subst he5
  refine Hs.then (PrefixProg.Hs.valid (hs_mul C bKey kB2 bTmp _ (by decide) (by decide) (by decide)
    (by vsimp [g4 lPC (by decide), g4 kB2 (by decide), hPC, hP.b2]; nlinarith)) w5 (by omega))
    (fun e6 ⟨he6, w6⟩ n6 hn6 => ?_); subst he6
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C bKey bTmp _ (by decide)) w6 (by omega)) (fun e7 ⟨he7, w7⟩ n7 hn7 => ?_)
  subst he7
  refine Hs.then (PrefixProg.Hs.valid (hs_add C bKey lQ _ (by decide)
    (by vsimp [g4 lPC (by decide), g4 kB2 (by decide), g4 lQ (by decide), hPC, hP.b2, hQ]; omega)) w7 (by omega))
    (fun e8 ⟨he8, w8⟩ n8 hn8 => ?_); subst he8
  refine Hs.last (PrefixProg.Hs.valid (hs_copy C bPw lQD _ (by decide)) w8 (by omega)) (fun e9 ⟨he9, w9⟩ n9 hn9 => ?_)
  subst he9
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [DS.set]; rw [k4, k3, k2, k1, hP.kin]; simp
  · vsimp [g4 lPC (by decide), g4 kB2 (by decide), g4 lQ (by decide), hPC, hP.b2, hQ]
  · vsimp [g4 lQD (by decide), hQD]
  · exact s1.trans (s2.trans (s3.trans (s4.trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans
      ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans (SameN.set _ _ _))))))))
  · exact ⟨by vsimp [c4.z], by vsimp [c4.one], by vsimp [c4.two]⟩
  · exact BF.trans (BF.of_fr f1 (by decide)) (BF.trans (BF.of_fr f2 (by decide)) (BF.trans (BF.of_fr f3 (by decide))
      (BF.trans (BF.of_fr f4 (by decide)) (BF.trans (BF.set _ _ _ (by decide)) (BF.trans (BF.set _ _ _ (by decide))
      (BF.trans (BF.set _ _ _ (by decide)) (BF.trans (BF.set _ _ _ (by decide)) (BF.set _ _ _ (by decide)))))))))
  · exact w9
  · omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
