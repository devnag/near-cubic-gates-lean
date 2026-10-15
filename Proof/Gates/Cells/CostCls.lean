import Proof.Gates.Cells.MainLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

theorem ctrL_length_eq (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) :
    (ctrL c p wt y).length = roleCount c.kind * (2 * p.J) := by
  unfold ctrL
  rw [List.length_flatMap]
  simp only [seg_length]
  rw [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

theorem kxL_length_eq (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) :
    (kxL c p wt y).length = roleCount c.kind * 4 := by
  unfold kxL
  rw [List.length_flatMap]
  simp only [List.length_append, pairOf_length]
  rw [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

/-- Monomial bookkeeping: `x ≤ a·y^5` and `z ≤ b·y^5` give `x·z ≤ a·b·y^10`. -/
theorem mul_bnd {x z a b y : ℕ} (hx : x ≤ a * y ^ 5) (hz : z ≤ b * y ^ 5) : x * z ≤ a * b * y ^ 10 := by
  calc x * z ≤ (a * y ^ 5) * (b * y ^ 5) := Nat.mul_le_mul hx hz
    _ = a * b * y ^ 10 := by ring

theorem pow_mono_y {y a b : ℕ} (hy : 1 ≤ y) (h : a ≤ b) : y ^ a ≤ y ^ b := Nat.pow_le_pow_right hy h

section B
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

theorem rowVals_length (y : Cells wt.I) : (rowVals c p wt y).length =
    (parts c).length * (wWin p ^ nDig c p * ∑ q ∈ p.primes, q ^ roleCount c.kind) := by
  simp only [rowVals, List.length_flatMap, List.length_map, vecs_len, vecsM_length, List.prod_replicate]
  rw [sum_sort_eq']
  simp [List.map_const', List.sum_replicate, mul_comm]
  left; left; rw [vecsM_length, List.prod_replicate]

include hs in
theorem wWin_le : wWin p ≤ c.n + 1 := by
  have := P_le_n c p hs
  unfold wWin; rw [hs.hE_eq]; omega

include hs in
theorem BN_le : wWin p ^ nDig c p ≤ (c.n + 1) ^ (2 * Jmax c.n) := by
  have h1 := wWin_le c p hs
  have h2 : nDig c p ≤ 2 * Jmax c.n := by
    unfold nDig
    have := roleCount_le_two c
    have := J_le_Jmax c p hs
    nlinarith
  calc wWin p ^ nDig c p ≤ (c.n + 1) ^ nDig c p := Nat.pow_le_pow_left h1 _
    _ ≤ (c.n + 1) ^ (2 * Jmax c.n) := Nat.pow_le_pow_right (by omega) h2

include hs in
theorem R_le : (reqIds c p).length ≤ (c.n + 1) ^ (2 * Jmax c.n) * (c.n + 1) ^ 4 := by
  rw [reqIds_len]
  have h1 := requestCount_le c p hs
  have h2 := P_le_n c p hs
  have h3 := J_le_Jmax c p hs
  calc requestCount c p ≤ p.P ^ (2 * p.J + 4) := h1
    _ ≤ (c.n + 1) ^ (2 * p.J + 4) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (c.n + 1) ^ (2 * Jmax c.n + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (c.n + 1) ^ (2 * Jmax c.n) * (c.n + 1) ^ 4 := by rw [pow_add]

include hs in
theorem rowVals_le (y : Cells wt.I) :
    (rowVals c p wt y).length ≤ 2 * ((c.n + 1) ^ (2 * Jmax c.n) * (c.n + 1) ^ 3) := by
  rw [rowVals_length]
  have h1 := parts_length_le c
  have h2 := rows_le c p hs
  have h3 := P_le_n c p hs
  have h4 := BN_le c p hs
  have h5 : p.P ^ 3 ≤ (c.n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) _
  calc (parts c).length * (wWin p ^ nDig c p * ∑ q ∈ p.primes, q ^ roleCount c.kind)
      ≤ 2 * ((c.n + 1) ^ (2 * Jmax c.n) * (c.n + 1) ^ 3) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h4 (h2.trans h5))

end B

section P
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hadm hs hw in
/-- **Per-cell cost.** `A = y^5`, `y = n + Big + Wd + Lk + Bk + 2`, `q = (n+1)^{2·Jmax n}`. -/
theorem cellCost_le (C : Ctx) (Big : ℕ) (hWd : wdNeed c p wt Big ≤ C.Wd) (TG TS : ℕ) :
    cellCostU c p wt TG TS ≤ 6000000 * ((c.n + 1) ^ (2 * Jmax c.n) *
      ((c.n + Big + C.Wd + C.Lk + C.Bk + 2) ^ 5 * (c.n + Big + C.Wd + C.Lk + C.Bk + 2) ^ 5)) + TG + TS := by
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  generalize hy : c.n + Big + C.Wd + C.Lk + C.Bk + 2 = y
  generalize hq : (c.n + 1) ^ (2 * Jmax c.n) = q
  have hq1 : 1 ≤ q := by rw [← hq]; exact Nat.one_le_pow _ _ (by omega)
  have hy1 : 1 ≤ y := by omega
  have hyA : y ≤ y ^ 5 := by simpa using pow_mono_y hy1 (show 1 ≤ 5 by omega)
  generalize hA : y ^ 5 = A at hyA
  have hA1 : 1 ≤ A := by omega
  have hJ := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hrc := roleCount_le_two c
  have hL0 := cellN_len c p wt hadm hs w hw
  have hL : (cellN c p wt).length ≤ 70 * A := by
    have : (c.n + 1) ^ 5 ≤ A := by rw [← hA]; exact Nat.pow_le_pow_left (by omega) 5
    omega
  have hR0 := R_le c p hs
  rw [hq] at hR0
  have hR : (reqIds c p).length ≤ q * A := by
    have : (c.n + 1) ^ 4 ≤ A := by
      rw [← hA]; exact (Nat.pow_le_pow_left (show c.n + 1 ≤ y by omega) 4).trans (pow_mono_y hy1 (by omega))
    exact hR0.trans (Nat.mul_le_mul_left _ this)
  have hrow0 := rowVals_le c p wt hs (cellOf wt.I 0)
  rw [hq] at hrow0
  have hrow : (rowVals c p wt (cellOf wt.I 0)).length ≤ 2 * (q * A) := by
    have : (c.n + 1) ^ 3 ≤ A := by
      rw [← hA]; exact (Nat.pow_le_pow_left (show c.n + 1 ≤ y by omega) 3).trans (pow_mono_y hy1 (by omega))
    have := Nat.mul_le_mul_left q this
    omega
  have hgW : gWork c p wt (cellOf wt.I 0) ≤ 73 * (q * A) := by
    unfold gWork
    have : A ≤ q * A := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hE : (ctrL c p wt (cellOf wt.I 0)).length ≤ 4 * A := by
    rw [ctrL_length_eq]; nlinarith
  have hX : (kxL c p wt (cellOf wt.I 0)).length ≤ 8 := by rw [kxL_length_eq]; omega
  have hW : recWidth c p wt ≤ A := by nlinarith
  have hN : c.n ≤ A := by omega
  have p1 : (reqIds c p).length * (12 * recWidth c p wt + 12 + 1 + (1 + 1 + 20) + 4) ≤ 51 * (q * (A * A)) := by
    calc (reqIds c p).length * (12 * recWidth c p wt + 12 + 1 + (1 + 1 + 20) + 4) ≤ (q * A) * (51 * A) :=
          Nat.mul_le_mul hR (by omega)
      _ = 51 * (q * (A * A)) := by ring
  have p2 : formsCost (cellN c p wt).length c.n ≤ 5112000 * (A * A) := by
    unfold formsCost
    calc 1000 * ((cellN c p wt).length + 1) * ((cellN c p wt).length + c.n + 1) ≤ 1000 * (71 * A) * (72 * A) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 5112000 * (A * A) := by ring
  have p3 : c.n * (6 * c.n + 26 + 4) ≤ 36 * (A * A) := by
    calc c.n * (6 * c.n + 26 + 4) ≤ A * (36 * A) := Nat.mul_le_mul hN (by omega)
      _ = 36 * (A * A) := by ring
  have m1 : A ≤ A * A := Nat.le_mul_of_pos_left _ (by omega)
  have m2 : A * A ≤ q * (A * A) := Nat.le_mul_of_pos_left _ (by omega)
  have m3 : q * A ≤ q * (A * A) := Nat.mul_le_mul_left _ m1
  unfold cellCostU blkCost passCost
  omega

end P

section Q
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hadm hs hw in
/-- **Prelude cost** (before the constants phase). -/
theorem preCost_le (C : Ctx) (Big : ℕ) :
    preCost c p wt Big ≤ 1000000 * ((c.n + Big + C.Wd + C.Lk + C.Bk + 2) ^ 5 *
      (c.n + Big + C.Wd + C.Lk + C.Bk + 2) ^ 5 * (c.n + Big + C.Wd + C.Lk + C.Bk + 2) ^ 5) := by
  generalize hy : c.n + Big + C.Wd + C.Lk + C.Bk + 2 = y
  have hy1 : 1 ≤ y := by omega
  have hyA : y ≤ y ^ 5 := by simpa using pow_mono_y hy1 (show 1 ≤ 5 by omega)
  generalize hA : y ^ 5 = A at hyA
  have hJ := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hrc := roleCount_le_two c
  have hL0 := cellN_len c p wt hadm hs w hw
  have hL : (cellN c p wt).length ≤ 70 * A := by
    have : (c.n + 1) ^ 5 ≤ A := by rw [← hA]; exact Nat.pow_le_pow_left (by omega) 5
    omega
  have hlen : (cellN c p wt).length = (callN c).length + (paramsN p).length + (witN c p wt).length := by
    simp [cellN]; omega
  have hsr : (srList c p).length ≤ 2 * A := by rw [srList_len]; nlinarith
  have hPr : (p.primes.sort (· ≤ ·)).length ≤ A := by
    rw [Finset.length_sort]; have := primes_card_le c p hs; have := P_le_n c p hs; omega
  have hB : 30 * Big + 45 ≤ 75 * A := by omega
  have q1 : (callN c).length * (30 * Big + 45) ≤ 5250 * (A * A) := by
    calc (callN c).length * (30 * Big + 45) ≤ (70 * A) * (75 * A) := Nat.mul_le_mul (by omega) hB
      _ = 5250 * (A * A) := by ring
  have q2 : (paramsN p).length * (30 * Big + 45) ≤ 5250 * (A * A) := by
    calc (paramsN p).length * (30 * Big + 45) ≤ (70 * A) * (75 * A) := Nat.mul_le_mul (by omega) hB
      _ = 5250 * (A * A) := by ring
  have q3 : (witN c p wt).length * (30 * Big + 45) ≤ 5250 * (A * A) := by
    calc (witN c p wt).length * (30 * Big + 45) ≤ (70 * A) * (75 * A) := Nat.mul_le_mul (by omega) hB
      _ = 5250 * (A * A) := by ring
  have m1 : A ≤ A * A := Nat.le_mul_of_pos_left _ (by omega)
  have m2 : A * A ≤ A * A * A := Nat.le_mul_of_pos_right _ (by omega)
  have q4 : (srList c p).length * ((witN c p wt).length * (30 * Big + 45) + 10 + 4) ≤ 10528 * (A * A * A) := by
    calc (srList c p).length * ((witN c p wt).length * (30 * Big + 45) + 10 + 4) ≤ (2 * A) * (5264 * (A * A)) :=
          Nat.mul_le_mul hsr (by omega)
      _ = 10528 * (A * A * A) := by ring
  have q5 : p.J * roleCount c.kind * (10 * (cellN c p wt).length + 20 + 4) ≤ 1448 * (A * A) := by
    calc p.J * roleCount c.kind * (10 * (cellN c p wt).length + 20 + 4) ≤ (2 * A) * (724 * A) :=
          Nat.mul_le_mul (by rw [← srList_len]; exact hsr) (by omega)
      _ = 1448 * (A * A) := by ring
  unfold preCost ldCost loadCost wcCost w2Cost w3Cost
  omega

end Q

/-- **The cost class of `mainOf`**, from the classes of the three phases: one constant, one exponent. -/
theorem totCost_class (S : SolveMachine) (tc tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ)
    (hCc : ConstClass tc) (hGc : GatherClass tg) (hSc : SysClass ts) :
    ∃ K e : ℕ, ∀ (C : Ctx) {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) (Big : ℕ),
      (∀ x ∈ cellN r.c r.p r.wt, natBitLength x ≤ Big) → wdNeed r.c r.p r.wt Big ≤ C.Wd →
      totCost tc tg ts S C r.c r.p r.wt Big ≤ loopCost K e C r.c r.p Big := by
  obtain ⟨Kc, ec, hc⟩ := hCc
  obtain ⟨Kg, eg, hg⟩ := hGc
  obtain ⟨Ks, es, hss⟩ := hSc
  refine ⟨7100000 + Kc + 3 * Kg + 2 * Ks + 20, 15 + ec + eg + es, fun C B1 B2 cT r Big hBig hWd => ?_⟩
  obtain ⟨w, hw⟩ := r.hw
  have hadm := r.adm
  have hs := selectParams_spec cT (header r.c) r.p r.hp
  have hcb := cb_eq r.c r.p r.wt hs w hw
  have hpre := preCost_le r.c r.p r.wt hadm hs w hw C Big
  have hcell := cellCost_le r.c r.p r.wt hadm hs w hw C Big hWd (tg C r.c r.p Big) (ts S C r.c r.p Big)
  have htc := hc C r.c r.p Big
  have htg := hg C r.c r.p Big
  have hts := hss S C r.c r.p Big
  have hR0 := R_le r.c r.p hs
  have hBN := BN_le r.c r.p hs
  unfold totCost loopCost
  rw [hcb]
  generalize hy : r.c.n + Big + C.Wd + C.Lk + C.Bk + 2 = y at hpre hcell
  generalize hq : (r.c.n + 1) ^ (2 * Jmax r.c.n) = q at hcell hR0 hBN
  generalize hG : 2 ^ (r.c.n - r.p.k) = G
  have hy1 : 1 ≤ y := by omega
  have hq1 : 1 ≤ q := by rw [← hq]; exact Nat.one_le_pow _ _ (by omega)
  have hG1 : 1 ≤ G := by rw [← hG]; exact Nat.one_le_two_pow
  set E := 15 + ec + eg + es with hE
  have hZ1 : 1 ≤ y ^ E := Nat.one_le_pow _ _ (by omega)
  -- the phases' classes in `y`
  have hy2 : r.c.n + Big + C.Wd + 2 ≤ y := by omega
  have hy3 : r.c.n + Big + C.Lk + C.Bk + 2 ≤ y := by omega
  have htc' : tc C r.c r.p Big ≤ Kc * y ^ E := by
    calc tc C r.c r.p Big ≤ Kc * (r.c.n + Big + C.Wd + 2) ^ ec := htc
      _ ≤ Kc * y ^ E := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hy2 _).trans (pow_mono_y hy1 (by omega)))
  have hR : (reqIds r.c r.p).length + wWin r.p ^ nDig r.c r.p + 1 ≤ 3 * (q * y ^ 4) := by
    have h4 : (r.c.n + 1) ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h5 : q * (r.c.n + 1) ^ 4 ≤ q * y ^ 4 := Nat.mul_le_mul_left _ h4
    have h6 : q ≤ q * y ^ 4 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
    omega
  have htg' : tg C r.c r.p Big ≤ 3 * Kg * (q * y ^ E) := by
    calc tg C r.c r.p Big ≤ Kg * ((reqIds r.c r.p).length + wWin r.p ^ nDig r.c r.p + 1) *
          (r.c.n + Big + C.Wd + 2) ^ eg := htg
      _ ≤ Kg * (3 * (q * y ^ 4)) * y ^ eg :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hR) (Nat.pow_le_pow_left hy2 _)
      _ = 3 * Kg * (q * y ^ (4 + eg)) := by rw [pow_add]; ring
      _ ≤ 3 * Kg * (q * y ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (pow_mono_y hy1 (by omega)))
  have hts' : ts S C r.c r.p Big ≤ 2 * Ks * (q * y ^ E) := by
    calc ts S C r.c r.p Big ≤ Ks * (wWin r.p ^ nDig r.c r.p + 1) * (r.c.n + Big + C.Lk + C.Bk + 2) ^ es := hts
      _ ≤ Ks * (2 * q) * y ^ es := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hy3 _)
      _ = 2 * Ks * (q * y ^ es) := by ring
      _ ≤ 2 * Ks * (q * y ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (pow_mono_y hy1 (by omega)))
  have hp15 : y ^ 5 * y ^ 5 * y ^ 5 ≤ y ^ E := by rw [← pow_add, ← pow_add]; exact pow_mono_y hy1 (by omega)
  have hp10 : y ^ 5 * y ^ 5 ≤ y ^ E := by rw [← pow_add]; exact pow_mono_y hy1 (by omega)
  have hqZ : q * (y ^ 5 * y ^ 5) ≤ q * y ^ E := Nat.mul_le_mul_left _ hp10
  have hZq : y ^ E ≤ q * y ^ E := Nat.le_mul_of_pos_left _ (by omega)
  have hcellZ : cellCostU r.c r.p r.wt (tg C r.c r.p Big) (ts S C r.c r.p Big) + 4 ≤
      (6000004 + 3 * Kg + 2 * Ks) * (q * y ^ E) := by
    have : 1 ≤ q * y ^ E := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hloop : G * (cellCostU r.c r.p r.wt (tg C r.c r.p Big) (ts S C r.c r.p Big) + 4) ≤
      (6000004 + 3 * Kg + 2 * Ks) * (G * (q * y ^ E)) := by
    calc G * (cellCostU r.c r.p r.wt (tg C r.c r.p Big) (ts S C r.c r.p Big) + 4) ≤
          G * ((6000004 + 3 * Kg + 2 * Ks) * (q * y ^ E)) := Nat.mul_le_mul_left _ hcellZ
      _ = (6000004 + 3 * Kg + 2 * Ks) * (G * (q * y ^ E)) := by ring
  have hT1 : q * y ^ E ≤ G * (q * y ^ E) := Nat.le_mul_of_pos_left _ (by omega)
  have hT0 : 1 ≤ q * y ^ E := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hfin : (7100000 + Kc + 3 * Kg + 2 * Ks + 20) * G * q * y ^ E =
      (7100000 + Kc + 3 * Kg + 2 * Ks + 20) * (G * (q * y ^ E)) := by ring
  rw [hfin]
  have hKc : Kc * y ^ E ≤ Kc * (G * (q * y ^ E)) := Nat.mul_le_mul_left _ (hZq.trans hT1)
  nlinarith

theorem cellsLoopGoal (S : SolveMachine) (cP gP sP : St VV MM) (tc tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ)
    (hC : ConstGoal cP tc) (hCc : ConstClass tc) (hG : GatherGoal gP tg) (hGc : GatherClass tg)
    (hS : SysGoal sP ts) (hSc : SysClass ts) :
    ∃ K e : ℕ, LoopGoal (mainOf cP gP sP) S K e := by
  obtain ⟨K, e, hKe⟩ := totCost_class S tc tg ts hCc hGc hSc
  exact ⟨K, e, mainOf_goal S cP gP sP tc tg ts hC hG hS K e (fun C _ _ _ r Big hBig hWd => hKe C r Big hBig hWd)⟩

end NearCubicGates.Close.Cells
