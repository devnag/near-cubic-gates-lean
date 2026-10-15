import Proof.Gates.CounterMachine.PrefixRun2

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicWires.RepairOrdinary (frame WordFunction)

/-! ## The length of the cell input, with explicit constants -/

theorem cellInput_len_explicit {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    (cellInput r).length ≤ 2 ^ 19 * (r.c.n + 1) ^ (B1 + B2 + 13) := by
  obtain ⟨w, hw⟩ := r.hw
  have hadm := r.adm
  have hs := selectParams_spec cT (header r.c) r.p r.hp
  set c := r.c
  set N := c.n + 1 with hN
  have hN5 : 5 ≤ N := by have := hadm.1; omega
  have hN1 : 1 ≤ N := by omega
  set Q := N ^ (B1 + B2 + 8) with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have q1 : N ≤ Q := by simpa using pw_le hN1 (show 1 ≤ B1 + B2 + 8 by omega)
  have q2 : N ^ 2 ≤ Q := pw_le hN1 (by omega)
  have q4 : N ^ 4 ≤ Q := pw_le hN1 (by omega)
  have qB : N ^ B2 ≤ Q := pw_le hN1 (by omega)
  have hW := hadm.2.2.2.2.2.2.1
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hbits : ∀ x ∈ cellN c r.p r.wt, natBitLength x ≤ 2 ^ 10 * Q := by
    intro x hx
    simp only [cellN, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · have := call_bits c hadm x hx; rw [← hN] at this; omega
    · have := params_bits c r.p hadm hs x hx; rw [← hN] at this; omega
    · have := wit_bits c r.p hadm hs r.wt w hw x hx; omega
  have hlen : (cellN c r.p r.wt).length ≤ 70 * N ^ 5 := by
    have h1 := call_len c hadm
    have h2 := params_len c r.p hadm hs
    have h3 := wit_len c r.p hadm hs r.wt w hw
    have hJ := (J_le_Jmax c r.p hs).trans (Jmax_le c r.p hadm hs)
    have e1 : (2 * c.W) ≤ 4 * N ^ 4 := by omega
    have e2 : r.p.J * 2 * (1 + 2 * c.W) ≤ 2 * N * (1 + 4 * N ^ 4) := by
      have := Nat.mul_le_mul (show r.p.J * 2 ≤ 2 * N by omega) (show 1 + 2 * c.W ≤ 1 + 4 * N ^ 4 by omega)
      exact this
    rw [← hN] at h1 h2
    have e3 : N ^ 5 = N * N ^ 4 := by ring
    have e4 : 5 * N ^ 4 ≤ N ^ 5 := by rw [e3]; exact Nat.mul_le_mul_right _ hN5
    have e5 : N ≤ N ^ 4 := by simpa using pw_le hN1 (show 1 ≤ 4 by omega)
    have e6 : 4 * N ^ 4 * (2 * N + 7) = 8 * N ^ 5 + 28 * N ^ 4 := by ring
    have e7 : 2 * N * (1 + 4 * N ^ 4) = 2 * N + 8 * N ^ 5 := by ring
    simp only [cellN, List.length_append]
    omega
  have hcell : cellInput r = (cellN c r.p r.wt).flatMap natWord := by
    rw [cellN_word]; rfl
  rw [hcell]
  have h := flat_len_le _ _ hbits
  have h5 : N ^ 5 * Q = N ^ (B1 + B2 + 13) := by rw [hQ, ← pow_add]; ring_nf
  calc _ ≤ (cellN c r.p r.wt).length * (2 * (2 ^ 10 * Q) + 1) := h
    _ ≤ 70 * N ^ 5 * (2 ^ 12 * Q) := Nat.mul_le_mul hlen (by omega)
    _ ≤ 2 ^ 19 * N ^ (B1 + B2 + 13) := by rw [← h5]; nlinarith

/-! ## The packaging -/

/-- A callee that is never called (no requests): the prefix program makes no calls. -/
noncomputable def noCallee : Callee :=
  ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    wordFunction_of_wmx (WMX.skip : WMX 1 0) 1 (by decide) (fun _ => 0) (fun e => e.elim)⟩

def zP (B1 B2 : ℕ) : Sz := ⟨16 * (2 ^ 19 + 1) ^ 2, 2 * (B1 + B2 + 13), 0, 0, 0, 0⟩

theorem pow_nbl (n : ℕ) : n + 1 ≤ 2 ^ natBitLength n := by
  unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem pow_nbl_le (n : ℕ) : 2 ^ natBitLength n ≤ 2 * (n + 1) := by
  unfold natBitLength
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega); omega

/-- The width of the run covers every field. -/
theorem width_ok {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    Lam r + 5 * (cellInput r).length + 8 ≤ (zP B1 B2).W (leadOnes (cellInput r)) := by
  set X := (cellInput r).length with hX
  set E := B1 + B2 + 13 with hE
  set N := (r.c.n + 1) ^ E with hNdef
  have hXl : X ≤ 2 ^ 19 * N := cellInput_len_explicit r
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have h1 : X + 1 ≤ (2 ^ 19 + 1) * N := by nlinarith
  have h2 : Lam r + 5 * X + 8 ≤ 16 * ((X + 1) * (X + 1)) := by
    have : Lam r = 8 * ((X + 1) * (X + 1)) := by unfold Lam; rw [pow_two]
    rw [this]; nlinarith
  have h3 : N ≤ 2 ^ (E * natBitLength r.c.n) := by
    rw [hNdef, mul_comm, pow_mul]; exact Nat.pow_le_pow_left (pow_nbl _) E
  have h4 : (X + 1) * (X + 1) ≤ (2 ^ 19 + 1) ^ 2 * (2 ^ (E * natBitLength r.c.n) * 2 ^ (E * natBitLength r.c.n)) := by
    calc (X + 1) * (X + 1) ≤ ((2 ^ 19 + 1) * N) * ((2 ^ 19 + 1) * N) := Nat.mul_le_mul h1 h1
      _ = (2 ^ 19 + 1) ^ 2 * (N * N) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 h3)
  have h5 : (zP B1 B2).W (leadOnes (cellInput r)) =
      16 * ((2 ^ 19 + 1) ^ 2 * (2 ^ (E * natBitLength r.c.n) * 2 ^ (E * natBitLength r.c.n))) := by
    unfold Sz.W zP; rw [leadOnes_cellInput]; simp only
    rw [← pow_add, show E * natBitLength r.c.n + E * natBitLength r.c.n = 2 * E * natBitLength r.c.n by ring]
    ring
  rw [h5]; omega

theorem run_ok {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : ∃ b n,
    Ex (ctxOf noCallee (zP B1 B2) (cellInput r)) mainP a0 b n ∧ b.out = prefixesWord r ∧ n ≤ costP r := by
  obtain ⟨b, n, hex, hn, hb⟩ := main_run r (ctxOf noCallee (zP B1 B2) (cellInput r)) rfl (width_ok r)
  exact ⟨b, n, hex, hb, hn⟩

theorem one_le_W (B1 B2 : ℕ) (inp : List Bool) : 1 ≤ (zP B1 B2).W (leadOnes inp) := by
  unfold Sz.W zP; simp only
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by norm_num))

/-- The step budget of the prefix machine. -/
noncomputable def prefixBudget (B1 B2 cT : ℕ) (r : CellReq B1 B2 cT) : ℕ :=
  langBudget noCallee (zP B1 B2) VV MM (cellInput r) (costP r)

/-- The prefix machine as a `WordFunction`. -/
noncomputable def prefixWF (B1 B2 cT : ℕ) :
    WordFunction (CellReq B1 B2 cT) cellInput prefixesWord (prefixBudget B1 B2 cT) :=
  wordFunction_of_lang cellInput prefixesWord noCallee (zP B1 B2) mainP costP run_ok
    (fun r => one_le_W B1 B2 (cellInput r))

/-! ## The cost class -/

section Class
variable {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT)

theorem ns_le_X : (srList r.c r.p).length ≤ (cellInput r).length := by
  have h2 : (srList r.c r.p).length ≤ (witRest r.c r.p r.wt).length := by
    unfold witRest; rw [List.length_flatMap]
    calc (srList r.c r.p).length = ((srList r.c r.p).map fun _ => 1).sum := by simp
      _ ≤ _ := by apply List.sum_le_sum; intro x _; simp
  have h3 : (witN r.c r.p r.wt).length = 1 + (coordsOf r.wt.I).length + (witRest r.c r.p r.wt).length := by
    unfold witN witRest; simp; omega
  have h4 : (cellN r.c r.p r.wt).length =
      (callN r.c).length + (paramsN r.p).length + (witN r.c r.p r.wt).length := by
    unfold cellN; simp only [List.length_append]
  have := cellN_len_le r
  omega

theorem parts_le_X : (callN r.c).length ≤ (cellInput r).length ∧ (paramsN r.p).length ≤ (cellInput r).length ∧
    (witN r.c r.p r.wt).length ≤ (cellInput r).length := by
  have h4 : (cellN r.c r.p r.wt).length =
      (callN r.c).length + (paramsN r.p).length + (witN r.c r.p r.wt).length := by
    unfold cellN; simp only [List.length_append]
  have := cellN_len_le r
  omega

theorem m_le_X : (r.c.first.gates.flatMap gateN).length + (r.c.second.gates.flatMap gateN).length +
    r.c.parity.length ≤ (cellInput r).length := by
  have h1 := circ_len_ge r.c.first
  have h2 := circ_len_ge r.c.second
  have h3 := split_len r
  have h4 := cellN_len_le r
  omega

theorem lam_eq : Lam r = 8 * ((cellInput r).length + 1) ^ 2 := rfl

theorem loadCost_mono {a b c d e a' b' c' d' e' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d')
    (h5 : e ≤ e') : loadCost a b c d e ≤ loadCost a' b' c' d' e' := by
  unfold loadCost; gcongr

theorem loadCost_poly (Y : ℕ) (hY : 1 ≤ Y) : loadCost Y Y Y Y (8 * Y ^ 2) ≤ 2000 * Y ^ 4 := by
  have h1 : Y ≤ Y ^ 2 := by nlinarith
  have h2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
  have h3 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY (by omega)
  unfold loadCost
  nlinarith

theorem preCost_le : preCost r.c r.p r.wt (Lam r) ≤
    2 ^ r.p.k * (10 ^ 4 * ((cellInput r).length + 1) ^ 3) := by
  set Y := (cellInput r).length + 1 with hY
  have hX := m_le_X r
  have hkk := kk_le_X r
  have hG := G_le_X r
  have hn := n_le_X r
  have e1 : (r.c.first.gates.flatMap gateN).length ≤ Y := by omega
  have e2 : (r.c.second.gates.flatMap gateN).length ≤ Y := by omega
  have e3 : r.c.parity.length ≤ Y := by omega
  have e4 : (coordsOf r.wt.I).length ≤ Y := by omega
  have e5 : r.c.first.gates.length + r.c.second.gates.length ≤ Y := by omega
  have e6 : r.c.n ≤ Y := by omega
  have step : preCost r.c r.p r.wt (Lam r) ≤
      (25 * Lam r + 25 + (Y * (25 * Lam r + 32) + 7 + (Y * (25 * Lam r + 32) + 7) + 1) + 1) +
      (25 * Lam r + 25 + (2 ^ r.p.k * (Y * (20 * Y + 15) + 74) + 4) + 1) +
      (25 * Lam r + 25 + (Y * (100 * Lam r + 110) + 8) + 1 + 1) +
      (Y + Y + 8) * (25 * Lam r + 9 * Y + 50) := by
    unfold preCost; gcongr
  refine step.trans ?_
  rw [lam_eq, ← hY]
  have hY1 : 1 ≤ Y := by omega
  have hP : 1 ≤ 2 ^ r.p.k := Nat.one_le_two_pow
  generalize 2 ^ r.p.k = P at hP ⊢
  have h1 : Y ≤ Y ^ 2 := by nlinarith
  have h2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by omega)
  have q0 : 1 ≤ P * Y ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have q1 : Y ≤ P * Y ^ 3 := le_trans (h1.trans h2) (Nat.le_mul_of_pos_left _ hP)
  have q2 : Y ^ 2 ≤ P * Y ^ 3 := le_trans h2 (Nat.le_mul_of_pos_left _ hP)
  have q3 : Y ^ 3 ≤ P * Y ^ 3 := Nat.le_mul_of_pos_left _ hP
  have q4 : P ≤ P * Y ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
  have q5 : P * Y ≤ P * Y ^ 3 := Nat.mul_le_mul_left _ (h1.trans h2)
  have q6 : P * Y ^ 2 ≤ P * Y ^ 3 := Nat.mul_le_mul_left _ h2
  nlinarith

theorem costP_le : costP r ≤ 2 ^ r.p.k * (10 ^ 5 * ((cellInput r).length + 1) ^ 4) := by
  obtain ⟨c1, c2, c3⟩ := parts_le_X r
  have c4 := ns_le_X r
  have hpre := preCost_le r
  have hn := n_le_X r
  have hk := k_le_n r
  have hN := cellN_len_le r
  set Y := (cellInput r).length + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hload : loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length
      (srList r.c r.p).length (Lam r) ≤ 2000 * Y ^ 4 :=
    (loadCost_mono (by omega) (by omega) (by omega) (by omega) (by rw [lam_eq])).trans (loadCost_poly Y hY1)
  unfold costP
  have hP : 1 ≤ 2 ^ r.p.k := Nat.one_le_two_pow
  generalize 2 ^ r.p.k = P at hP hpre ⊢
  generalize preCost r.c r.p r.wt (Lam r) = Q at hpre ⊢
  generalize loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length
      (srList r.c r.p).length (Lam r) = L at hload ⊢
  have h3 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by omega)
  have h1 : Y ≤ Y ^ 4 := Nat.le_self_pow (by omega) Y
  have q0 : 1 ≤ P * Y ^ 4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have q1 : Y ≤ P * Y ^ 4 := le_trans h1 (Nat.le_mul_of_pos_left _ hP)
  have q4 : Y ^ 4 ≤ P * Y ^ 4 := Nat.le_mul_of_pos_left _ hP
  have q3 : P * Y ^ 3 ≤ P * Y ^ 4 := Nat.mul_le_mul_left _ h3
  nlinarith

end Class

/-- R's language budget with no call bounds: at most `10⁶·(N+1)·H²`, `H` = width + leading ones + input length +
the size constants + the callee's tape count + 1. -/
theorem lang_le (K : Callee) (a1 c1 : ℕ) (inp : List Bool) (N : ℕ) :
    langBudget K ⟨a1, c1, 0, 0, 0, 0⟩ VV MM inp N ≤
      10 ^ 6 * ((N + 1) * (2 ^ (c1 * leadOnes inp) * a1 + leadOnes inp + inp.length + a1 + c1 + TSK K + 1) ^ 2) := by
  simp only [langBudget, costA, costB, costC, Sz.W, Sz.Lk, Sz.Bk, zero_mul, pow_zero, mul_zero, zero_add, add_zero,
    VV, MM]
  generalize 2 ^ (c1 * leadOnes inp) * a1 = W
  generalize leadOnes inp = L
  generalize inp.length = I
  generalize TSK K = T
  have hS1 : 1 ≤ (N + 1) * (W + L + I + a1 + c1 + T + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have base : ∀ x, x ≤ W + L + I + a1 + c1 + T + 1 → x ≤ (N + 1) * (W + L + I + a1 + c1 + T + 1) ^ 2 := by
    intro x hx
    calc x ≤ (W + L + I + a1 + c1 + T + 1) ^ 2 := hx.trans (Nat.le_self_pow (by omega) _)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have prod : ∀ x y, x ≤ W + L + I + a1 + c1 + T + 1 → y ≤ W + L + I + a1 + c1 + T + 1 →
      x * y ≤ (N + 1) * (W + L + I + a1 + c1 + T + 1) ^ 2 := by
    intro x y hx hy
    calc x * y ≤ (W + L + I + a1 + c1 + T + 1) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hx hy
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have nprod : ∀ x, x ≤ W + L + I + a1 + c1 + T + 1 → N * x ≤ (N + 1) * (W + L + I + a1 + c1 + T + 1) ^ 2 := by
    intro x hx
    exact Nat.mul_le_mul (by omega) (hx.trans (Nat.le_self_pow (by omega) _))
  have nW2 : N * W ^ 2 ≤ (N + 1) * (W + L + I + a1 + c1 + T + 1) ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  have f1 := base L (by omega)
  have f2 := base a1 (by omega)
  have f3 := base W (by omega)
  have f4 := base I (by omega)
  have f6 := prod L W (by omega) (by omega)
  have f7 := prod L c1 (by omega) (by omega)
  have f8 := nprod W (by omega)
  have f9 := nprod T (by omega)
  have f10 := nprod 1 (by omega)
  generalize (N + 1) * (W + L + I + a1 + c1 + T + 1) ^ 2 = S at *
  nlinarith

/-- The budget bound for any width constants `a1`, `c1 ≥ 1` (no call bounds): `C·2^k·(X+1)^{4+2c1}`, with `C`
depending only on `a1`, `c1` and the (never called) callee. -/
theorem budget_bound (a1 c1 : ℕ) (hc1 : 1 ≤ c1) {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    langBudget noCallee ⟨a1, c1, 0, 0, 0, 0⟩ VV MM (cellInput r) (costP r) ≤
      10 ^ 6 * ((10 ^ 5 + 1) * (a1 * 2 ^ c1 + a1 + c1 + TSK noCallee + 3) ^ 2) * 2 ^ r.p.k *
        ((cellInput r).length + 1) ^ (4 + 2 * c1) := by
  have hlang := lang_le noCallee a1 c1 (cellInput r) (costP r)
  have hcost := costP_le r
  have hL : leadOnes (cellInput r) = natBitLength r.c.n := leadOnes_cellInput r
  have hn := n_le_X r
  rw [hL] at hlang
  generalize TSK noCallee = T at hlang ⊢
  generalize (cellInput r).length = X at hlang hcost hn ⊢
  have hY1 : 1 ≤ X + 1 := by omega
  have hYc : X + 1 ≤ (X + 1) ^ c1 := Nat.le_self_pow (by omega) _
  have hYc1 : 1 ≤ (X + 1) ^ c1 := Nat.one_le_pow _ _ (by omega)
  have hpow : 2 ^ natBitLength r.c.n ≤ 2 * (X + 1) := (pow_nbl_le _).trans (by omega)
  have hW : 2 ^ (c1 * natBitLength r.c.n) * a1 ≤ a1 * 2 ^ c1 * (X + 1) ^ c1 := by
    rw [mul_comm c1, pow_mul]
    calc (2 ^ natBitLength r.c.n) ^ c1 * a1 ≤ (2 * (X + 1)) ^ c1 * a1 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpow _)
      _ = a1 * 2 ^ c1 * (X + 1) ^ c1 := by rw [mul_pow]; ring
  have hLb : natBitLength r.c.n ≤ X + 1 := (nbl_le_self' _).trans (by omega)
  have hH : 2 ^ (c1 * natBitLength r.c.n) * a1 + natBitLength r.c.n + X + a1 + c1 + T + 1 ≤
      (a1 * 2 ^ c1 + a1 + c1 + T + 3) * (X + 1) ^ c1 := by
    have h1 : a1 + c1 + T + 1 ≤ (a1 + c1 + T + 1) * (X + 1) ^ c1 := Nat.le_mul_of_pos_right _ hYc1
    calc _ ≤ a1 * 2 ^ c1 * (X + 1) ^ c1 + (X + 1) ^ c1 + (X + 1) ^ c1 + (a1 + c1 + T + 1) * (X + 1) ^ c1 := by
          omega
      _ = _ := by ring
  have hP : 1 ≤ 2 ^ r.p.k := Nat.one_le_two_pow
  have hN1 : costP r + 1 ≤ 2 ^ r.p.k * ((10 ^ 5 + 1) * (X + 1) ^ 4) := by
    have : 1 ≤ 2 ^ r.p.k * (X + 1) ^ 4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc costP r + 1 ≤ 2 ^ r.p.k * (10 ^ 5 * (X + 1) ^ 4) + 2 ^ r.p.k * (X + 1) ^ 4 := by omega
      _ = _ := by ring
  calc _ ≤ _ := hlang
    _ ≤ 10 ^ 6 * ((2 ^ r.p.k * ((10 ^ 5 + 1) * (X + 1) ^ 4)) *
          ((a1 * 2 ^ c1 + a1 + c1 + T + 3) * (X + 1) ^ c1) ^ 2) := by gcongr
    _ = _ := by ring

/-- **The cost class, uniform in `cT`.** -/
theorem prefixBudget_class (B1 B2 : ℕ) : ∃ C e : ℕ, ∀ (cT : ℕ) (r : CellReq B1 B2 cT),
    prefixBudget B1 B2 cT r ≤ C * 2 ^ r.p.k * ((cellInput r).length + 1) ^ e :=
  ⟨_, _, fun _ r => budget_bound (16 * (2 ^ 19 + 1) ^ 2) (2 * (B1 + B2 + 13)) (by omega) r⟩

/-! ## The prefix machine -/

@[irreducible] noncomputable def prefixMachine (B1 B2 cT : ℕ) : PrefixMachine B1 B2 cT where
  budget := prefixBudget B1 B2 cT
  wf := prefixWF B1 B2 cT
  cls := by
    obtain ⟨C, e, h⟩ := prefixBudget_class B1 B2
    exact ⟨C, e, h cT⟩

theorem prefixMachine_budget (B1 B2 cT : ℕ) : (prefixMachine B1 B2 cT).budget = prefixBudget B1 B2 cT := by
  unfold prefixMachine; rfl

theorem prefixMachine_uniform (B1 B2 : ℕ) :
    ∃ e : ℕ, ∀ cT : ℕ, ∃ C : ℕ, ∀ r : CellReq B1 B2 cT,
      (prefixMachine B1 B2 cT).budget r ≤ C * 2 ^ r.p.k * ((cellInput r).length + 1) ^ e := by
  obtain ⟨C, e, h⟩ := prefixBudget_class B1 B2
  exact ⟨e, fun cT => ⟨C, fun r => by rw [prefixMachine_budget]; exact h cT r⟩⟩

end NearCubicGates.Close.CounterMachine.PrefixProg
