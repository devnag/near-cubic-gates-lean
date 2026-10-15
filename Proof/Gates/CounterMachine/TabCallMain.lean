import Proof.Gates.CounterMachine.TabCallFormula
import Proof.Gates.CounterMachine.TabCallSel

/-! # RK, part 13: the whole stage A (from the cold start to RG's state and the blank log) -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable (tP tK : ℕ) {B1 B2 cT : ℕ}

/-- Stage A. -/
def stA (Cl El : ℕ) : WM (NS tP tK) NR :=
  .seq (stA1 tP tK) (.seq (.seq (unCP Q (uS tP tK) uR) (.seq (pidxP (Td 0) (Td 1) (E 1) (E 21) (E 20) (E 22))
    (unFW Q (uS tP tK) uR))) (.seq (stA3a tP tK) (.seq (stA3b tP tK) (stA3c tP tK Cl El))))

structure D3 (x : TabCallReq B1 B2 cT) (Cl El : ℕ) (σ τ : WState (NS tP tK) NR) : Prop where
  st : τ.st = Function.update σ.st (sLOG tP tK) (List.replicate (lcap Cl El x.r.c.n x.r.p.k) false)
  shY : ∀ y ∈ ysL tP tK, τ.sh y = 0
  sh : ∀ y, y ∉ ysL tP tK → τ.sh y = σ.sh y
  v11 : τ.val (X 11) = ((if x.r.c.kind = .pair then 1 else 0) + 1) * (x.r.p.J + 1)
  v19 : τ.val (X 19) = x.r.c.first.gates.length
  v22 : τ.val (X 22) = 2 * x.r.p.k
  vq : τ.val (qjReg (dTag x.id)) = qjVal (dTag x.id) (dF2 x.id)
  vb : ∀ d ∈ bndRegs, τ.val d = 2 * (tabCallInput x).length
  vG4 : τ.val (Gl 4) = x.r.c.n + 1
  vo : ∀ r, r ∉ [X 11, X 19, X 22, qjReg (dTag x.id), X 6, X 7, X 16, X 17, X 20, X 21, Gl 4] → τ.val r = σ.val r

/-- The step count of stage A. -/
def costA (x : TabCallReq B1 B2 cT) (Λ Cl El : ℕ) : ℕ :=
  (60 * (tabCallInput x).length + 10 + 1 + (400 * (Λ + 1) ^ 3 + 1 + (100 * (cellInput x.r).length + 30))) + 1 +
  ((30000 * (Λ + 1) ^ 2 + 23 * ((encN (dRho x.id)).length +
      (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt ++ [])).length)) + 1 +
    ((40 * (dF1 x.id + kindTag x.r.c.kind + 1) + 20) + 1 + 2100 * (Λ + 1) ^ 3)) + 1 +
  (300 * (x.r.p.J + x.r.p.k + x.r.c.first.gates.length + dF2 x.id + (tabCallInput x).length + 1) + 1 +
    (6 * (60 * (tabCallInput x).length + 10) + 1 +
      200 * (El + x.r.c.n + 1) * (lcap Cl El x.r.c.n x.r.p.k * (x.r.c.n + 1) + 1)))

theorem stA_spec (x : TabCallReq B1 B2 cT) (Λ cap Cl El : ℕ)
    (hb1 : ∀ v ∈ descN x.id, natBitLength v + 2 ≤ Λ ∧ 2 ^ (natBitLength v + 1) ≤ Λ)
    (hbits : ∀ y ∈ descN x.id ++ cellN x.r.c x.r.p x.r.wt, natBitLength y + 2 ≤ Λ)
    (hlen : (descN x.id ++ cellN x.r.c x.r.p x.r.wt).length ≤ Λ)
    (hRd1 : ∀ v ∈ [x.r.c.n, kindTag x.r.c.kind, x.r.c.first.gates.length, x.r.c.first.coeffs.length,
      x.r.c.first.table.length, x.r.c.second.gates.length, x.r.c.second.coeffs.length, x.r.c.second.table.length,
      x.r.c.parity.length], 2 ^ (natBitLength v + 1) ≤ Λ) (hn : 2 * x.r.c.n + 3 ≤ Λ)
    (hRd2 : ∀ v ∈ [x.r.p.k, x.r.p.P, x.r.p.e, x.r.p.J, (x.r.p.primes.sort (· ≤ ·)).length, x.r.p.factors.length],
      2 ^ (natBitLength v + 1) ≤ Λ)
    (hRd3 : 2 ^ (natBitLength (coordsOf x.r.wt.I).length + 1) ≤ Λ ∧ ∀ s < x.r.p.J,
      2 ^ (natBitLength (x.r.wt.coef s 0).length + 1) ≤ Λ ∧ 2 ^ (natBitLength (x.r.wt.coef s 1).length + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 20 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length +
      4 * (tabCallInput x).length + Λ + (encN (dRho x.id)).length + 10 ≤ cap)
    (hsm : dF1 x.id + kindTag x.r.c.kind + 3 ≤ cap)
    (hc3a : 2 * (x.r.p.J + 1) + 2 * x.r.p.k + x.r.c.first.gates.length + dF2 x.id + 2 * (tabCallInput x).length + 10 ≤ cap)
    (hc3c : 4 * (lcap Cl El x.r.c.n x.r.p.k * (x.r.c.n + 1)) + 2 * x.r.c.n + 10 ≤ cap) (hkn : x.r.p.k ≤ x.r.c.n) :
    ∃ σ2 τ, WExec cap (stA tP tK Cl El) (startState (NS tP tK) NR (tabCallInput x)) τ (costA x Λ Cl El) ∧
      A2 tP tK x σ2 ∧ D3 tP tK x Cl El σ2 τ := by
  have hlen1 : (descN x.id).length ≤ Λ := le_trans (by simp) hlen
  obtain ⟨τ1, e1, h1⟩ := stA1_spec tP tK x Λ cap hb1 hlen1 (by omega)
  obtain ⟨τ2, e2, h2⟩ := ucp_spec tP tK x Λ cap τ1 h1 hbits hlen hRd1 hn hRd2 (by omega)
  obtain ⟨τ3, e3, h3⟩ := a2a_spec tP tK x cap τ1 τ2 h1 h2 hsm
  obtain ⟨τ4, e4, h4⟩ := a2_spec tP tK x Λ cap τ3 h3 hbits hlen hRd3 (by omega)
  obtain ⟨τ5, e5, s5, sh5, v11, v19, v22, vq, vb, vo⟩ := stA3a_spec tP tK x cap τ4 h4 hc3a
  have z5 : ∀ r, r ∉ [X 11, X 19, X 22, qjReg (dTag x.id), X 6, X 7, X 16, X 17, X 20, X 21] →
      r ∉ [X 0, X 1, X 8, X 14, X 18, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15] → τ5.val r = 0 :=
    fun r h h' => by rw [vo r h]; exact h4.regs r h'
  obtain ⟨τ6, e6, s6, v6, shY6, sh6⟩ := stA3b_spec tP tK x cap τ4 τ5 h4 sh5
    (by rw [vo _ (by lnm)]; exact h4.len) (z5 _ (by lnm) (by lnm)) (z5 _ (by lnm) (by lnm)) (by omega)
  have e7 := stA3c_spec tP tK Cl El x.r.c.n x.r.p.k cap τ6 (by rw [v6, vo _ (by lnm)]; exact h4.vn)
    (by rw [v6, vo _ (by lnm)]; exact h4.vk) hkn
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [v6]; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact z5 _ (by lnm) (by lnm))
    (by rw [s6, s5]; exact (h4.other _ (by lnm)).1)
    (by rw [sh6 _ (by simp only [ysL]; lnm), sh5]; exact (h4.other _ (by lnm)).2) hc3c
  have E := WExec.seq e1 (WExec.seq (WExec.seq e2 (WExec.seq e3 e4)) (WExec.seq e5 (WExec.seq e6 e7)))
  rw [h1.q15] at E
  have hqne : ∀ d, d ∈ bndRegs → d ≠ Gl 4 := fun d hd => by
    simp only [bndRegs, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> lne
  have hq4 : qjReg (dTag x.id) ≠ Gl 4 := by unfold qjReg; split_ifs <;> lne
  refine ⟨τ4, _, WExec.mono E (by unfold costA; omega), h4, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [WState.setv_st, WState.sets_st]; rw [s6, s5]
  · intro y hy; simp only [WState.setv_sh, WState.sets_sh]; exact shY6 y hy
  · intro y hy; simp only [WState.setv_sh, WState.sets_sh]; rw [sh6 y hy, sh5]
  · simp only [WState.setv_val, WState.sets_val]; rw [Function.update_of_ne (by lne), v6]; exact v11
  · simp only [WState.setv_val, WState.sets_val]; rw [Function.update_of_ne (by lne), v6]; exact v19
  · simp only [WState.setv_val, WState.sets_val]; rw [Function.update_of_ne (by lne), v6]; exact v22
  · simp only [WState.setv_val, WState.sets_val]; rw [Function.update_of_ne hq4, v6]; exact vq
  · intro d hd; simp only [WState.setv_val, WState.sets_val]; rw [Function.update_of_ne (hqne d hd), v6]; exact vb d hd
  · simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a1, a2, a3, a4, a6, a7, a8, a9, a10, a11, a12⟩ := hr
    simp only [WState.setv_val, WState.sets_val]; rw [Function.update_of_ne a12, v6]
    exact vo r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                   exact ⟨a1, a2, a3, a4, a6, a7, a8, a9, a10, a11⟩)

end NearCubicGates.Close.CounterMachine.TabCallProg
