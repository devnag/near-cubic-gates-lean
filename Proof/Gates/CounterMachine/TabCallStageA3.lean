import Proof.Gates.CounterMachine.TabCallBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable (tP tK : ℕ) {B1 B2 cT : ℕ}

/-- `X 5 := q − 1` (residue requests, tag `0`) or `X 10 := j`. -/
def qjP : WM (NS tP tK) NR :=
  .ifr (Td 0) (copyR (Td 2) (X 10) (E 20)) (.seq (copyR (Td 2) (X 5) (E 20)) (.dec (X 5)))

/-- The register value written by `qjP`. -/
def qjReg (tag : ℕ) : Fin NR := if tag = 0 then X 5 else X 10
def qjVal (tag v : ℕ) : ℕ := if tag = 0 then v - 1 else v

@[simp] theorem qjReg_val (t : ℕ) : (qjReg t).val = if t = 0 then 5 else 10 := by
  unfold qjReg; split_ifs <;> rfl

theorem qjP_spec (σ : WState (NS tP tK) NR) (tag v cap : ℕ) (h0 : σ.val (Td 0) = tag) (h2 : σ.val (Td 2) = v)
    (h5 : σ.val (X 5) = 0) (h10 : σ.val (X 10) = 0) (h20 : σ.val (E 20) = 0) (hc : v + 1 ≤ cap) :
    WExec cap (qjP tP tK) σ (σ.setv (qjReg tag) (qjVal tag v)) (18 * v + 10) := by
  by_cases ht : tag = 0
  · have e1 := copyR_spec cap (v := Td 2) (d := X 5) (t := E 20) (by lne) (by lne) (by lne) σ h20 (by omega)
    rw [h5, h2, Nat.zero_add] at e1
    have e2 := WExec.dec (cap := cap) (X 5) (σ.setv (X 5) v) (by simp; omega)
    refine WExec.cast cap (WExec.ifrF (by rw [h0, ht]) (WExec.seq e1 e2)) ?_ (by omega)
    simp [qjReg, qjVal, ht, wsetv_setv]
  · have e1 := copyR_spec cap (v := Td 2) (d := X 10) (t := E 20) (by lne) (by lne) (by lne) σ h20 (by omega)
    rw [h10, h2, Nat.zero_add] at e1
    exact WExec.cast cap (WExec.ifrT (by rw [h0]; exact ht) e1) (by simp [qjReg, qjVal, ht]) (by omega)

/-- The bound registers. -/
def bndRegs : List (Fin NR) := [X 6, X 7, X 16, X 17, X 20, X 21]

def stA3a : WM (NS tP tK) NR :=
  .seq (rcP (X 0) (X 1) (X 11) (E 20) (E 22)) (.seq (copyR (X 14) (X 19) (E 20)) (.seq (copyR (E 3) (X 22) (E 20))
    (.seq (copyR (E 3) (X 22) (E 20)) (.seq (qjP tP tK) (cpyL (E 19) (E 20) bndRegs)))))

theorem stA3a_spec (x : TabCallReq B1 B2 cT) (cap : ℕ) (σ : WState (NS tP tK) NR) (hA : A2 tP tK x σ)
    (hc : 2 * (x.r.p.J + 1) + 2 * x.r.p.k + x.r.c.first.gates.length + dF2 x.id + 2 * (tabCallInput x).length + 10 ≤ cap) :
    ∃ τ, WExec cap (stA3a tP tK) σ τ (300 * (x.r.p.J + x.r.p.k + x.r.c.first.gates.length + dF2 x.id +
        (tabCallInput x).length + 1)) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.val (X 11) = ((if x.r.c.kind = .pair then 1 else 0) + 1) * (x.r.p.J + 1) ∧
      τ.val (X 19) = x.r.c.first.gates.length ∧ τ.val (X 22) = 2 * x.r.p.k ∧
      τ.val (qjReg (dTag x.id)) = qjVal (dTag x.id) (dF2 x.id) ∧ (∀ d ∈ bndRegs, τ.val d = 2 * (tabCallInput x).length) ∧
      (∀ r, r ∉ [X 11, X 19, X 22, qjReg (dTag x.id), X 6, X 7, X 16, X 17, X 20, X 21] → τ.val r = σ.val r) := by
  have z : ∀ r, r ∉ [X 0, X 1, X 8, X 14, X 18, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15] →
    σ.val r = 0 := hA.regs
  have hf1 : (if x.r.c.kind = .pair then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have e1 := rcP_spec cap (X 0) (X 1) (X 11) (E 20) (E 22) (by simp [List.nodup_cons]; decide) σ _ x.r.p.J hA.flag
    hf1 hA.vJ (z _ (by lnm)) (z _ (by lnm)) (z _ (by lnm)) (by omega)
  set f := (if x.r.c.kind = .pair then 1 else 0) with hf
  set σ1 := σ.setv (X 11) ((f + 1) * (x.r.p.J + 1)) with hσ1
  have v1 : ∀ r, r ≠ X 11 → σ1.val r = σ.val r := fun r h => by simp [hσ1, Function.update_of_ne h]
  have e2 := copyR_spec cap (v := X 14) (d := X 19) (t := E 20) (by lne) (by lne) (by lne) σ1
    (by rw [v1 _ (by lne)]; exact z _ (by lnm)) (by rw [v1 _ (by lne), v1 _ (by lne), z _ (by lnm), hA.vG0]; omega)
  rw [v1 _ (by lne), v1 _ (by lne), z (X 19) (by lnm), hA.vG0, Nat.zero_add] at e2
  set σ2 := σ1.setv (X 19) x.r.c.first.gates.length with hσ2
  have v2 : ∀ r, r ≠ X 11 → r ≠ X 19 → σ2.val r = σ.val r := fun r h1 h2 => by
    simp [hσ2, Function.update_of_ne h2]; exact v1 r h1
  have e3 := copyR_spec cap (v := E 3) (d := X 22) (t := E 20) (by lne) (by lne) (by lne) σ2
    (by rw [v2 _ (by lne) (by lne)]; exact z _ (by lnm))
    (by rw [v2 _ (by lne) (by lne), v2 _ (by lne) (by lne), z _ (by lnm), hA.vk]; omega)
  rw [v2 _ (by lne) (by lne), v2 _ (by lne) (by lne), z (X 22) (by lnm), hA.vk, Nat.zero_add] at e3
  set σ3 := σ2.setv (X 22) x.r.p.k with hσ3
  have e4 := copyR_spec cap (v := E 3) (d := X 22) (t := E 20) (by lne) (by lne) (by lne) σ3
    (by simp [hσ3, Function.update_of_ne (show E 20 ≠ X 22 by lne)]; rw [v2 _ (by lne) (by lne)]; exact z _ (by lnm))
    (by simp [hσ3, Function.update_of_ne (show E 3 ≠ X 22 by lne)]; rw [v2 _ (by lne) (by lne), hA.vk]; omega)
  have v3e : σ3.val (E 3) = x.r.p.k := by
    simp [hσ3, Function.update_of_ne (show E 3 ≠ X 22 by lne)]; rw [v2 _ (by lne) (by lne), hA.vk]
  rw [v3e, show σ3.val (X 22) = x.r.p.k by simp [hσ3]] at e4
  set σ4 := σ3.setv (X 22) (x.r.p.k + x.r.p.k) with hσ4
  have v4 : ∀ r, r ≠ X 11 → r ≠ X 19 → r ≠ X 22 → σ4.val r = σ.val r := fun r h1 h2 h3 => by
    simp [hσ4, hσ3, Function.update_of_ne h3]; exact v2 r h1 h2
  have e5 := qjP_spec tP tK σ4 (dTag x.id) (dF2 x.id) cap (by rw [v4 _ (by lne) (by lne) (by lne)]; exact hA.t0)
    (by rw [v4 _ (by lne) (by lne) (by lne)]; exact hA.t2) (by rw [v4 _ (by lne) (by lne) (by lne)]; exact z _ (by lnm))
    (by rw [v4 _ (by lne) (by lne) (by lne)]; exact z _ (by lnm))
    (by rw [v4 _ (by lne) (by lne) (by lne)]; exact z _ (by lnm)) (by omega)
  set σ5 := σ4.setv (qjReg (dTag x.id)) (qjVal (dTag x.id) (dF2 x.id)) with hσ5
  have hq : qjReg (dTag x.id) = X 5 ∨ qjReg (dTag x.id) = X 10 := by unfold qjReg; split_ifs <;> simp
  have v5' : ∀ r, r ≠ X 11 → r ≠ X 19 → r ≠ X 22 → r ≠ qjReg (dTag x.id) → σ5.val r = σ.val r :=
    fun r h1 h2 h3 h4 => by simp [hσ5, Function.update_of_ne h4]; exact v4 r h1 h2 h3
  have v5 : ∀ r, r ≠ X 11 → r ≠ X 19 → r ≠ X 22 → r ≠ X 5 → r ≠ X 10 → σ5.val r = σ.val r := fun r h1 h2 h3 h4 h5 => by
    have : r ≠ qjReg (dTag x.id) := by rcases hq with h | h <;> rw [h] <;> assumption
    exact v5' r h1 h2 h3 this
  obtain ⟨τ, e6, h6a, h6b, h6c, h6d⟩ := cpyL_spec cap (E 19) (E 20) (by lne) bndRegs σ5 (by simp [bndRegs])
    (fun d hd => by
      simp only [bndRegs, List.mem_cons, List.not_mem_nil, or_false] at hd
      have hb : d ≠ E 19 ∧ d ≠ E 20 ∧ d ≠ X 11 ∧ d ≠ X 19 ∧ d ≠ X 22 ∧ d ≠ X 5 ∧ d ≠ X 10 ∧ d ∉ [X 0, X 1, X 8, X 14,
          X 18, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15] := by
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by lne, by lne, by lne, by lne, by lne, by lne, by lne, by lnm⟩
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hb
      exact ⟨b1, b2, by rw [v5 _ b3 b4 b5 b6 b7]; exact z _ b8⟩)
    (by rw [v5 _ (by lne) (by lne) (by lne) (by lne) (by lne)]; exact z _ (by lnm))
    (by rw [v5 _ (by lne) (by lne) (by lne) (by lne) (by lne), hA.len]; omega)
  have hlen5 : σ5.val (E 19) = 2 * (tabCallInput x).length := by
    rw [v5 _ (by lne) (by lne) (by lne) (by lne) (by lne), hA.len]
  rw [hlen5] at e6 h6a
  refine ⟨τ, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_,
    by rw [h6c]; simp [hσ5, hσ4, hσ3, hσ2, hσ1], by rw [h6d]; simp [hσ5, hσ4, hσ3, hσ2, hσ1], ?_, ?_, ?_, ?_, h6a, ?_⟩
  · simp only [bndRegs, List.length_cons, List.length_nil]
    nlinarith
  · have q1 : X 11 ≠ qjReg (dTag x.id) := by rcases hq with h | h <;> rw [h] <;> lne
    rw [h6b _ (by simp only [bndRegs]; lnm)]
    simp only [hσ5, hσ4, hσ3, hσ2, hσ1, WState.setv_val]
    rw [Function.update_of_ne q1, Function.update_of_ne (show X 11 ≠ X 22 by lne),
      Function.update_of_ne (show X 11 ≠ X 22 by lne), Function.update_of_ne (show X 11 ≠ X 19 by lne),
      Function.update_self]
  · have q1 : X 19 ≠ qjReg (dTag x.id) := by rcases hq with h | h <;> rw [h] <;> lne
    rw [h6b _ (by simp only [bndRegs]; lnm)]
    simp only [hσ5, hσ4, hσ3, hσ2, WState.setv_val]
    rw [Function.update_of_ne q1, Function.update_of_ne (show X 19 ≠ X 22 by lne),
      Function.update_of_ne (show X 19 ≠ X 22 by lne), Function.update_self]
  · have q1 : X 22 ≠ qjReg (dTag x.id) := by rcases hq with h | h <;> rw [h] <;> lne
    rw [h6b _ (by simp only [bndRegs]; lnm)]
    simp only [hσ5, hσ4, WState.setv_val]
    rw [Function.update_of_ne q1, Function.update_self]; ring
  · rw [h6b _ (by simp only [bndRegs]; rcases hq with h | h <;> rw [h] <;> lnm)]; simp [hσ5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a1, a2, a3, a4, a6, a7, a8, a9, a10, a11⟩ := hr
    rw [h6b r (by simp only [bndRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
                  exact ⟨a6, a7, a8, a9, a10, a11⟩)]
    exact v5' r a1 a2 a3 a4

/-- RG's streams `Y 1 … Y 6`. -/
def ysL : List (Fin (NS tP tK + 1)) := [Y tP tK 1, Y tP tK 2, Y tP tK 3, Y tP tK 4, Y tP tK 5, Y tP tK 6]

def stA3b : WM (NS tP tK) NR := rwL (E 19) (E 22) (E 20) (ysL tP tK)

theorem stA3b_spec (x : TabCallReq B1 B2 cT) (cap : ℕ) (σ0 σ : WState (NS tP tK) NR) (hA : A2 tP tK x σ0)
    (hsh : σ.sh = σ0.sh) (hL : σ.val (E 19) = 2 * (tabCallInput x).length) (h20 : σ.val (E 20) = 0)
    (h22 : σ.val (E 22) = 0) (hc : 2 * (tabCallInput x).length ≤ cap) :
    ∃ τ, WExec cap (stA3b tP tK) σ τ (6 * (60 * (tabCallInput x).length + 10)) ∧ τ.st = σ.st ∧ τ.val = σ.val ∧
      (∀ y ∈ ysL tP tK, τ.sh y = 0) ∧ (∀ y, y ∉ ysL tP tK → τ.sh y = σ.sh y) := by
  have hb := streams_le x
  simp only [allN] at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  have hle := len_eq x
  obtain ⟨τ, e, h1, h2, h3, h4⟩ := rwL_spec cap (E 19) (E 22) (E 20) (by lne) (by lne) (by lne) (ysL tP tK) σ h22 h20
    (fun y hy => by
      rw [hL, hsh]
      simp only [ysL, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hA.yh 1 (by decide) (by decide), hA.y1]; omega
      · rw [hA.yh 2 (by decide) (by decide), hA.y2]; omega
      · rw [hA.yh 3 (by decide) (by decide), hA.y3]; omega
      · rw [hA.yh 4 (by decide) (by decide), hA.y4]; omega
      · rw [hA.yh 5 (by decide) (by decide), hA.y5]; omega
      · rw [hA.yh 6 (by decide) (by decide), hA.y6]; omega) (by rw [hL]; exact hc)
  rw [hL] at e
  exact ⟨τ, WExec.mono e (by simp [ysL]; omega), h3, h4, h1, h2⟩

def stA3c (Cl El : ℕ) : WM (NS tP tK) NR :=
  .seq (copyR (E 0) (Gl 3) (E 20)) (.seq (copyR (E 3) (E 23) (E 20)) (.seq (Codec.repLoop (E 23) (.dec (Gl 3)))
    (.seq (copyR (E 0) (Gl 4) (E 20)) (.seq (.inc (Gl 4)) (logP Gl (sLOG tP tK) Cl El)))))

/-- The log length. -/
def lcap (Cl El n k : ℕ) : ℕ := Cl * 2 ^ (n - k) * (n + 1) ^ El

theorem stA3c_spec (Cl El n k cap : ℕ) (σ : WState (NS tP tK) NR) (hn : σ.val (E 0) = n) (hk : σ.val (E 3) = k)
    (hkn : k ≤ n) (hz : ∀ r ∈ [E 20, E 23, Gl 0, Gl 1, Gl 2, Gl 3, Gl 4, Gl 5], σ.val r = 0)
    (hL : σ.st (sLOG tP tK) = []) (hLh : σ.sh (sLOG tP tK) = 0)
    (hc : 4 * (lcap Cl El n k * (n + 1)) + 2 * n + 10 ≤ cap) :
    WExec cap (stA3c tP tK Cl El) σ
      ((σ.sets (sLOG tP tK) (List.replicate (lcap Cl El n k) false)).setv (Gl 4) (n + 1))
      (200 * (El + n + 1) * (lcap Cl El n k * (n + 1) + 1)) := by
  have z : ∀ r ∈ [E 20, E 23, Gl 0, Gl 1, Gl 2, Gl 3, Gl 4, Gl 5], σ.val r = 0 := hz
  have hl1 : 1 ≤ lcap Cl El n k * (n + 1) ∨ lcap Cl El n k = 0 := by
    rcases Nat.eq_zero_or_pos (lcap Cl El n k) with h | h
    · exact Or.inr h
    · exact Or.inl (by nlinarith)
  have e1 := copyR_spec cap (v := E 0) (d := Gl 3) (t := E 20) (by lne) (by lne) (by lne) σ (z _ (by simp))
    (by rw [z _ (by simp), hn]; omega)
  rw [z (Gl 3) (by simp), hn, Nat.zero_add] at e1
  set σ1 := σ.setv (Gl 3) n with hσ1
  have e2 := copyR_spec cap (v := E 3) (d := E 23) (t := E 20) (by lne) (by lne) (by lne) σ1
    (by simp [hσ1, Function.update_of_ne (show E 20 ≠ Gl 3 by lne)]; exact z _ (by simp))
    (by simp [hσ1, Function.update_of_ne (show E 23 ≠ Gl 3 by lne), Function.update_of_ne (show E 3 ≠ Gl 3 by lne)]
        rw [z _ (by simp), hk]; omega)
  have v13 : σ1.val (E 3) = k := by simp [hσ1, Function.update_of_ne (show E 3 ≠ Gl 3 by lne), hk]
  have v123 : σ1.val (E 23) = 0 := by
    simp [hσ1, Function.update_of_ne (show E 23 ≠ Gl 3 by lne)]; exact z _ (by simp)
  rw [v13, v123, Nat.zero_add] at e2
  set σ2 := σ1.setv (E 23) k with hσ2
  have e3 := decLoop_spec cap (T := Gl 3) (t := E 23) σ2 k (by simp [hσ2])
    (by simp [hσ2, hσ1, Function.update_of_ne (show Gl 3 ≠ E 23 by lne)]; omega) (by lne) (by omega)
    (by simp [hσ2, hσ1, Function.update_of_ne (show Gl 3 ≠ E 23 by lne)]; omega)
  have v2 : σ2.val (Gl 3) = n := by simp [hσ2, hσ1, Function.update_of_ne (show Gl 3 ≠ E 23 by lne)]
  rw [v2] at e3
  set σ3 := (σ2.setv (Gl 3) (n - k)).setv (E 23) 0 with hσ3
  have v3 : ∀ r, r ≠ Gl 3 → r ≠ E 23 → σ3.val r = σ.val r := fun r a b => by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne a, Function.update_of_ne b]
  have e4 := copyR_spec cap (v := E 0) (d := Gl 4) (t := E 20) (by lne) (by lne) (by lne) σ3
    (by rw [v3 _ (by lne) (by lne)]; exact z _ (by simp))
    (by rw [v3 _ (by lne) (by lne), v3 _ (by lne) (by lne), z (Gl 4) (by simp), hn]; omega)
  rw [v3 _ (by lne) (by lne), v3 _ (by lne) (by lne), z (Gl 4) (by simp), hn, Nat.zero_add] at e4
  have e5 := WExec.inc (cap := cap) (Gl 4) (σ3.setv (Gl 4) n) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at e5
  rw [wsetv_setv] at e5
  set σ5 := σ3.setv (Gl 4) (n + 1) with hσ5
  have v5 : ∀ r, r ≠ Gl 3 → r ≠ E 23 → r ≠ Gl 4 → σ5.val r = σ.val r := fun r a b c => by
    simp [hσ5, Function.update_of_ne c]; exact v3 r a b
  have e6 := logP_spec cap Gl (sLOG tP tK) Cl El σ5 (n - k) (n + 1) (by omega)
    (by rw [v5 _ (by lne) (by lne) (by lne)]; exact z _ (by simp))
    (by rw [v5 _ (by lne) (by lne) (by lne)]; exact z _ (by simp))
    (by rw [v5 _ (by lne) (by lne) (by lne)]; exact z _ (by simp))
    (by simp [hσ5, hσ3, Function.update_of_ne (show Gl 3 ≠ Gl 4 by lne), Function.update_of_ne (show Gl 3 ≠ E 23 by lne)])
    (by simp [hσ5])
    (by rw [v5 _ (by lne) (by lne) (by lne)]; exact z _ (by simp))
    (by simp [hσ5, hσ3, hσ2, hσ1, hL]) (by simp [hσ5, hσ3, hσ2, hσ1, hLh])
    (by unfold lcap at hc; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · apply WState.eq
    · simp [hσ5, hσ3, hσ2, hσ1]
    · simp [hσ5, hσ3, hσ2, hσ1, lcap]
    · funext r
      by_cases r3 : r = Gl 3
      · subst r3; simp [Function.update_of_ne (show Gl 3 ≠ Gl 4 by lne)]; exact (z _ (by simp)).symm
      · by_cases r23 : r = E 23
        · subst r23
          simp [Function.update_of_ne (show E 23 ≠ Gl 3 by lne), Function.update_of_ne (show E 23 ≠ Gl 4 by lne),
            hσ5, hσ3]
          exact (z _ (by simp)).symm
        · by_cases r4 : r = Gl 4
          · subst r4; simp [Function.update_of_ne (show Gl 4 ≠ Gl 3 by lne), hσ5]
          · simp [Function.update_of_ne r3, Function.update_of_ne r4]
            exact v5 r r3 r23 r4
    · simp [hσ5, hσ3, hσ2, hσ1]
  · unfold lcap
    set M := Cl * 2 ^ (n - k) * (n + 1) ^ El
    have hB : 1 ≤ M * (n + 1) + 1 := by omega
    have h1 : 100 * (El + (n - k) + 1) * (M * (n + 1) + 1) ≤ 100 * (El + n + 1) * (M * (n + 1) + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have h2 : 100 * (El + n + 1) ≤ 100 * (El + n + 1) * (M * (n + 1) + 1) := Nat.le_mul_of_pos_right _ hB
    have h3 : 200 * (El + n + 1) * (M * (n + 1) + 1) = 100 * (El + n + 1) * (M * (n + 1) + 1) +
        100 * (El + n + 1) * (M * (n + 1) + 1) := by ring
    rw [h3]
    have : k * (1 + 4) + 1 ≤ 5 * n + 1 := by nlinarith
    omega

end NearCubicGates.Close.CounterMachine.TabCallProg
