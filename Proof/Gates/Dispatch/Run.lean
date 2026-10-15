import Proof.Gates.Dispatch.Setup
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {V : ℕ}

theorem teardown_spec (C : Ctx) (inp : List Bool) (p0 cap : ℕ) (b : DS V)
    (h1 : b.out.length ≤ cap) (h2 : p0 + 4 * b.wq ≤ cap) (h3 : b.cp ≤ cap) :
    ∃ τ, WXExec cap (teardownP (V := V)) (E C inp p0 b) τ
        (5 * b.out.length + 1 + 1 + (5 * (p0 + 4 * b.wq) + 1 + 1 + (5 * b.cp + 1))) ∧
      τ.st sOUT = b.out ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0 := by
  have t1 := rewind_spec (V := V) cap sOUT rOP b.out.length (E C inp p0 b) (by simp) (by simp) h1
  set τ1 := ((E C inp p0 b).setv rOP 0).seth sOUT 0 with hτ1
  have t2 := rewind_spec (V := V) cap sIN rIP (p0 + 4 * b.wq) τ1 (by simp [hτ1]) (by simp [hτ1]) h2
  set τ2 := (τ1.setv rIP 0).seth sIN 0 with hτ2
  have t3 := rewind_spec (V := V) cap sCW rCP b.cp τ2 (by simp [hτ2, hτ1]) (by simp [hτ2, hτ1]) h3
  refine ⟨_, WXExec.seq t1 (WXExec.seq t2 t3), by simp [hτ2, hτ1], ?_, ?_⟩
  · intro i
    simp only [WState.seth_sh, WState.setv_sh, hτ2, hτ1]
    by_cases hc : i = sCW
    · subst hc; simp
    · rw [Function.update_of_ne hc]
      by_cases hn : i = sIN
      · subst hn; simp
      · rw [Function.update_of_ne hn]
        by_cases ho : i = sOUT
        · subst ho; simp
        · rw [Function.update_of_ne ho]
          have h0 : i.val ≠ 0 := fun e => hn (Fin.ext e)
          have h1' : i.val ≠ 1 := fun e => ho (Fin.ext e)
          have h2' : i.val ≠ 2 := fun e => hc (Fin.ext e)
          simp [E, shF, h0, h1', h2']
  · intro q
    simp only [WState.seth_val, WState.setv_val, hτ2, hτ1]
    by_cases hc : q = rCP
    · subst hc; simp
    · rw [Function.update_of_ne hc]
      by_cases hn : q = rIP
      · subst hn; simp
      · rw [Function.update_of_ne hn]
        by_cases ho : q = rOP
        · subst ho; simp
        · rw [Function.update_of_ne ho]
          have h5 : q.val ≠ 5 := fun e => hc (Fin.ext e)
          have h6 : q.val ≠ 6 := fun e => hn (Fin.ext e)
          have h7 : q.val ≠ 7 := fun e => ho (Fin.ext e)
          simp [E, valF, h5, h6, h7]

/-- **The whole run.** -/
theorem prog_spec (K : ℕ) (hK : 1 ≤ K) (main : St V) (cw wit : List Bool) {b : DS V} {n : ℕ}
    (h : Ex (ctxOf K cw wit) main a0 b n) (m : ℕ) (hnm : n ≤ m) :
    ∃ τ, WXExec (capOf K cw wit m) (prog K main) (Interfaces.startState (V + 3) NR (frame cw ++ frame wit)) τ
      (budgetOf V K cw.length m) ∧ τ.st sOUT = b.out ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0 := by
  obtain ⟨c, hc, hs⟩ := setup_spec (V := V) K hK cw wit m
  have hW1 : 1 ≤ wdOf K cw.length := Nat.one_le_pow _ _ (by omega)
  have hWL : cw.length ≤ wdOf K cw.length := le_trans (by omega) (Nat.le_self_pow (by norm_num) (cw.length + K))
  have hcap : 2 * wdOf K cw.length + 4 * (cw.length + wit.length) + m + 100 = capOf K cw wit m := rfl
  have hval0 : Valid (ctxOf K cw wit) (a0 (V := V)) :=
    ⟨fun x => by simp [a0], by simp [a0], by simp [a0]⟩
  have hb := h.valid hW1 hval0
  have hlo := h.out_len
  have hwq := h.wq_le
  simp only [a0, List.length_nil, Nat.zero_add] at hlo hwq
  obtain ⟨r1, _⟩ := comp_ok (ctxOf K cw wit) (inpOf cw wit) (p0Of cw) (capOf K cw wit m) (inp_layout cw wit) hW1 hWL
    (by rw [← hcap]; simp [ctxOf]; omega) (by rw [← hcap]; simp [ctxOf]; omega)
    (by rw [← hcap]; simp [ctxOf, p0Of]; omega) h hval0 (by rw [← hcap]; simp [a0]; omega)
  have eW : (ctxOf K cw wit).Wd = wdOf K cw.length := rfl
  rw [eW] at r1
  have hwqW := hb.wq_le
  have hcpW := hb.cp_le
  simp only [ctxOf] at hwqW hcpW
  obtain ⟨τ, ht, hout, hsh, hval⟩ := teardown_spec (ctxOf K cw wit) (inpOf cw wit) (p0Of cw) (capOf K cw wit m) b
    (by rw [← hcap]; omega) (by rw [← hcap]; unfold p0Of; omega) (by rw [← hcap]; omega)
  refine ⟨τ, WXExec.seq' _ hs (WXExec.seq' _ r1 ht le_rfl) ?_, hout, hsh, hval⟩
  unfold budgetOf p0Of
  have hk : n * KC (wdOf K cw.length) ≤ m * KC (wdOf K cw.length) := Nat.mul_le_mul_right _ hnm
  omega

/-! ## Packaging -/

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- **The dispatch machine from a language program.** -/
noncomputable def dispatchMachineOf (B1 B2 cT K : ℕ) (hK : 1 ≤ K) (main : St V) (N : ℕ → ℕ)
    (hmain : ∀ (c : Call) (w : List Bool), ∃ b n, Ex (ctxOf K (callWord c) w) main a0 b n ∧
      b.out = dispatchWord B1 B2 cT c w ∧ n ≤ N (callWord c).length)
    (hN : ∃ C e : ℕ, ∀ L, N L ≤ C * (L + 1) ^ e) : DispatchMachine B1 B2 cT where
  budget := fun c _ => budgetOf V K (callWord c).length (N (callWord c).length)
  wf := wordFunction_of_wmx (prog K main) sOUT (by simp) (fun r => capOf K (callWord r.1) r.2 (N (callWord r.1).length))
    (by
      intro r
      obtain ⟨b, n, hex, hout, hn⟩ := hmain r.1 r.2
      obtain ⟨τ, hrun, hst, hsh, hval⟩ := prog_spec K hK main (callWord r.1) r.2 hex _ hn
      exact ⟨τ, hrun, by rw [hst, hout], hsh, hval⟩)
  cls := by
    obtain ⟨C, e, hC⟩ := hN
    refine ⟨200 * (V + 2) * (K + 1) ^ 4 + C * (500 * (2 * (K + 1) ^ 4) ^ 2) + 30 * C + 400, e + 8, ?_⟩
    intro c w
    set L := (callWord c).length
    have hL1 : 1 ≤ (L + 1) := by omega
    have hP : ∀ k, (L + 1) ^ k ≤ (L + 1) ^ (e + 8) → True := fun _ _ => trivial
    have hNe := hC L
    -- the pieces
    have hX : L + K + 1 ≤ (K + 1) * (L + 1) := by nlinarith
    have hs : setupCost V K L ≤ 200 * (V + 2) * (K + 1) ^ 4 * (L + 1) ^ 4 := by
      unfold setupCost
      have := Nat.pow_le_pow_left hX 4
      rw [mul_pow] at this
      calc 200 * (V + 2) * (L + K + 1) ^ 4 ≤ 200 * (V + 2) * ((K + 1) ^ 4 * (L + 1) ^ 4) :=
            Nat.mul_le_mul_left _ this
        _ = 200 * (V + 2) * (K + 1) ^ 4 * (L + 1) ^ 4 := by ring
    have hWd : wdOf K L + 1 ≤ 2 * (K + 1) ^ 4 * (L + 1) ^ 4 := by
      unfold wdOf
      have h1 := Nat.pow_le_pow_left (show L + K ≤ (K + 1) * (L + 1) by nlinarith) 4
      rw [mul_pow] at h1
      have h2 : 1 ≤ (K + 1) ^ 4 * (L + 1) ^ 4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have hKC : KC (wdOf K L) ≤ 500 * (2 * (K + 1) ^ 4) ^ 2 * (L + 1) ^ 8 := by
      unfold KC
      have := Nat.pow_le_pow_left hWd 2
      calc 500 * (wdOf K L + 1) ^ 2 ≤ 500 * (2 * (K + 1) ^ 4 * (L + 1) ^ 4) ^ 2 := Nat.mul_le_mul_left _ this
        _ = 500 * (2 * (K + 1) ^ 4) ^ 2 * (L + 1) ^ 8 := by ring
    have hmono : ∀ k, k ≤ e + 8 → (L + 1) ^ k ≤ (L + 1) ^ (e + 8) := fun k hk => Nat.pow_le_pow_right hL1 hk
    have hp4 := hmono 4 (by omega)
    have hp1 := hmono 1 (by omega)
    have hp0 := hmono 0 (by omega)
    have hNK : N L * KC (wdOf K L) ≤ C * (500 * (2 * (K + 1) ^ 4) ^ 2) * (L + 1) ^ (e + 8) := by
      calc N L * KC (wdOf K L) ≤ (C * (L + 1) ^ e) * (500 * (2 * (K + 1) ^ 4) ^ 2 * (L + 1) ^ 8) :=
            Nat.mul_le_mul hNe hKC
        _ = C * (500 * (2 * (K + 1) ^ 4) ^ 2) * (L + 1) ^ (e + 8) := by ring
    have hN30 : 30 * N L ≤ 30 * C * (L + 1) ^ (e + 8) := by
      have := hmono e (by omega)
      calc 30 * N L ≤ 30 * (C * (L + 1) ^ e) := Nat.mul_le_mul_left _ hNe
        _ ≤ 30 * (C * (L + 1) ^ (e + 8)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
        _ = 30 * C * (L + 1) ^ (e + 8) := by ring
    have hs' : setupCost V K L ≤ 200 * (V + 2) * (K + 1) ^ 4 * (L + 1) ^ (e + 8) :=
      le_trans hs (Nat.mul_le_mul_left _ hp4)
    have hL' : 50 * L + 300 ≤ 400 * (L + 1) ^ (e + 8) := by
      have : L + 1 ≤ (L + 1) ^ (e + 8) := by simpa using hp1
      omega
    show budgetOf V K L (N L) ≤ _
    unfold budgetOf
    nlinarith

end NearCubicGates.Close.Dispatch
