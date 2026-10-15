import Proof.Wire_3_5.OutMachineP3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.P4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass.Out.Half NearCubicWires.WireExponent3_5.FinalPass.Out.P1
open NearCubicWires.WireExponent3_5.FinalPass.Out.P3 (fb)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (addB oneB shlB subB addB_spec oneB_spec shlB_spec subB_spec)

/-! ## The arithmetic -/

theorem q_half (q i W : ℕ) (h : i < W) : q % 2 ^ i * 2 ^ (W - i) / 2 = q % 2 ^ i * 2 ^ (W - (i + 1)) := by
  have e : 2 ^ (W - i) = 2 ^ (W - (i + 1)) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [e, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by norm_num)]

theorem q_next (q i W : ℕ) (h : i < W) :
    q % 2 ^ (i + 1) * 2 ^ (W - (i + 1)) = q % 2 ^ i * 2 ^ (W - (i + 1)) + q / 2 ^ i % 2 * 2 ^ (W - 1) := by
  rw [Nat.mod_pow_succ, Nat.add_mul]
  congr 1
  have e : 2 ^ (W - 1) = 2 ^ i * 2 ^ (W - (i + 1)) := by rw [← pow_add]; congr 1; omega
  rw [e]; ring

theorem r_parity (g x : ℕ) (hg : g % 2 = 1) : g * x % 2 = x % 2 := by
  rw [Nat.mul_mod, hg, Nat.one_mul, Nat.mod_mod]

theorem r_odd (g x : ℕ) (hx : x % 2 = 1) : (g * x - g) / 2 = g * (x / 2) := by
  have e : x = 2 * (x / 2) + 1 := by omega
  have e2 : g * x = 2 * (g * (x / 2)) + g := by
    have := congrArg (g * ·) e
    rw [this, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  omega

theorem r_even (g x : ℕ) (hx : x % 2 = 0) : g * x / 2 = g * (x / 2) := by
  have e : x = 2 * (x / 2) := by omega
  have e2 : g * x = 2 * (g * (x / 2)) := by
    rw [Nat.mul_left_comm, ← e]
  omega

theorem qq_lt (q i W : ℕ) (h : i ≤ W) : q % 2 ^ i * 2 ^ (W - i) < 2 ^ W := by
  have h1 : q % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  have e : 2 ^ W = 2 ^ i * 2 ^ (W - i) := by rw [← pow_add]; congr 1; omega
  rw [e]
  exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)

theorem qh_lt (q i W : ℕ) (h : i < W) : q % 2 ^ i * 2 ^ (W - (i + 1)) + 2 ^ (W - 1) < 2 ^ W := by
  have h1 : q % 2 ^ i * 2 ^ (W - (i + 1)) < 2 ^ (W - 1) := by
    have := qq_lt q i (W - 1) (by omega)
    rwa [show W - 1 - i = W - (i + 1) by omega] at this
  have e : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
    rw [← Nat.two_mul, ← pow_succ']; congr 1; omega
  omega

/-! ## One round -/

/-- **One round**: `Q := Q/2`; if `R` is odd, `R −= g`, `Q += H`; `R := R/2`; `rK −= 1`. -/
def divBody (Rs Q : Fin (nsO + 1)) : WM nsO nrO :=
  .seq (halfW Q rR) (.seq (.fwd Rs) (.seq
    (.ifs Rs (.seq (.bwd Rs) (.seq (subB Rs sU rF rR) (addB Q (sX 5) rF rR))) (.bwd Rs))
    (.seq (halfW Rs rR) (.dec rK))))

theorem divBody_spec (Rs Q : Fin (nsO + 1)) (hRQ : Rs ≠ Q) (hRU : Rs ≠ sU) (hQU : Q ≠ sU) (hRH : Rs ≠ sX 5)
    (hQH : Q ≠ sX 5) (W g r qq m : ℕ) (σ : St) (hW : 1 ≤ W) (hRs : NumOn σ Rs W r) (hQ : NumOn σ Q W qq)
    (hG : NumOn σ sU W g) (hH : NumOn σ (sX 5) W (2 ^ (W - 1))) (hF : σ.val rF = 0) (hR : σ.val rR = 0)
    (hK : σ.val rK = m + 1) (hm : m + 1 ≤ W) (hr : r < 2 ^ W) (hq : qq < 2 ^ W) (hsub : r % 2 = 1 → g ≤ r)
    (hadd : r % 2 = 1 → qq / 2 + 2 ^ (W - 1) < 2 ^ W) :
    WExec (capO W) (divBody Rs Q) σ
      (((σ.sets Q (fb W (qq / 2 + if r % 2 = 1 then 2 ^ (W - 1) else 0))).sets Rs
        (fb W ((if r % 2 = 1 then r - g else r) / 2))).setv rK m) (150 * W + 28) := by
  have hc : 2 * W + 1 ≤ capO W := by unfold capO; omega
  have hFR : rF ≠ rR := by decide
  have s1 := halfW_spec (capO W) Q rR W qq σ hQ hR hq (by omega)
  set σ1 := σ.sets Q (fb W (qq / 2)) with hσ1
  have hRs1 : NumOn σ1 Rs W r := numOn_sets_ne _ _ _ _ hRQ hRs
  have s2 : WExec (capO W) (.fwd Rs) σ1 (σ1.seth Rs 1) 1 := by
    have e := WExec.fwd (cap := capO W) Rs σ1
    rwa [hRs1.2] at e
  have bR : wbit (σ1.seth Rs 1) Rs = (r % 2 == 1) := by
    unfold wbit
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, hRs1.1]
    exact bit0_frame W r hW
  have bk : WExec (capO W) (.bwd Rs) (σ1.seth Rs 1) σ1 1 := by
    have e := WExec.bwd (cap := capO W) Rs (σ1.seth Rs 1)
    rwa [wseth_sh_self, Nat.sub_self, wseth_seth, ← hRs1.2, wseth_same] at e
  by_cases hodd : r % 2 = 1
  · simp only [hodd, if_true]
    have sb := subB_spec (capO W) W hRU hFR σ1 r g hRs1 (numOn_sets_ne _ _ _ _ (Ne.symm hQU) hG) hF hR
      (hsub hodd) hr hc
    set σ2 := σ1.sets Rs (fb W (r - g)) with hσ2
    have sa := addB_spec (capO W) W hQH hFR σ2 (qq / 2) (2 ^ (W - 1))
      (numOn_sets_ne _ _ _ _ (Ne.symm hRQ) (numOn_sets_self σ Q W _ hQ.2))
      (numOn_sets_ne _ _ _ _ (Ne.symm hRH) (numOn_sets_ne _ _ _ _ (Ne.symm hQH) hH)) hF hR (hadd hodd) hc
    set σ3 := σ2.sets Q (fb W (qq / 2 + 2 ^ (W - 1))) with hσ3
    have hRs3 : NumOn σ3 Rs W (r - g) :=
      numOn_sets_ne _ _ _ _ hRQ (numOn_sets_self σ1 Rs W _ hRs1.2)
    have sh := halfW_spec (capO W) Rs rR W (r - g) σ3 hRs3 hR (by omega) (by omega)
    have hK3 : (σ3.sets Rs (fb W ((r - g) / 2))).val rK = m + 1 := by simp [hσ3, hσ2, hσ1, hK]
    have sd := WExec.dec (cap := capO W) rK (σ3.sets Rs (fb W ((r - g) / 2))) (by rw [hK3]; unfold capO; omega)
    rw [hK3, Nat.add_sub_cancel] at sd
    have b' : wbit (σ1.seth Rs 1) Rs = true := by rw [bR]; simp [hodd]
    refine WExec.cast (capO W) (WExec.seq s1 (WExec.seq s2 (WExec.seq (WExec.ifsT b' (WExec.seq bk (WExec.seq sb sa)))
      (WExec.seq sh sd)))) ?_ (by omega)
    refine WState.eq rfl ?_ rfl rfl
    funext j
    simp only [hσ3, hσ2, hσ1, WState.setv_st, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [hodd, if_false, Nat.add_zero]
    have sh := halfW_spec (capO W) Rs rR W r σ1 hRs1 hR hr (by omega)
    have hK1 : (σ1.sets Rs (fb W (r / 2))).val rK = m + 1 := by simp [hσ1, hK]
    have sd := WExec.dec (cap := capO W) rK (σ1.sets Rs (fb W (r / 2))) (by rw [hK1]; unfold capO; omega)
    rw [hK1, Nat.add_sub_cancel] at sd
    have b' : wbit (σ1.seth Rs 1) Rs = false := by rw [bR]; simp; omega
    exact WExec.cast (capO W) (WExec.seq s1 (WExec.seq s2 (WExec.seq (WExec.ifsF b' bk) (WExec.seq sh sd)))) rfl
      (by omega)

theorem q_new (q i W : ℕ) (g : ℕ) (hg : g % 2 = 1) (h : i < W) :
    q % 2 ^ i * 2 ^ (W - i) / 2 + (if g * (q / 2 ^ i) % 2 = 1 then 2 ^ (W - 1) else 0) =
      q % 2 ^ (i + 1) * 2 ^ (W - (i + 1)) := by
  rw [q_half q i W h, q_next q i W h, r_parity g _ hg]
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ i) with h2 | h2 <;> simp [h2]

theorem r_new (q i g : ℕ) (hg : g % 2 = 1) :
    (if g * (q / 2 ^ i) % 2 = 1 then g * (q / 2 ^ i) - g else g * (q / 2 ^ i)) / 2 = g * (q / 2 ^ (i + 1)) := by
  have e : q / 2 ^ (i + 1) = q / 2 ^ i / 2 := by rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [r_parity g _ hg, e]
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ i) with h2 | h2
  · simp only [h2]; simp only [show ¬ (0 = 1) by omega, if_false]; exact r_even g _ h2
  · simp only [h2, if_true]; exact r_odd g _ h2

/-- **`W` rounds**: `Q := q`, `R := 0`, from `R = g·(q/2^i)`, `Q = (q mod 2^i)·2^(W−i)`. -/
theorem divLoop_spec (Rs Q : Fin (nsO + 1)) (hRQ : Rs ≠ Q) (hRU : Rs ≠ sU) (hQU : Q ≠ sU) (hRH : Rs ≠ sX 5)
    (hQH : Q ≠ sX 5) (W g q : ℕ) (hW : 1 ≤ W) (hg : g % 2 = 1) (hgq : g * q < 2 ^ W) (hq : q < 2 ^ W) :
    ∀ (m i : ℕ) (σ : St), i + m = W → NumOn σ Rs W (g * (q / 2 ^ i)) → NumOn σ Q W (q % 2 ^ i * 2 ^ (W - i)) →
      NumOn σ sU W g → NumOn σ (sX 5) W (2 ^ (W - 1)) → σ.val rF = 0 → σ.val rR = 0 → σ.val rK = m →
      WExec (capO W) (.whr rK (divBody Rs Q)) σ (((σ.sets Q (fb W q)).sets Rs (fb W 0)).setv rK 0)
        (m * (150 * W + 30) + 1)
  | 0, i, σ, hi, hRs, hQ, _, _, _, _, hK => by
    have hiW : i = W := by omega
    rw [hiW, Nat.sub_self, pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hq] at hQ
    rw [hiW, Nat.div_eq_of_lt hq, Nat.mul_zero] at hRs
    refine WExec.cast (capO W) (WExec.whrF hK) ?_ (by omega)
    refine WState.eq rfl ?_ ?_ rfl
    · funext j
      simp only [WState.setv_st, WState.sets_st, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; exact hRs.1
      · subst h2; exact hQ.1
      · rfl
    · funext j
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs with h1
      · subst h1; exact hK
      · rfl
  | m + 1, i, σ, hi, hRs, hQ, hG, hH, hF, hR, hK => by
    have hiW : i < W := by omega
    have hr : g * (q / 2 ^ i) < 2 ^ W := lt_of_le_of_lt (Nat.mul_le_mul_left g (Nat.div_le_self q _)) hgq
    have body := divBody_spec Rs Q hRQ hRU hQU hRH hQH W g (g * (q / 2 ^ i)) (q % 2 ^ i * 2 ^ (W - i)) m σ hW hRs
      hQ hG hH hF hR hK (by omega) hr (qq_lt q i W hiW.le)
      (fun ho => by
        rw [r_parity g _ hg] at ho
        have : 1 ≤ q / 2 ^ i := by
          rcases Nat.eq_zero_or_pos (q / 2 ^ i) with h0 | h0
          · rw [h0] at ho; simp at ho
          · exact h0
        exact Nat.le_mul_of_pos_right g this)
      (fun _ => by rw [q_half q i W hiW]; exact qh_lt q i W hiW)
    rw [q_new q i W g hg hiW, r_new q i g hg] at body
    set σ' := ((σ.sets Q (fb W (q % 2 ^ (i + 1) * 2 ^ (W - (i + 1))))).sets Rs (fb W (g * (q / 2 ^ (i + 1))))).setv rK m
      with hσ'
    have ih := divLoop_spec Rs Q hRQ hRU hQU hRH hQH W g q hW hg hgq hq m (i + 1) σ' (by omega)
      (numOn_setv _ _ _ _ _ _ (numOn_sets_self _ Rs W _ (by simp [hRs.2])))
      (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (Ne.symm hRQ) (numOn_sets_self σ Q W _ hQ.2)))
      (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (Ne.symm hRU) (numOn_sets_ne _ _ _ _ (Ne.symm hQU) hG)))
      (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (Ne.symm hRH) (numOn_sets_ne _ _ _ _ (Ne.symm hQH) hH)))
      (by simp [hσ', Function.update_of_ne (show rF ≠ rK by decide), hF])
      (by simp [hσ', Function.update_of_ne (show rR ≠ rK by decide), hR]) (by simp [hσ'])
    refine WExec.cast (capO W) (WExec.whrT (by omega) body ih) ?_ (by ring_nf; omega)
    refine WState.eq rfl ?_ ?_ rfl
    · funext j; simp only [hσ', WState.setv_st, WState.sets_st, Function.update_apply]; split_ifs <;> rfl
    · funext j; simp only [hσ', WState.setv_val, WState.sets_val, Function.update_apply]; split_ifs <;> rfl

/-! ## The top word `H = 2^(W−1)` -/

/-- One doubling of `X 5`; `rK −= 1`. -/
def shlBody : WM nsO nrO := .seq (shlB (sX 5) (sX 4) rF rR) (.dec rK)

theorem shlLoop_spec (W : ℕ) :
    ∀ (m j : ℕ) (σ : St), j + m = W - 1 → NumOn σ (sX 5) W (2 ^ j) → NumOn σ (sX 4) W 0 → σ.val rF = 0 →
      σ.val rR = 0 → σ.val rK = m → m ≤ W →
      WExec (capO W) (.whr rK shlBody) σ ((σ.sets (sX 5) (fb W (2 ^ (W - 1)))).setv rK 0) (m * (41 * W + 12) + 1)
  | 0, j, σ, hj, h5, _, _, _, hK, _ => by
    rw [show j = W - 1 by omega] at h5
    refine WExec.cast (capO W) (WExec.whrF hK) ?_ (by omega)
    refine WState.eq rfl ?_ ?_ rfl
    · funext k
      simp only [WState.setv_st, WState.sets_st, Function.update_apply]
      split_ifs with h1
      · subst h1; exact h5.1
      · rfl
    · funext k
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs with h1
      · subst h1; exact hK
      · rfl
  | m + 1, j, σ, hj, h5, h4, hF, hR, hK, hm => by
    have s := shlB_spec (capO W) W (show sX 5 ≠ sX 4 by decide) (show rF ≠ rR by decide) σ (2 ^ j) 0 h5 h4 hF hR
      (by unfold capO; omega)
    have e2 : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
    rw [e2] at s
    have hK1 : (σ.sets (sX 5) (fb W (2 ^ (j + 1)))).val rK = m + 1 := by simp [hK]
    have sd := WExec.dec (cap := capO W) rK (σ.sets (sX 5) (fb W (2 ^ (j + 1)))) (by rw [hK1]; unfold capO; omega)
    rw [hK1, Nat.add_sub_cancel] at sd
    have ih := shlLoop_spec W m (j + 1) ((σ.sets (sX 5) (fb W (2 ^ (j + 1)))).setv rK m) (by omega)
      (numOn_setv _ _ _ _ _ _ (numOn_sets_self σ _ W _ h5.2))
      (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (by decide) h4))
      (by simp [Function.update_of_ne (show rF ≠ rK by decide), hF])
      (by simp [Function.update_of_ne (show rR ≠ rK by decide), hR]) (by simp) (by omega)
    refine WExec.cast (capO W) (WExec.whrT (by omega) (WExec.seq s sd) ih) ?_ (by ring_nf; omega)
    refine WState.eq rfl ?_ ?_ rfl
    · funext k; simp only [WState.setv_st, WState.sets_st, Function.update_apply]; split_ifs <;> rfl
    · funext k; simp only [WState.setv_val, WState.sets_val, Function.update_apply]; split_ifs <;> rfl

/-- **`X 5 := 2^(W−1)`**: `oneB`, `rK := W − 1`, `W − 1` doublings. -/
def mkH : WM nsO nrO :=
  .seq (oneB (sX 5) (sX 4) rF rR) (.seq (UnionMachine.BinW.dupR rW rK (rg 0)) (.seq (.dec rK) (.whr rK shlBody)))

def mkHCost (W : ℕ) : ℕ := 41 * W + 7 + 1 + (18 * W + 3 + 1 + (1 + 1 + (W * (41 * W + 12) + 1)))

/-- `div Rs Q`: `rK := W`, `W` rounds. -/
def div (Rs Q : Fin (nsO + 1)) : WM nsO nrO := .seq (UnionMachine.BinW.dupR rW rK (rg 0)) (.whr rK (divBody Rs Q))

def divCost (W : ℕ) : ℕ := 18 * W + 3 + 1 + (W * (150 * W + 30) + 1)

/-- **P4's program**. -/
def p4P : WM nsO nrO := .seq mkH (.seq (div sN (sX 0)) (div sD (sX 1)))

def p4Cost (W : ℕ) : ℕ := mkHCost W + 1 + (divCost W + 1 + divCost W)

theorem p4Cost_le (W : ℕ) : p4Cost W ≤ 1000 * (W + 1) ^ 2 := by
  unfold p4Cost mkHCost divCost
  nlinarith [Nat.zero_le W]

theorem mkH_spec (W a b u v : ℕ) (σ : St) (h : Words σ W a b u v) (hW : 1 ≤ W) :
    WExec (capO W) mkH σ (σ.sets (sX 5) (fb W (2 ^ (W - 1)))) (mkHCost W) := by
  have hc : 2 * W + 1 ≤ capO W := by unfold capO; omega
  have hF : σ.val rF = 0 := h.bd.regs rF (by decide)
  have hR : σ.val rR = 0 := h.bd.regs rR (by decide)
  have s1 := oneB_spec (capO W) W (show sX 5 ≠ sX 4 by decide) (show rF ≠ rR by decide) σ 0 0 (h.hx 5) (h.hx 4) hF hR
    hW hc
  have s2 := UnionMachine.BinW.dupR_spec (capO W) rW rK (rg 0) (by decide) (by decide) (by decide)
    (σ.sets (sX 5) (fb W 1)) W h.bd.hw (h.bd.regs rK (by decide)) (h.bd.regs (rg 0) (by decide)) (by omega)
  have s3 := WExec.dec (cap := capO W) rK ((σ.sets (sX 5) (fb W 1)).setv rK W) (by simp; unfold capO; omega)
  simp only [wsetv_setv, wsetv_val_self] at s3
  have s4 := shlLoop_spec W (W - 1) 0 (((σ.sets (sX 5) (fb W 1)).setv rK (W - 1))) (by omega)
    (numOn_setv _ _ _ _ _ _ (numOn_sets_self σ _ W 1 (h.bd.heads _)))
    (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (by decide) (h.hx 4)))
    (by simp [Function.update_of_ne (show rF ≠ rK by decide), hF])
    (by simp [Function.update_of_ne (show rR ≠ rK by decide), hR]) (by simp) (by omega)
  refine WExec.cast (capO W) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · refine WState.eq rfl ?_ ?_ rfl
    · funext k; simp only [WState.setv_st, WState.sets_st, Function.update_apply]; split_ifs <;> rfl
    · funext k
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs with hk
      · subst hk; exact (h.bd.regs rK (by decide)).symm
      · rfl
  · unfold mkHCost
    have : (W - 1) * (41 * W + 12) ≤ W * (41 * W + 12) := Nat.mul_le_mul_right _ (by omega)
    omega

theorem div_spec (Rs Q : Fin (nsO + 1)) (hRQ : Rs ≠ Q) (hRU : Rs ≠ sU) (hQU : Q ≠ sU) (hRH : Rs ≠ sX 5)
    (hQH : Q ≠ sX 5) (W g q : ℕ) (σ : St) (hW : 1 ≤ W) (hg : g % 2 = 1) (hgq : g * q < 2 ^ W) (hq : q < 2 ^ W)
    (hRs : NumOn σ Rs W (g * q)) (hQ : NumOn σ Q W 0) (hG : NumOn σ sU W g) (hH : NumOn σ (sX 5) W (2 ^ (W - 1)))
    (hw : σ.val rW = W) (hF : σ.val rF = 0) (hR : σ.val rR = 0) (hK : σ.val rK = 0) (h0 : σ.val (rg 0) = 0) :
    WExec (capO W) (div Rs Q) σ ((σ.sets Q (fb W q)).sets Rs (fb W 0)) (divCost W) := by
  have s1 := UnionMachine.BinW.dupR_spec (capO W) rW rK (rg 0) (by decide) (by decide) (by decide) σ W hw hK h0
    (by unfold capO; omega)
  have s2 := divLoop_spec Rs Q hRQ hRU hQU hRH hQH W g q hW hg hgq hq W 0 (σ.setv rK W) (by omega)
    (by simpa using numOn_setv σ Rs rK W W (g * q) hRs) (by rw [pow_zero, Nat.mod_one, Nat.zero_mul]; exact numOn_setv σ Q rK W W 0 hQ)
    (numOn_setv _ _ _ _ _ _ hG) (numOn_setv _ _ _ _ _ _ hH)
    (by simp [Function.update_of_ne (show rF ≠ rK by decide), hF])
    (by simp [Function.update_of_ne (show rR ≠ rK by decide), hR]) (by simp)
  refine WExec.cast (capO W) (WExec.seq s1 s2) ?_ (by unfold divCost; omega)
  refine WState.eq rfl ?_ ?_ rfl
  · funext k; simp only [WState.setv_st, WState.sets_st, Function.update_apply]
  · funext k
    simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with hk
    · subst hk; exact hK.symm
    · rfl

theorem p4_run (W a b v : ℕ) (σ : St) (h : Words σ W a b (Nat.gcd a b) v) (hg : Nat.gcd a b % 2 = 1)
    (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hb0 : 0 < b) :
    ∃ τ, WExec (capO W) p4P σ τ (p4Cost W) ∧ Quot τ W (a / Nat.gcd a b) (b / Nat.gcd a b) := by
  set g := Nat.gcd a b with hgdef
  have hW : 1 ≤ W := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · subst h0; simp at hb; omega
    · exact h0
  have ea : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have eb : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hqa : a / g < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) ha
  have hqb : b / g < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) hb
  have sH := mkH_spec W a b g v σ h hW
  set σH := σ.sets (sX 5) (fb W (2 ^ (W - 1))) with hσH
  have hH : NumOn σH (sX 5) W (2 ^ (W - 1)) := numOn_sets_self σ _ W _ (h.bd.heads _)
  have s1 := div_spec sN (sX 0) (by decide) (by decide) (by decide) (by decide) (by decide) W g (a / g) σH hW hg
    (by rw [ea]; exact ha) hqa (by rw [ea]; exact numOn_sets_ne _ _ _ _ (by decide) h.hn)
    (numOn_sets_ne _ _ _ _ (by decide) (h.hx 0)) (numOn_sets_ne _ _ _ _ (by decide) h.hu) hH h.bd.hw
    (h.bd.regs rF (by decide)) (h.bd.regs rR (by decide)) (h.bd.regs rK (by decide)) (h.bd.regs (rg 0) (by decide))
  set σ1 := (σH.sets (sX 0) (fb W (a / g))).sets sN (fb W 0) with hσ1
  have s2 := div_spec sD (sX 1) (by decide) (by decide) (by decide) (by decide) (by decide) W g (b / g) σ1 hW hg
    (by rw [eb]; exact hb) hqb
    (by rw [eb]; exact numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide)
      (numOn_sets_ne _ _ _ _ (by decide) h.hd)))
    (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide) (h.hx 1))))
    (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide) h.hu)))
    (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide) hH)) h.bd.hw
    (h.bd.regs rF (by decide)) (h.bd.regs rR (by decide)) (h.bd.regs rK (by decide)) (h.bd.regs (rg 0) (by decide))
  refine ⟨(σ1.sets (sX 1) (fb W (b / g))).sets sD (fb W 0),
    WExec.cast (capO W) (WExec.seq sH (WExec.seq s1 s2)) rfl (by unfold p4Cost; omega), ?_⟩
  have keep : ∀ (X : Fin (nsO + 1)) (y : ℕ), X ≠ sX 5 → X ≠ sX 0 → X ≠ sN → X ≠ sX 1 → X ≠ sD → NumOn σ X W y →
      NumOn ((σ1.sets (sX 1) (fb W (b / g))).sets sD (fb W 0)) X W y := fun X y h5 h0 hN h1 hD hX =>
    numOn_sets_ne _ _ _ _ hD (numOn_sets_ne _ _ _ _ h1 (numOn_sets_ne _ _ _ _ hN (numOn_sets_ne _ _ _ _ h0
      (numOn_sets_ne _ _ _ _ h5 hX))))
  refine ⟨⟨h.bd.heads, h.bd.cell, h.bd.hw, h.bd.regs⟩, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp [hσ1, hσH, Function.update_of_ne (show sO ≠ sD by decide), Function.update_of_ne (show sO ≠ sX 1 by decide),
      Function.update_of_ne (show sO ≠ sN by decide), Function.update_of_ne (show sO ≠ sX 0 by decide),
      Function.update_of_ne (show sO ≠ sX 5 by decide), h.ho]
  · exact numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide)
      (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_self σH _ W _ (by simp [hσH, h.bd.heads]))))
  · exact numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_self σ1 _ W _ (by simp [hσ1, hσH, h.bd.heads]))
  · by_cases h5 : j = 5
    · subst h5
      exact ⟨2 ^ (W - 1), numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide)
        (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_ne _ _ _ _ (by decide) hH)))⟩
    · have hne : ∀ j : Fin 6, 2 ≤ j.val → j ≠ 5 →
          sX j ≠ sX 5 ∧ sX j ≠ sX 0 ∧ sX j ≠ sN ∧ sX j ≠ sX 1 ∧ sX j ≠ sD := by decide
      obtain ⟨a1, a2, a3, a4, a5⟩ := hne j hj h5
      exact ⟨0, keep (sX j) 0 a1 a2 a3 a4 a5 (h.hx j)⟩

/-- **P4**. -/
def ph4 : Ph4 := ⟨p4P, p4Cost, 1000, p4Cost_le, p4_run⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.P4
