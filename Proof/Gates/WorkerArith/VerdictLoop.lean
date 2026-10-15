import Proof.Gates.WorkerArith.VerdictOps

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Worker

section Flag
variable {w : List Bool} {W : ℕ} {wv : Fin 30 → ℕ} {pos lp bad : ℕ} (cap : ℕ)

/-- A flag register set by a test, consumed by a branch. -/
theorem flagM {r : Fin 16} (hr : regs W w.length lp bad r = 0) (b : Bool) {P Q : WMX 29 16} {τ : WState 29 16}
    {c : ℕ} (hP : b = true → WXExec cap P (mk w W wv pos lp bad) τ c)
    (hQ : b = false → WXExec cap Q (mk w W wv pos lp bad) τ c) (hcap : 1 ≤ cap) :
    WXExec cap (.ifr r (.seq (WMX.dec r) P) Q) ((mk w W wv pos lp bad).setv r b.toNat) τ (c + 3) := by
  cases b
  · have e : (mk w W wv pos lp bad).setv r (false.toNat) = mk w W wv pos lp bad := mk_setv_zero w W wv pos lp bad hr
    rw [e]
    exact (WXExec.ifrF (by simp [hr]) (hQ rfl)).mono (by omega)
  · have hd := WXExec.dec cap r ((mk w W wv pos lp bad).setv r (true.toNat)) (by simp; omega)
    have e : ((mk w W wv pos lp bad).setv r (true.toNat)).setv r
        (((mk w W wv pos lp bad).setv r (true.toNat)).val r - 1) = mk w W wv pos lp bad := by
      rw [wsetv_setv]; simp only [WState.setv_val, Function.update_self, Bool.toNat_true, Nat.sub_self]
      exact mk_setv_zero w W wv pos lp bad hr
    rw [e] at hd
    exact (WXExec.ifrT (by simp) (WXExec.seq hd (hP rfl))).mono (by omega)

end Flag

/-! ## One endpoint -/

/-- `POS` (11) for `false`, `NEG` (12) for `true`. -/
def tgt (b : Bool) : Fin 30 := if b then 12 else 11

theorem tgt_numS (b : Bool) : NumS (tgt b) := by cases b <;> (unfold NumS tgt; decide)

/-- One endpoint, negated iff `f`. -/
def endp (f : Bool) : WMX 29 16 :=
  .seq (zread 13) (.seq (zread 14) (.seq (zread 15) (.seq (BinW.divmod 10 15 16 17 18 0 1 3 4)
    (.seq (BinW.mul 14 16 19 20 0 1 2) (.seq (nzP 13 4 11 0 1)
      (.ifr 11 (.seq (WMX.dec 11) (BinW.add (tgt (!f)) 19 0 1)) (BinW.add (tgt f) 19 0 1)))))))

def Keep (Y : Fin 30) : Prop := Y.val < 11 ∨ 21 < Y.val

theorem sgnN_ne (z : ℤ) : decide (sgnN z ≠ 0) = decide (z < 0) := by
  unfold sgnN; by_cases h : z < 0 <;> simp [h]

theorem endpM (r : VerdictReq) (f : Bool) (x : ℚ) (k : ℕ) {W : ℕ} (wv : Fin 30 → ℕ) (lp bad cap : ℕ)
    (hk : k + 3 ≤ (nats r).length) (h0 : (nats r).getD k 0 = sgnN x.num)
    (h1 : (nats r).getD (k + 1) 0 = x.num.natAbs) (h2 : (nats r).getD (k + 2) 0 = x.den)
    (hD : wv 10 = 2 ^ (verdictWord r).length) (hdvd : x.den ∣ 2 ^ (verdictWord r).length)
    (hW : 3 * (verdictWord r).length + 2 ≤ W)
    (hP : wv 11 + posC (2 ^ (verdictWord r).length) f x < 2 ^ W)
    (hN : wv 12 + negC (2 ^ (verdictWord r).length) f x < 2 ^ W) (hcap : 4 * W + 4 ≤ cap) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap (endp f) (mk (verdictWord r) W wv (pfx r k) lp bad)
      (mk (verdictWord r) W wv' (pfx r (k + 3)) lp bad) (1400 * (W + 1) ^ 2) ∧
      wv' 11 = wv 11 + posC (2 ^ (verdictWord r).length) f x ∧
      wv' 12 = wv 12 + negC (2 ^ (verdictWord r).length) f x ∧ ∀ Y, Keep Y → wv' Y = wv Y := by
  set L := (verdictWord r).length with hL
  set D := 2 ^ L with hDdef
  have hW1 : 1 ≤ W := by omega
  have hLW : L ≤ W := by omega
  have hcap2 : 2 * W + 1 ≤ cap := by omega
  have hnum : x.num.natAbs < 2 ^ L := by
    have := field_lt r (getD_mem (nats r) (k + 1) (by omega)); rwa [h1] at this
  have hden0 : 0 < x.den := x.den_pos
  have hdenD : x.den ≤ D := Nat.le_of_dvd (by positivity) hdvd
  have hDW : 2 * D ≤ 2 ^ W := by
    rw [hDdef, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDW' : D < 2 ^ W := by have : 0 < D := by positivity
                              omega
  have hmag : x.num.natAbs * (D / x.den) < 2 ^ W := by
    have hq : D / x.den ≤ D := Nat.div_le_self _ _
    calc x.num.natAbs * (D / x.den) < 2 ^ L * 2 ^ L := by
          apply Nat.mul_lt_mul_of_lt_of_le hnum hq (by positivity)
      _ = 2 ^ (2 * L) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the three reads
  have e1 := zreadF r (W := W) (wv := wv) (lp := lp) (bad := bad) cap (X := 13) (by unfold NumS; decide) (by decide)
    k (by omega) (by omega) hW1 hcap
  have e2 := zreadF r (W := W) (wv := Function.update wv 13 ((nats r).getD k 0)) (lp := lp) (bad := bad) cap (X := 14)
    (by unfold NumS; decide) (by decide) (k + 1) (by omega) (by omega) hW1 hcap
  have e3 := zreadF r (W := W)
    (wv := Function.update (Function.update wv 13 ((nats r).getD k 0)) 14 ((nats r).getD (k + 1) 0))
    (lp := lp) (bad := bad) cap (X := 15) (by unfold NumS; decide) (by decide) (k + 2) (by omega) (by omega) hW1 hcap
  rw [h0, h1, h2] at e3
  rw [h0, h1] at e2
  rw [h0] at e1
  set wv3 := Function.update (Function.update (Function.update wv 13 (sgnN x.num)) 14 x.num.natAbs) 15 x.den
    with hwv3
  have e4 := divM (w := verdictWord r) (W := W) (wv := wv3) (pos := pfx r (k + 3)) (lp := lp) (bad := bad) cap
    (A := 10) (B := 15) (Q := 16) (M := 17) (X := 18) (by unfold NumS; decide) (by unfold NumS; decide)
    (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hwv3, hD, hDW']) (by simp [hwv3, hden0]) (by simp [hwv3]; omega) hcap2
  have hv3 : wv3 10 = D := by simp [hwv3, hD]
  have hv15 : wv3 15 = x.den := by simp [hwv3]
  rw [hv3, hv15] at e4
  set wv4 := Function.update (Function.update (Function.update wv3 16 (D / x.den)) 17 (D % x.den)) 18 0 with hwv4
  have e5 := mulM (w := verdictWord r) (W := W) (wv := wv4) (pos := pfx r (k + 3)) (lp := lp) (bad := bad) cap
    (A := 14) (B := 16) (C := 19) (S := 20) (by unfold NumS; decide) (by unfold NumS; decide)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [hwv4, hwv3]; exact hmag) (by simp [hwv4]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hDW')
    hcap2
  have hv14 : wv4 14 = x.num.natAbs := by simp [hwv4, hwv3]
  have hv16 : wv4 16 = D / x.den := by simp [hwv4]
  rw [hv14, hv16] at e5
  set wv5 := Function.update (Function.update wv4 19 (x.num.natAbs * (D / x.den))) 20 0 with hwv5
  have e6 := nzM (w := verdictWord r) (W := W) (wv := wv5) (pos := pfx r (k + 3)) (lp := lp) (bad := bad) cap
    (X := 13) (Z := 4) (by unfold NumS; decide) (by unfold NumS; decide) (by decide)
    (by simp [hwv5, hwv4, hwv3]; unfold sgnN; split_ifs <;> simp <;> omega) hcap2
  have hv13 : wv5 13 = sgnN x.num := by simp [hwv5, hwv4, hwv3]
  rw [hv13, sgnN_ne] at e6
  set b := decide (x.num < 0) with hb
  have hv19 : wv5 19 = x.num.natAbs * (D / x.den) := by simp [hwv5]
  have hv11 : wv5 11 = wv 11 := by simp [hwv5, hwv4, hwv3]
  have hv12 : wv5 12 = wv 12 := by simp [hwv5, hwv4, hwv3]
  set wv6 := Function.update wv5 (tgt (xor b f)) (wv5 (tgt (xor b f)) + wv5 19) with hwv6
  have hpc : posC D f x = if xor b f then 0 else x.num.natAbs * (D / x.den) := rfl
  have hnc : negC D f x = if xor b f then x.num.natAbs * (D / x.den) else 0 := rfl
  have htgt : wv5 (tgt (xor b f)) + wv5 19 < 2 ^ W := by
    rw [hv19]; unfold tgt
    cases hx : xor b f
    · simp only [Bool.false_eq_true, ↓reduceIte, hv11]; rw [hpc, hx] at hP; simpa using hP
    · simp only [↓reduceIte, hv12]; rw [hnc, hx] at hN; simpa using hN
  have e7 := flagM (w := verdictWord r) (W := W) (wv := wv5) (pos := pfx r (k + 3)) (lp := lp) (bad := bad) cap
    (r := 11) rfl b (P := BinW.add (tgt (!f)) 19 0 1) (Q := BinW.add (tgt f) 19 0 1)
    (τ := mk (verdictWord r) W wv6 (pfx r (k + 3)) lp bad) (c := 50 * (W + 1) ^ 2)
    (fun hb1 => by
      have := addM (w := verdictWord r) (W := W) (wv := wv5) (pos := pfx r (k + 3)) (lp := lp) (bad := bad) cap
        (X := tgt (!f)) (Y := 19) (tgt_numS _) (by unfold NumS; decide) (by cases f <;> decide)
        (by rw [hb1] at htgt; simpa using htgt) hcap2
      rw [hwv6, hb1]; simpa using this)
    (fun hb0 => by
      have := addM (w := verdictWord r) (W := W) (wv := wv5) (pos := pfx r (k + 3)) (lp := lp) (bad := bad) cap
        (X := tgt f) (Y := 19) (tgt_numS _) (by unfold NumS; decide) (by cases f <;> decide)
        (by rw [hb0] at htgt; simpa using htgt) hcap2
      rw [hwv6, hb0]; simpa using this) (by omega)
  refine ⟨wv6, ?_, ?_, ?_, ?_⟩
  · have E := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 e7)))))
    refine E.mono ?_
    have := one_le_sq W
    omega
  · rw [hwv6, hpc]; unfold tgt
    cases hx : xor b f
    · simp [hv11, hv19]
    · simp [hv11]
  · rw [hwv6, hnc]; unfold tgt
    cases hx : xor b f
    · simp [hv12]
    · simp [hv12, hv19]
  · intro Y hY
    unfold Keep at hY
    have hY' : ∀ j : Fin 30, 11 ≤ j.val → j.val ≤ 21 → Y ≠ j := by
      intro j hj1 hj2 e; subst e; omega
    have ht : Y ≠ tgt (xor b f) := by unfold tgt; split_ifs <;> exact hY' _ (by decide) (by decide)
    simp only [hwv6, hwv5, hwv4, hwv3, Function.update_of_ne ht,
      Function.update_of_ne (hY' 20 (by decide) (by decide)), Function.update_of_ne (hY' 19 (by decide) (by decide)),
      Function.update_of_ne (hY' 18 (by decide) (by decide)), Function.update_of_ne (hY' 17 (by decide) (by decide)),
      Function.update_of_ne (hY' 16 (by decide) (by decide)), Function.update_of_ne (hY' 15 (by decide) (by decide)),
      Function.update_of_ne (hY' 14 (by decide) (by decide)), Function.update_of_ne (hY' 13 (by decide) (by decide))]

/-- `flagM` with an existential post-state. -/
theorem flagE {w : List Bool} {W : ℕ} {wv : Fin 30 → ℕ} {pos lp bad : ℕ} (cap : ℕ) {r : Fin 16}
    (hr : regs W w.length lp bad r = 0) (b : Bool) {P Q : WMX 29 16} {Post : WState 29 16 → Prop} {c : ℕ}
    (hP : b = true → ∃ τ, WXExec cap P (mk w W wv pos lp bad) τ c ∧ Post τ)
    (hQ : b = false → ∃ τ, WXExec cap Q (mk w W wv pos lp bad) τ c ∧ Post τ) (hcap : 1 ≤ cap) :
    ∃ τ, WXExec cap (.ifr r (.seq (WMX.dec r) P) Q) ((mk w W wv pos lp bad).setv r b.toNat) τ (c + 3) ∧ Post τ := by
  cases b
  · obtain ⟨τ, e, hτ⟩ := hQ rfl
    exact ⟨τ, flagM cap hr false (fun h => absurd h (by decide)) (fun _ => e) hcap, hτ⟩
  · obtain ⟨τ, e, hτ⟩ := hP rfl
    exact ⟨τ, flagM cap hr true (fun _ => e) (fun h => absurd h (by decide)) hcap, hτ⟩

/-! ## One term -/

/-- One term with sign flag `fs` (`true` iff `σ_t = −1`). -/
def termP (fs : Bool) : WMX 29 16 :=
  .seq (zread 21) (.seq (nzP 21 4 11 0 1)
    (.seq (.ifr 11 (.seq (WMX.dec 11) (.seq (BinW.add (tgt fs) 10 0 1) (endp (!fs)))) (endp fs)) (endp false)))

theorem bitN_ne (b : Bool) : decide (bitN b ≠ 0) = b := by cases b <;> rfl

/-- The denominators of a term's endpoints divide `2^L`. -/
theorem term_dvd (r : VerdictReq) (i : ℕ) (hi : i < r.I.length) :
    (r.I.getD i dT).2.1.den ∣ 2 ^ (verdictWord r).length ∧ (r.I.getD i dT).2.2.den ∣ 2 ^ (verdictWord r).length := by
  have hm : r.I.getD i dT ∈ r.I := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  obtain ⟨h1, h2⟩ := r.hden _ hm
  have f1 := field_lt r (mem_nats_term r i 3 hi (by norm_num))
  have f2 := field_lt r (mem_nats_term r i 6 hi (by norm_num))
  exact ⟨den_dvd_pow r.q _ _ h1 f1, den_dvd_pow r.q _ _ h2 f2⟩

theorem termM (r : VerdictReq) (fs : Bool) (i : ℕ) {W : ℕ} (wv : Fin 30 → ℕ) (lp bad cap : ℕ) (hi : i < r.I.length)
    (hD : wv 10 = 2 ^ (verdictWord r).length) (hW : 3 * (verdictWord r).length + 2 ≤ W)
    (hP : wv 11 + posT (2 ^ (verdictWord r).length) fs (r.I.getD i dT) < 2 ^ W)
    (hN : wv 12 + negT (2 ^ (verdictWord r).length) fs (r.I.getD i dT) < 2 ^ W) (hcap : 4 * W + 4 ≤ cap) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap (termP fs) (mk (verdictWord r) W wv (pfx r (6 + 7 * i)) lp bad)
      (mk (verdictWord r) W wv' (pfx r (6 + 7 * (i + 1))) lp bad) (3200 * (W + 1) ^ 2) ∧
      wv' 11 = wv 11 + posT (2 ^ (verdictWord r).length) fs (r.I.getD i dT) ∧
      wv' 12 = wv 12 + negT (2 ^ (verdictWord r).length) fs (r.I.getD i dT) ∧ ∀ Y, Keep Y → wv' Y = wv Y := by
  set x := r.I.getD i dT with hx
  set k := 6 + 7 * i with hk
  have hW1 : 1 ≤ W := by omega
  have hcap2 : 2 * W + 1 ≤ cap := by omega
  have hlen : k + 7 ≤ (nats r).length := by rw [nats_length]; omega
  have fld : ∀ j < 7, (nats r).getD (k + j) 0 = (termN x).getD j 0 := fun j hj => nats_term r i j hi hj
  obtain ⟨hd1, hd2⟩ := term_dvd r i hi
  have hDW : (2 ^ (verdictWord r).length) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the flip bit
  have e1 := zreadF r (W := W) (wv := wv) (lp := lp) (bad := bad) cap (X := 21) (by unfold NumS; decide)
    (by decide) k (by omega) (by omega) hW1 hcap
  have f0 := fld 0 (by norm_num)
  simp only [Nat.add_zero] at f0
  rw [f0] at e1
  set wv1 := Function.update wv 21 (bitN x.1) with hwv1
  have e2 := nzM (w := verdictWord r) (W := W) (wv := wv1) (pos := pfx r (k + 1)) (lp := lp) (bad := bad) cap
    (X := 21) (Z := 4) (by unfold NumS; decide) (by unfold NumS; decide) (by decide)
    (by simp [hwv1]; unfold bitN; split_ifs <;> simp <;> omega) hcap2
  have hv21 : wv1 21 = bitN x.1 := by simp [hwv1]
  rw [hv21, bitN_ne] at e2
  have hP' : wv 11 + ((if (x.1 && !fs) then (2 ^ (verdictWord r).length) else 0) + posC (2 ^ (verdictWord r).length) (xor fs x.1) x.2.1 + posC (2 ^ (verdictWord r).length) false x.2.2) < 2 ^ W := hP
  have hN' : wv 12 + ((if (x.1 && fs) then (2 ^ (verdictWord r).length) else 0) + negC (2 ^ (verdictWord r).length) (xor fs x.1) x.2.1 + negC (2 ^ (verdictWord r).length) false x.2.2) < 2 ^ W := hN
  have fp : ∀ j, j < 3 → (nats r).getD (k + 1 + j) 0 = (ratN x.2.1).getD j 0 := by
    intro j hj; rw [show k + 1 + j = k + (1 + j) by omega, fld (1 + j) (by omega)]
    interval_cases j <;> rfl
  have fk : ∀ j, j < 3 → (nats r).getD (k + 4 + j) 0 = (ratN x.2.2).getD j 0 := by
    intro j hj; rw [show k + 4 + j = k + (4 + j) by omega, fld (4 + j) (by omega)]
    interval_cases j <;> rfl
  -- the flipped p̂ (and the constant σ·1)
  have e3 := flagE (w := verdictWord r) (W := W) (wv := wv1) (pos := pfx r (k + 1)) (lp := lp) (bad := bad) cap
    (r := 11) rfl x.1 (P := .seq (BinW.add (tgt fs) 10 0 1) (endp (!fs))) (Q := endp fs)
    (Post := fun τ => ∃ wv2 : Fin 30 → ℕ, τ = mk (verdictWord r) W wv2 (pfx r (k + 1 + 3)) lp bad ∧
      wv2 11 = wv 11 + ((if (x.1 && !fs) then (2 ^ (verdictWord r).length) else 0) + posC (2 ^ (verdictWord r).length) (xor fs x.1) x.2.1) ∧
      wv2 12 = wv 12 + ((if (x.1 && fs) then (2 ^ (verdictWord r).length) else 0) + negC (2 ^ (verdictWord r).length) (xor fs x.1) x.2.1) ∧
      ∀ Y, Keep Y → wv2 Y = wv1 Y) (c := 1500 * (W + 1) ^ 2)
    (fun hb => by
      have ea := addM (w := verdictWord r) (W := W) (wv := wv1) (pos := pfx r (k + 1)) (lp := lp) (bad := bad) cap
        (X := tgt fs) (Y := 10) (tgt_numS _) (by unfold NumS; decide) (by cases fs <;> decide)
        (by cases fs <;> simp [tgt, hwv1, hD, hb] at hP' hN' ⊢ <;> omega) hcap2
      set wva := Function.update wv1 (tgt fs) (wv1 (tgt fs) + wv1 10) with hwva
      have hva10 : wva 10 = (2 ^ (verdictWord r).length) := by cases fs <;> simp [hwva, hwv1, tgt, hD]
      obtain ⟨wv2, eb, h11, h12, hkeep⟩ := endpM r (!fs) x.2.1 (k + 1) wva lp bad cap (by omega)
        (by rw [fp 0 (by norm_num)]; rfl) (by rw [fp 1 (by norm_num)]; rfl) (by rw [fp 2 (by norm_num)]; rfl)
        hva10 hd1 hW
        (by cases fs <;> simp [hwva, hwv1, tgt, hD, hb] at hP' ⊢ <;> omega)
        (by cases fs <;> simp [hwva, hwv1, tgt, hD, hb] at hN' ⊢ <;> omega) hcap
      refine ⟨_, (WXExec.seq ea eb).mono ?_, wv2, rfl, ?_, ?_, ?_⟩
      · have := one_le_sq W; omega
      · rw [h11]; cases fs <;> simp [hwva, hwv1, tgt, hD, hb] <;> ring
      · rw [h12]; cases fs <;> simp [hwva, hwv1, tgt, hD, hb] <;> ring
      · intro Y hY
        rw [hkeep Y hY]
        have : Y ≠ tgt fs := by intro e; subst e; cases fs <;> simp [Keep, tgt] at hY
        simp [hwva, Function.update_of_ne this])
    (fun hb => by
      obtain ⟨wv2, eb, h11, h12, hkeep⟩ := endpM r fs x.2.1 (k + 1) wv1 lp bad cap (by omega)
        (by rw [fp 0 (by norm_num)]; rfl) (by rw [fp 1 (by norm_num)]; rfl) (by rw [fp 2 (by norm_num)]; rfl)
        (by simp [hwv1, hD]) hd1 hW
        (by simp [hwv1, hb] at hP' ⊢; omega) (by simp [hwv1, hb] at hN' ⊢; omega) hcap
      refine ⟨_, eb.mono ?_, wv2, rfl, ?_, ?_, hkeep⟩
      · have := one_le_sq W; omega
      · rw [h11]; simp [hwv1, hb]
      · rw [h12]; simp [hwv1, hb]) (by omega)
  obtain ⟨τ, e3, wv2, rfl, h11, h12, hkeep2⟩ := e3
  -- the endpoint κ̂
  obtain ⟨wv3, e4, g11, g12, hkeep3⟩ := endpM r false x.2.2 (k + 4) wv2 lp bad cap (by omega)
    (by rw [fk 0 (by norm_num)]; rfl) (by rw [fk 1 (by norm_num)]; rfl) (by rw [fk 2 (by norm_num)]; rfl)
    (by rw [hkeep2 10 (by unfold Keep; decide)]; simp [hwv1, hD]) hd2 hW
    (by rw [h11]; omega) (by rw [h12]; omega) hcap
  refine ⟨wv3, ?_, ?_, ?_, ?_⟩
  · have E := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))
    rw [show k + 1 + 3 = k + 4 by omega, show k + 4 + 3 = 6 + 7 * (i + 1) by omega] at E
    refine E.mono ?_
    have := one_le_sq W; omega
  · rw [g11, h11]; unfold posT; ring
  · rw [g12, h12]; unfold negT; ring
  · intro Y hY
    rw [hkeep3 Y hY, hkeep2 Y hY]
    have : Y ≠ 21 := by intro e; subst e; simp [Keep] at hY
    simp [hwv1, Function.update_of_ne this]

/-! ## One gadget, all gadgets -/

/-- A run of terms with the given sign flags. -/
def terms : List Bool → WMX 29 16
  | [] => WMX.skip
  | f :: fl => .seq (termP f) (terms fl)

/-- One gadget: its ten terms with the signs of eq:gadget-pair-identity. -/
def gbody : WMX 29 16 := terms ((List.range 10).map fsOf)

theorem posS_succ (D : ℕ) (I : List (Bool × (ℚ × ℚ))) (n : ℕ) :
    posS D I (n + 1) = posS D I n + posT D (fsOf n) (I.getD n dT) := Finset.sum_range_succ _ _
theorem negS_succ (D : ℕ) (I : List (Bool × (ℚ × ℚ))) (n : ℕ) :
    negS D I (n + 1) = negS D I n + negT D (fsOf n) (I.getD n dT) := Finset.sum_range_succ _ _
theorem posS_mono (D : ℕ) (I : List (Bool × (ℚ × ℚ))) {n m : ℕ} (h : n ≤ m) : posS D I n ≤ posS D I m :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)
theorem negS_mono (D : ℕ) (I : List (Bool × (ℚ × ℚ))) {n m : ℕ} (h : n ≤ m) : negS D I n ≤ negS D I m :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem termsM (r : VerdictReq) {W : ℕ} (lp bad cap : ℕ) (hW : 3 * (verdictWord r).length + 2 ≤ W)
    (hPb : posS (2 ^ (verdictWord r).length) r.I r.I.length < 2 ^ W)
    (hNb : negS (2 ^ (verdictWord r).length) r.I r.I.length < 2 ^ W) (hcap : 4 * W + 4 ≤ cap) :
    ∀ (fl : List Bool) (i0 : ℕ) (wv : Fin 30 → ℕ), (∀ j < fl.length, fl.getD j false = fsOf (i0 + j)) →
      i0 + fl.length ≤ r.I.length → wv 10 = 2 ^ (verdictWord r).length →
      wv 11 = posS (2 ^ (verdictWord r).length) r.I i0 → wv 12 = negS (2 ^ (verdictWord r).length) r.I i0 →
      ∃ wv' : Fin 30 → ℕ, WXExec cap (terms fl) (mk (verdictWord r) W wv (pfx r (6 + 7 * i0)) lp bad)
        (mk (verdictWord r) W wv' (pfx r (6 + 7 * (i0 + fl.length))) lp bad) (fl.length * (3300 * (W + 1) ^ 2)) ∧
        wv' 11 = posS (2 ^ (verdictWord r).length) r.I (i0 + fl.length) ∧
        wv' 12 = negS (2 ^ (verdictWord r).length) r.I (i0 + fl.length) ∧ ∀ Y, Keep Y → wv' Y = wv Y
  | [], i0, wv, _, _, _, h11, h12 => ⟨wv, by
      simp only [terms, List.length_nil, Nat.add_zero, Nat.zero_mul]; exact WXExec.skip cap _, by simpa using h11,
      by simpa using h12, fun _ _ => rfl⟩
  | f :: fl, i0, wv, hfl, hlen, hD, h11, h12 => by
    have hf : f = fsOf i0 := by have := hfl 0 (by simp); simpa using this
    subst hf
    have hi : i0 < r.I.length := by simp at hlen; omega
    have hP1 := posS_mono (2 ^ (verdictWord r).length) r.I (show i0 + 1 ≤ r.I.length by omega)
    have hN1 := negS_mono (2 ^ (verdictWord r).length) r.I (show i0 + 1 ≤ r.I.length by omega)
    rw [posS_succ] at hP1; rw [negS_succ] at hN1
    obtain ⟨wv1, e1, g11, g12, hk1⟩ := termM r (fsOf i0) i0 wv lp bad cap hi hD hW (by rw [h11]; omega)
      (by rw [h12]; omega) hcap
    obtain ⟨wv2, e2, f11, f12, hk2⟩ := termsM r lp bad cap hW hPb hNb hcap fl (i0 + 1) wv1
      (fun j hj => by
        have := hfl (j + 1) (by simp; omega); rw [List.getD_cons_succ] at this; rw [this]; congr 1; omega)
      (by simp at hlen; omega) (by rw [hk1 10 (by unfold Keep; decide), hD])
      (by rw [g11, h11, posS_succ]) (by rw [g12, h12, negS_succ])
    refine ⟨wv2, ?_, ?_, ?_, fun Y hY => by rw [hk2 Y hY, hk1 Y hY]⟩
    · have E := WXExec.seq e1 e2
      rw [show 6 + 7 * (i0 + 1 + fl.length) = 6 + 7 * (i0 + (fsOf i0 :: fl).length) by simp; ring] at E
      refine E.mono ?_
      simp only [List.length_cons]
      have := one_le_sq W
      nlinarith
    · rw [f11]; simp; ring_nf
    · rw [f12]; simp; ring_nf

theorem fsOf_mod (a j : ℕ) : fsOf (10 * a + j) = fsOf j := by
  unfold fsOf; congr 3; ext; simp

theorem gbodyM (r : VerdictReq) {W : ℕ} (lp bad cap : ℕ) (hW : 3 * (verdictWord r).length + 2 ≤ W)
    (hPb : posS (2 ^ (verdictWord r).length) r.I r.I.length < 2 ^ W)
    (hNb : negS (2 ^ (verdictWord r).length) r.I r.I.length < 2 ^ W) (hcap : 4 * W + 4 ≤ cap)
    (a : ℕ) (wv : Fin 30 → ℕ) (ha : 10 * (a + 1) ≤ r.I.length) (hD : wv 10 = 2 ^ (verdictWord r).length)
    (h11 : wv 11 = posS (2 ^ (verdictWord r).length) r.I (10 * a))
    (h12 : wv 12 = negS (2 ^ (verdictWord r).length) r.I (10 * a)) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap gbody (mk (verdictWord r) W wv (pfx r (6 + 70 * a)) lp bad)
        (mk (verdictWord r) W wv' (pfx r (6 + 70 * (a + 1))) lp bad) (33000 * (W + 1) ^ 2) ∧
      wv' 11 = posS (2 ^ (verdictWord r).length) r.I (10 * (a + 1)) ∧
      wv' 12 = negS (2 ^ (verdictWord r).length) r.I (10 * (a + 1)) ∧ ∀ Y, Keep Y → wv' Y = wv Y := by
  obtain ⟨wv', e, h1, h2, hk⟩ := termsM r lp bad cap hW hPb hNb hcap ((List.range 10).map fsOf) (10 * a) wv
    (fun j hj => by
      simp at hj
      rw [fsOf_mod a j]; simp [List.getD_eq_getElem?_getD, hj])
    (by simp; omega) hD h11 h12
  simp only [List.length_map, List.length_range] at e h1 h2
  refine ⟨wv', ?_, by rw [h1]; ring_nf, by rw [h2]; ring_nf, hk⟩
  rw [show 6 + 7 * (10 * a) = 6 + 70 * a by ring, show 6 + 7 * (10 * a + 10) = 6 + 70 * (a + 1) by ring] at e
  exact e.mono (by nlinarith)

/-- The gadget loop: `M` passes of `gbody`, counted down in register `10`. -/
def gloop : WMX 29 16 := .whr 10 (.seq (WMX.dec 10) gbody)

theorem gloopM (r : VerdictReq) {W : ℕ} (bad cap : ℕ) (hW : 3 * (verdictWord r).length + 2 ≤ W)
    (hPb : posS (2 ^ (verdictWord r).length) r.I r.I.length < 2 ^ W)
    (hNb : negS (2 ^ (verdictWord r).length) r.I r.I.length < 2 ^ W) (hcap : 4 * W + 4 ≤ cap)
    (hMc : r.M ≤ cap) (wv : Fin 30 → ℕ) (hD : wv 10 = 2 ^ (verdictWord r).length) (h11 : wv 11 = 0)
    (h12 : wv 12 = 0) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap gloop (mk (verdictWord r) W wv (pfx r 6) r.M bad)
        (mk (verdictWord r) W wv' (pfx r (6 + 70 * r.M)) 0 bad) (r.M * (33000 * (W + 1) ^ 2 + 4) + 1) ∧
      wv' 11 = posS (2 ^ (verdictWord r).length) r.I r.I.length ∧
      wv' 12 = negS (2 ^ (verdictWord r).length) r.I r.I.length ∧ ∀ Y, Keep Y → wv' Y = wv Y := by
  have hlen := r.hlen
  let Inv : ℕ → WState 29 16 → Prop := fun a σ => ∃ (wv' : Fin 30 → ℕ) (lp' : ℕ),
    σ = mk (verdictWord r) W wv' (pfx r (6 + 70 * a)) lp' bad ∧
    wv' 11 = posS (2 ^ (verdictWord r).length) r.I (10 * a) ∧
    wv' 12 = negS (2 ^ (verdictWord r).length) r.I (10 * a) ∧ ∀ Y, Keep Y → wv' Y = wv Y
  have hl := Runs.count (cap := cap) (K := 10) (body := gbody) (33000 * (W + 1) ^ 2) r.M Inv hMc
    (by
      rintro a ha σ ⟨wv1, lp1, rfl, g11, g12, hk⟩ -
      rw [mk_setv_lp]
      obtain ⟨wv2, e, f11, f12, hk2⟩ := gbodyM r (r.M - a - 1) bad cap hW hPb hNb hcap a wv1 (by omega)
        (by rw [hk 10 (by unfold Keep; decide), hD]) g11 g12
      exact ⟨_, e, ⟨wv2, r.M - a - 1, rfl, f11, f12, fun Y hY => by rw [hk2 Y hY, hk Y hY]⟩, by simp [regs]⟩)
    (mk (verdictWord r) W wv (pfx r 6) r.M bad) ⟨wv, r.M, by simp, by simp [h11, posS], by simp [h12, negS],
      fun _ _ => rfl⟩ (by simp [regs])
  obtain ⟨τ, e, ⟨wv', lp', rfl, f11, f12, hk⟩, hz⟩ := hl
  have hlp : lp' = 0 := by simpa [regs] using hz
  subst hlp
  refine ⟨wv', e, ?_, ?_, hk⟩
  · rw [f11, hlen]
  · rw [f12, hlen]

end NearCubicGates.Close.WorkerArith
