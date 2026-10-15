import Proof.Gates.Expand.Print4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

/-- The printer's constants. -/
structure PConst (V W : ℕ) (w : Fin 14 → ℕ) : Prop where
  tm : w 9 = 2 ^ V * 2 ^ W
  m : w 10 = 2 ^ W
  one : w 11 = 1
  h : w 12 = 2 ^ (W - 1)
  zero : w 13 = 0

def setFlagCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + ((1 + 1 + 3) + 1)

def bitBodyCost (Wb : ℕ) : ℕ :=
  1 + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (((1 + 1 + natWCost Wb) + 1) + 1 +
    ((34 * Wb + 3) + 1 + ((41 * Wb + 7) + 1 + setFlagCost Wb))))))

def signCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + ((2 * natWCost Wb + 100 * Wb + 20) + 1)

theorem bitsUpTo_length_mono (s : ℕ) : ∀ j j', j ≤ j' → (bitsUpTo s j).length ≤ (bitsUpTo s j').length := by
  intro j j' h
  induction j' with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with h1 | h1
    · rw [bitsUpTo_succ, List.length_append]; have := ih (by omega); omega
    · rw [show j = n + 1 by omega]

section Rec
variable {PB : Fin 14 ↪ Fin (ns + 1)} {PG : Fin 5 ↪ Fin nr} {PR : Fin 4 ↪ Fin nr} {O : Fin (ns + 1)} {OP : Fin nr}
  {cap Wb : ℕ} {σ0 : WState ns nr} (z : Regs0 PG PR σ0) (hl : PLay PB PG PR O OP)
include z hl

theorem setFlag_spec {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} (h : RS PB PG O OP Wb σ0 τ w u 0 0)
    (h13 : w 13 = 0) (h4 : w 4 < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (setFlag PB PG) τ (setFlagCost Wb) (fun τ' => RS PB PG O OP Wb σ0 τ' w u 0 (decide (0 < w 4)).toNat) := by
  refine Runs.seq (rLt z hl 13 4 (by decide) h (by rw [h13]; exact Nat.two_pow_pos Wb) h4 hcap) (fun τ1 h1 => ?_)
  rw [h13] at h1
  refine Runs.ifr (c := 1 + 1 + 3) (fun hT => ?_) (fun hF => ?_)
  · rw [h1.2.2.2.2.1] at hT
    have hp : 0 < w 4 := by by_contra hc; simp [hc] at hT
    simp only [decide_eq_true hp, Bool.toNat_true] at h1 ⊢
    exact Runs.seq (c2 := 3) (rDecF hl h1 (by omega)) (fun τ2 h2 => rIncG (cap := cap) hl h2 (by omega))
  · rw [h1.2.2.2.2.1] at hF
    have hp : ¬ 0 < w 4 := by intro hc; simp [hc] at hF
    simp only [decide_eq_false hp, Bool.toNat_false] at h1 ⊢
    exact (Runs.of (WXExec.skip cap τ1) h1).cost (by omega)

theorem bitBody_spec {τ : WState ns nr} {w : Fin 14 → ℕ} {u0 : List Bool} (s j : ℕ)
    (h : RS PB PG O OP Wb σ0 τ w (u0 ++ bitsUpTo s j) 0 1) (h4 : w 4 = s / 2 ^ j) (h6 : w 6 = j)
    (h11 : w 11 = 1) (h13 : w 13 = 0) (hok : ∀ i, w i < 2 ^ Wb) (hjW : j + 1 < 2 ^ Wb)
    (hO0 : σ0.sh O = (σ0.st O).length) (hW : 1 ≤ Wb) (hcap : 2 * Wb + 2 ≤ cap)
    (hcO : σ0.val OP + (u0 ++ bitsUpTo s (j + 1)).length + 2 * Wb + 2 ≤ cap) :
    Runs cap (bitBody PB PG PR O OP) τ (bitBodyCost Wb) (fun τ' => ∃ w', RS PB PG O OP Wb σ0 τ' w'
      (u0 ++ bitsUpTo s (j + 1)) 0 (decide (0 < s / 2 ^ (j + 1))).toNat ∧ w' 4 = s / 2 ^ (j + 1) ∧
      w' 6 = j + 1 ∧ (∀ i, i ≠ 4 → i ≠ 6 → i ≠ 7 → w' i = w i) ∧ ∀ i, w' i < 2 ^ Wb) := by
  have hbs := bitsUpTo_succ s j
  refine Runs.seq (rDecG hl h (by omega)) (fun τ1 h1 => ?_)
  simp only [Nat.sub_self] at h1
  refine Runs.seq (rCopy z hl 7 4 (by decide) (by simp [bl]) h1 (by omega)) (fun τ2 h2 => ?_)
  refine Runs.seq (rAnd z hl 7 11 (by decide) (by simp [bl]) h2 (by omega)) (fun τ3 h3 => ?_)
  simp only [Function.update_self, Function.update_of_ne (show (11 : Fin 14) ≠ 7 by decide), h4, h11,
    Function.update_idem] at h3
  have hb7 : s / 2 ^ j &&& 1 < 2 ^ Wb := lt_of_le_of_lt Nat.and_le_right (by simpa using Nat.one_lt_two_pow_iff.mpr (by omega))
  refine Runs.seq (rLt z hl 13 7 (by decide) h3 (by simp; rw [h13]; exact Nat.two_pow_pos Wb) (by simpa using hb7)
    (by omega)) (fun τ4 h4' => ?_)
  simp only [Function.update_self, Function.update_of_ne (show (13 : Fin 14) ≠ 7 by decide), h13] at h4'
  refine Runs.seq (Runs.ifr (c := 1 + 1 + natWCost Wb)
    (Q := fun ρ => RS PB PG O OP Wb σ0 ρ (Function.update w 7 (s / 2 ^ j &&& 1)) (u0 ++ bitsUpTo s (j + 1)) 0 0)
    (fun hT => ?_) (fun hF => ?_)) (fun τ5 h5 => ?_)
  · rw [h4'.2.2.2.2.1] at hT
    have hp : 0 < s / 2 ^ j &&& 1 := by by_contra hc; exact hT (by rw [decide_eq_false hc]; rfl)
    have hbit := (and_one_testBit s j).mp hp
    rw [decide_eq_true hp] at h4'
    refine Runs.seq (rDecF hl h4' (by omega)) (fun τ6 h6' => ?_)
    refine (rNatW z hl 6 h6' hO0 (by simp; rw [h6]; omega) hW hcap (by rw [hbs] at hcO; simp [hbit] at hcO ⊢; omega)).post
      (fun ρ hρ => ?_)
    simp only [Function.update_of_ne (show (6 : Fin 14) ≠ 7 by decide), h6] at hρ
    rw [hbs, if_pos hbit, ← List.append_assoc]; exact hρ
  · rw [h4'.2.2.2.2.1] at hF
    have hp : ¬ 0 < s / 2 ^ j &&& 1 := by intro hc; rw [decide_eq_true hc] at hF; exact absurd hF (by decide)
    have hbit : ¬ s.testBit j = true := fun hb => hp ((and_one_testBit s j).mpr hb)
    rw [decide_eq_false hp] at h4'
    refine (Runs.of (WXExec.skip cap τ4) ?_).cost (by omega)
    rw [hbs, if_neg hbit, List.append_nil]; exact h4'
  · have hw4 : (Function.update w 7 (s / 2 ^ j &&& 1)) 4 = s / 2 ^ j := by simp [h4]
    have hs4 : s / 2 ^ j < 2 ^ Wb := by have := hok 4; rwa [h4] at this
    have hs5 : s / 2 ^ (j + 1) < 2 ^ Wb := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hs4
    refine Runs.seq (rHalf z hl 4 (by simp [bl]) h5 (by rw [hw4]; exact hs4) (by omega)) (fun τ6 h6' => ?_)
    rw [hw4, Nat.div_div_eq_div_mul, ← pow_succ] at h6'
    refine Runs.seq (rInc z hl 6 11 (by decide) (by simp [bl]) h6' (by simp; rw [h6]; omega) (by omega))
      (fun τ7 h7 => ?_)
    refine (setFlag_spec z hl h7 (by simp [h13]) (by simp; exact hs5) (by omega)).post
      (fun ρ hρ => ⟨_, hρ, by simp, by simp [h6], fun i h1 h2 h3 => by simp [h1, h2, h3], fun i => ?_⟩)
    by_cases e6 : i = 6
    · subst e6; simp [h6]; omega
    · by_cases e4 : i = 4
      · subst e4; simp; exact hs5
      · by_cases e7 : i = 7
        · subst e7; simpa using hb7
        · simp [e6, e4, e7]; exact hok i

/-- The bit loop's invariant. -/
def BInv (PB : Fin 14 ↪ Fin (ns + 1)) (PG : Fin 5 ↪ Fin nr) (O : Fin (ns + 1)) (OP : Fin nr) (Wb : ℕ)
    (σ0 : WState ns nr) (w0 : Fin 14 → ℕ) (u0 : List Bool) (s k : ℕ) (τ : WState ns nr) : Prop :=
  k ≤ Nat.size s ∧ ∃ w, RS PB PG O OP Wb σ0 τ w (u0 ++ bitsUpTo s (Nat.size s - k)) 0
    (decide (0 < s / 2 ^ (Nat.size s - k))).toNat ∧ w 4 = s / 2 ^ (Nat.size s - k) ∧ w 6 = Nat.size s - k ∧
    (∀ i, i ≠ 4 → i ≠ 6 → i ≠ 7 → w i = w0 i) ∧ ∀ i, w i < 2 ^ Wb

theorem bitLoop_spec (w0 : Fin 14 → ℕ) (u0 : List Bool) (s : ℕ) (hs : s < 2 ^ Wb) (h11 : w0 11 = 1) (h13 : w0 13 = 0)
    (hO0 : σ0.sh O = (σ0.st O).length) (hW : 1 ≤ Wb) (hcap : 2 * Wb + 2 ≤ cap)
    (hcO : σ0.val OP + (u0 ++ bitsUpTo s (Nat.size s)).length + 2 * Wb + 2 ≤ cap) :
    ∀ k τ, BInv PB PG O OP Wb σ0 w0 u0 s k τ →
      Runs cap (.whr (PG 4) (bitBody PB PG PR O OP)) τ (k * (bitBodyCost Wb + 2) + 1)
        (BInv PB PG O OP Wb σ0 w0 u0 s 0) := by
  have hsz : Nat.size s ≤ Wb := Nat.size_le.mpr hs
  have hWl : Wb < 2 ^ Wb := Nat.lt_two_pow_self
  refine Runs.whr _ _ _ (fun τ hτ => ⟨?_, hτ⟩) (fun k τ hτ => ?_)
  · obtain ⟨_, w, h, _⟩ := hτ
    rw [h.2.2.2.2.2.1, Nat.sub_zero, Nat.div_eq_of_lt (Nat.lt_size_self s)]; rfl
  · obtain ⟨hk, w, h, h4, h6, hw, hok⟩ := hτ
    set j := Nat.size s - (k + 1) with hj
    have hjs : j < Nat.size s := by omega
    have hpos : 0 < s / 2 ^ j := (div_pos_iff_lt_size s j).mpr hjs
    rw [decide_eq_true hpos, Bool.toNat_true] at h
    refine ⟨by rw [h.2.2.2.2.2.1]; decide, ?_⟩
    have hj1 : j + 1 = Nat.size s - k := by omega
    have hcO' : σ0.val OP + (u0 ++ bitsUpTo s (j + 1)).length + 2 * Wb + 2 ≤ cap := by
      have := bitsUpTo_length_mono s (j + 1) (Nat.size s) (by omega)
      simp only [List.length_append] at hcO ⊢; omega
    refine (bitBody_spec z hl s j h h4 h6 (by rw [hw 11 (by decide) (by decide) (by decide)]; exact h11)
      (by rw [hw 13 (by decide) (by decide) (by decide)]; exact h13) hok (by omega) hO0 hW hcap hcO').post
      (fun ρ ⟨w', hρ, h4', h6', hw', hok'⟩ => ⟨by omega, w', ?_, ?_, ?_, ?_, hok'⟩)
    · rw [← hj1]; exact hρ
    · rw [← hj1]; exact h4'
    · rw [← hj1]; exact h6'
    · intro i a b c; rw [hw' i a b c, hw i a b c]

theorem signPart_spec {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} (V W : ℕ)
    (h : RS PB PG O OP Wb σ0 τ w u 0 0) (hc : PConst V W w) (h5 : w 5 < 2 ^ W) (hok : ∀ i, w i < 2 ^ Wb)
    (hWW : 2 ^ W < 2 ^ Wb) (hO0 : σ0.sh O = (σ0.st O).length) (hW : 1 ≤ Wb) (hcap : 2 * Wb + 2 ≤ cap)
    (hcO : σ0.val OP + u.length + 2 * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (signPart PB PG PR O OP) τ (signCost Wb) (fun τ' => ∃ w', RS PB PG O OP Wb σ0 τ' w'
      (u ++ (if w 5 < 2 ^ (W - 1) then natWord 0 ++ natWord (w 5) else natWord 1 ++ natWord (2 ^ W - w 5))) 0 0 ∧
      (∀ i, i ≠ 8 → w' i = w i) ∧ ∀ i, w' i < 2 ^ Wb) := by
  have hnw : ∀ v, v < 2 ^ Wb → (natWord v).length ≤ 2 * Wb + 1 := by
    intro v hv; rw [natWord_length]; have := lenF_le v Wb hv hW; omega
  refine Runs.seq (rLt z hl 5 12 (by decide) h (hok 5) (hok 12) (by omega)) (fun τ1 h1 => ?_)
  rw [hc.h] at h1
  refine Runs.ifr (c := 2 * natWCost Wb + 100 * Wb + 20) (fun hT => ?_) (fun hF => ?_)
  · rw [h1.2.2.2.2.1] at hT
    have hp : w 5 < 2 ^ (W - 1) := by by_contra hc'; exact hT (by rw [decide_eq_false hc']; rfl)
    rw [decide_eq_true hp, Bool.toNat_true] at h1
    refine (Runs.seq (rDecF hl h1 (by omega)) (fun τ2 h2 => Runs.seq (rNatW z hl 13 h2 hO0 (hok 13) hW hcap
      (by omega)) (fun τ3 h3 => (rNatW z hl 5 h3 hO0 (hok 5) hW hcap (by
        have := hnw _ (hok 13); simp only [List.length_append]; omega)).post
          (fun ρ hρ => ⟨w, ?_, fun _ _ => rfl, hok⟩)))).cost (by omega)
    rw [hc.zero] at hρ; rw [if_pos hp, ← List.append_assoc]; exact hρ
  · rw [h1.2.2.2.2.1] at hF
    have hp : ¬ w 5 < 2 ^ (W - 1) := by intro hc'; rw [decide_eq_true hc'] at hF; exact absurd hF (by decide)
    rw [decide_eq_false hp, Bool.toNat_false] at h1
    have h5' : w 5 ≤ 2 ^ W := by omega
    refine (Runs.seq (rCopy z hl 8 10 (by decide) (by simp [bl]) h1 (by omega)) (fun τ2 h2 => Runs.seq
      (rSub z hl 8 5 (by decide) (by simp [bl]) h2 (by simp [hc.m]; exact h5') (by simp [hc.m]; exact hWW) (by omega))
      (fun τ3 h3 => Runs.seq (rNatW z hl 11 h3 hO0 (by simp; exact hok 11) hW hcap (by omega))
        (fun τ4 h4 => (rNatW z hl 8 h4 hO0 (by simp [hc.m]; omega) hW hcap (by
          have := hnw _ (hok 11); simp only [List.length_append, Function.update_of_ne (show (11 : Fin 14) ≠ 8 by decide)]; omega)).post
          (fun ρ hρ => ⟨Function.update w 8 (2 ^ W - w 5), ?_, fun i hi => by simp [hi], fun i => ?_⟩))))).cost
            (by omega)
    · have e : Function.update (Function.update w 8 (w 10)) 8 (Function.update w 8 (w 10) 8 -
          Function.update w 8 (w 10) 5) = Function.update w 8 (2 ^ W - w 5) := by
        funext i; by_cases e8 : i = 8
        · subst e8; simp [hc.m]
        · simp [e8]
      rw [e] at hρ
      rw [if_neg hp, ← List.append_assoc]
      simpa [hc.one] using hρ
    · by_cases e : i = 8
      · subst e; simp; omega
      · simp [e]; exact hok i

end Rec

end NearCubicGates.Close.Expand
