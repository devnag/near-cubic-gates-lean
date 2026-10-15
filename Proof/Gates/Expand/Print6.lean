import Proof.Gates.Expand.Print5

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

def prRecCost (Wb V : ℕ) : ℕ :=
  BinW.divCost Wb + 1 + (natWCost Wb + 1 + (BinW.divCost Wb + 1 + ((41 * Wb + 3) + 1 + (setFlagCost Wb + 1 +
    ((V * (bitBodyCost Wb + 2) + 1) + 1 + signCost Wb)))))

section Rec
variable {PB : Fin 14 ↪ Fin (ns + 1)} {PG : Fin 5 ↪ Fin nr} {PR : Fin 4 ↪ Fin nr} {O : Fin (ns + 1)} {OP : Fin nr}
  {cap Wb : ℕ} {σ0 : WState ns nr} (z : Regs0 PG PR σ0) (hl : PLay PB PG PR O OP)
include z hl

/-- **One monomial**: the record `x` in `WK` prints `recOut V W x`. -/
theorem prRec_spec {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} (V W x : ℕ)
    (h : RS PB PG O OP Wb σ0 τ w u 0 0) (hc : PConst V W w) (hx : w 0 = x) (hok : ∀ i, w i < 2 ^ Wb)
    (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hO0 : σ0.sh O = (σ0.st O).length) (hW : 1 ≤ Wb) (hcap : 2 * Wb + 2 ≤ cap)
    (hcO : σ0.val OP + (u ++ recOut V W x).length + 2 * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (prRec PB PG PR O OP) τ (prRecCost Wb V) (fun τ' => ∃ w', RS PB PG O OP Wb σ0 τ' w'
      (u ++ recOut V W x) 0 0 ∧ (∀ i, 9 ≤ i.val → w' i = w i) ∧ w' 0 = w 0 ∧ ∀ i, w' i < 2 ^ Wb) := by
  have hV : 0 < 2 ^ V := Nat.two_pow_pos V
  have hWp : 0 < 2 ^ W := Nat.two_pow_pos W
  have hTM : 0 < 2 ^ V * 2 ^ W := Nat.mul_pos hV hWp
  have hWW : 2 ^ W < 2 ^ Wb := by nlinarith
  have hxl : x < 2 ^ Wb := by rw [← hx]; exact hok 0
  set TM := 2 ^ V * 2 ^ W with hTMd
  set s := x % TM / 2 ^ W with hsd
  set acc := x % TM % 2 ^ W with haccd
  have hs : s < 2 ^ V := by
    rw [hsd, Nat.div_lt_iff_lt_mul hWp]; exact Nat.mod_lt _ hTM
  have hsz : Nat.size s ≤ V := Nat.size_le.mpr hs
  have hacc : acc < 2 ^ W := Nat.mod_lt _ hWp
  have hlenR : (u ++ recOut V W x).length = (u ++ natWord (x / TM)).length + (bitsUpTo s (Nat.size s)).length +
      (if acc < 2 ^ (W - 1) then natWord 0 ++ natWord acc else natWord 1 ++ natWord (2 ^ W - acc)).length := by
    simp only [recOut, List.length_append, bitsUpTo, bitsOf]; ring
  have hsign : ∀ v, v < 2 ^ Wb → (natWord v).length ≤ 2 * Wb + 1 := by
    intro v hv; rw [natWord_length]; have := lenF_le v Wb hv hW; omega
  refine Runs.seq (rDivmod z hl 0 9 1 2 3 (by decide) (by simp [bl]) (by simp [bl]) (by simp [bl]) h (hok 0)
    (by rw [hc.tm]; exact hTM) (by rw [hc.tm]; nlinarith) (by omega)) (fun τ1 h1 => ?_)
  rw [hx, hc.tm] at h1
  refine Runs.seq (rNatW z hl 1 h1 hO0 (by simp <;> exact lt_of_le_of_lt (Nat.div_le_self _ _) hxl) hW hcap
    (by simp only [hlenR, List.length_append] at hcO ⊢; omega)) (fun τ2 h2 => ?_)
  simp only [Function.update_of_ne (show (1 : Fin 14) ≠ 3 by decide), Function.update_of_ne (show (1 : Fin 14) ≠ 2 by decide),
    Function.update_self] at h2
  refine Runs.seq (rDivmod z hl 2 10 4 5 3 (by decide) (by simp [bl]) (by simp [bl]) (by simp [bl]) h2
    (by simp <;> exact lt_of_lt_of_le (Nat.mod_lt _ hTM) (by nlinarith)) (by simp [hc.m] <;> exact hWp)
    (by simp [hc.m] <;> nlinarith) (by omega)) (fun τ3 h3 => ?_)
  simp only [Function.update_of_ne (show (2 : Fin 14) ≠ 3 by decide), Function.update_self,
    Function.update_of_ne (show (10 : Fin 14) ≠ 3 by decide), Function.update_of_ne (show (10 : Fin 14) ≠ 2 by decide),
    Function.update_of_ne (show (10 : Fin 14) ≠ 1 by decide), hc.m] at h3
  refine Runs.seq (rZero z hl 6 0 (by decide) (by simp [bl]) h3 (by omega)) (fun τ4 h4 => ?_)
  set w4 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update w 1 (x / TM)) 2 (x % TM)) 3 0) 4 s) 5 acc) 3 0) 6 0 with hw4
  have e4 : ∀ i, 9 ≤ i.val → w4 i = w i := by
    intro i hi
    have h1 : i ≠ 1 := by rintro rfl; simp at hi
    have h2 : i ≠ 2 := by rintro rfl; simp at hi
    have h3' : i ≠ 3 := by rintro rfl; simp at hi
    have h4' : i ≠ 4 := by rintro rfl; simp at hi
    have h5 : i ≠ 5 := by rintro rfl; simp at hi
    have h6 : i ≠ 6 := by rintro rfl; simp at hi
    simp [hw4, h1, h2, h3', h4', h5, h6]
  have hVW : 2 ^ V < 2 ^ Wb := by nlinarith
  have hsW : s < 2 ^ Wb := lt_trans hs hVW
  have haW : acc < 2 ^ Wb := lt_trans hacc hWW
  have hmW : x % TM < 2 ^ Wb := lt_of_lt_of_le (Nat.mod_lt _ hTM) (by nlinarith)
  have hdW : x / TM < 2 ^ Wb := lt_of_le_of_lt (Nat.div_le_self _ _) hxl
  have hok4 : ∀ i, w4 i < 2 ^ Wb := by
    intro i
    simp only [hw4, Function.update_apply]
    split_ifs <;> first | exact Nat.two_pow_pos Wb | exact hsW | exact haW | exact hmW | exact hdW | exact hok i
  have hw44 : w4 4 = s := by simp [hw4]
  refine Runs.seq (setFlag_spec z hl h4 (by rw [e4 13 (by decide), hc.zero]) (by exact hok4 4) (by omega))
    (fun τ5 h5 => ?_)
  rw [hw44] at h5
  have hB : BInv PB PG O OP Wb σ0 w4 (u ++ natWord (x / TM)) s (Nat.size s) τ5 :=
    ⟨le_rfl, w4, by simpa [bitsUpTo] using h5, by simp [hw44], by simp [hw4], fun _ _ _ _ => rfl, hok4⟩
  refine Runs.seq ((bitLoop_spec z hl w4 (u ++ natWord (x / TM)) s hsW (by rw [e4 11 (by decide), hc.one]) (by rw [e4 13 (by decide), hc.zero]) hO0 hW hcap
      (by simp only [hlenR, List.length_append] at hcO ⊢; omega) (Nat.size s) τ5 hB).cost
      (show Nat.size s * (bitBodyCost Wb + 2) + 1 ≤ V * (bitBodyCost Wb + 2) + 1 by
        have := Nat.mul_le_mul_right (bitBodyCost Wb + 2) hsz; omega)) (fun τ6 h6 => ?_)
  obtain ⟨_, w5, h5', h54, h56, h5w, hok5⟩ := h6
  rw [Nat.sub_zero, Nat.div_eq_of_lt (Nat.lt_size_self s)] at h5'
  have e5 : ∀ i, 9 ≤ i.val → w5 i = w i := by
    intro i hi
    rw [h5w i (by rintro rfl; simp at hi) (by rintro rfl; simp at hi) (by rintro rfl; simp at hi), e4 i hi]
  have hw55 : w5 5 = acc := by rw [h5w 5 (by decide) (by decide) (by decide)]; simp [hw4]
  have hc5 : PConst V W w5 := ⟨by rw [e5 9 (by decide), hc.tm], by rw [e5 10 (by decide), hc.m],
    by rw [e5 11 (by decide), hc.one], by rw [e5 12 (by decide), hc.h], by rw [e5 13 (by decide), hc.zero]⟩
  have h5'' : RS PB PG O OP Wb σ0 τ6 w5 (u ++ natWord (x / TM) ++ bitsUpTo s (Nat.size s)) 0 0 := by
    simpa using h5'
  refine (signPart_spec z hl V W h5'' hc5 (by rw [hw55]; exact hacc) hok5 hWW hO0 hW hcap
    (by simp only [hlenR, List.length_append] at hcO ⊢; omega)).post (fun ρ ⟨w6, h6', h6w, hok6⟩ => ⟨w6, ?_, ?_, ?_, hok6⟩)
  · rw [hw55] at h6'
    have : u ++ recOut V W x = u ++ natWord (x / TM) ++ bitsUpTo s (Nat.size s) ++
        (if acc < 2 ^ (W - 1) then natWord 0 ++ natWord acc else natWord 1 ++ natWord (2 ^ W - acc)) := by
      simp only [recOut, bitsUpTo, bitsOf, List.append_assoc, hsd, haccd, hTMd]
    rw [this]; exact h6'
  · intro i hi; rw [h6w i (by rintro rfl; simp at hi), e5 i hi]
  · rw [h6w 0 (by decide), h5w 0 (by decide) (by decide) (by decide)]; simp [hw4]

end Rec

end NearCubicGates.Close.Expand
