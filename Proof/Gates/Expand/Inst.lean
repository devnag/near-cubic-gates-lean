import Proof.Gates.Expand.PassV
import Proof.Gates.Expand.Pass

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Tabulator

variable {ns nr : ℕ}

/-- The uniform cost of one token program. -/
def hcost (Wb L E V : ℕ) : ℕ := 5000 * (E + L + V + 2) * (Wb + L + 2) ^ 2

/-- What a token's payload may be: bit lengths below `L`, exponents at most `E`, variables below `V`. -/
def TokOK (L E V : ℕ) : Tok → Prop
  | .const a => natBitLength a.natAbs ≤ L
  | .var j => j < V ∧ natBitLength j ≤ L
  | .pow e => e ≤ E ∧ natBitLength e ≤ L
  | _ => True

/-- The largest exponent of a formula. -/
def maxExp {V : ℕ} : Formula V → ℕ
  | .const _ => 0
  | .var _ => 0
  | .add f g => max (maxExp f) (maxExp g)
  | .neg f => maxExp f
  | .sub f g => max (maxExp f) (maxExp g)
  | .mul f g => max (maxExp f) (maxExp g)
  | .pow f e => max (maxExp f) e

theorem maxExp_le_size {V : ℕ} (F : Formula V) : maxExp F ≤ F.size := by
  induction F with
  | const a => simp [maxExp]
  | var v => simp [maxExp]
  | add f g hf hg => simp only [maxExp, Formula.size]; omega
  | neg f hf => simp only [maxExp, Formula.size]; omega
  | sub f g hf hg => simp only [maxExp, Formula.size]; omega
  | mul f g hf hg => simp only [maxExp, Formula.size]; omega
  | pow f e hf => simp only [maxExp, Formula.size]; omega

theorem toks_ok {V : ℕ} (F : Formula V) : ∀ tok ∈ toks F, TokOK (tokBits F) (maxExp F) V tok := by
  induction F with
  | const a =>
    intro tok ht; simp [toks] at ht; subst ht
    simp only [TokOK]; rw [tokBits_const]; omega
  | var v =>
    intro tok ht; simp [toks] at ht; subst ht
    simp only [TokOK]; rw [tokBits_var]; exact ⟨v.isLt, by omega⟩
  | add f g hf hg =>
    intro tok ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · have := hf tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_add] <;> (try simp only [maxExp]) <;> omega
    · have := hg tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_add] <;> (try simp only [maxExp]) <;> omega
    · simp [TokOK]
  | neg f hf =>
    intro tok ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · have := hf tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_neg] <;> (try simp only [maxExp]) <;> omega
    · simp [TokOK]
  | sub f g hf hg =>
    intro tok ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · have := hf tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_sub] <;> (try simp only [maxExp]) <;> omega
    · have := hg tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_sub] <;> (try simp only [maxExp]) <;> omega
    · simp [TokOK]
  | mul f g hf hg =>
    intro tok ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · have := hf tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_mul] <;> (try simp only [maxExp]) <;> omega
    · have := hg tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_mul] <;> (try simp only [maxExp]) <;> omega
    · simp [TokOK]
  | pow f e hf =>
    intro tok ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · have := hf tok ht; cases tok <;> simp only [TokOK] at this ⊢ <;> rw [tokBits_pow] <;> (try simp only [maxExp]) <;> omega
    · simp only [TokOK, maxExp]; rw [tokBits_pow]; omega

/-! ## Cost bounds -/

theorem two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · rw [pow_succ]; have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h); omega

theorem readNat_cost_le (x : ℕ) :
    (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ 120 * (natBitLength x + 2) * (x + 2) := by
  have := two_pow_nbl_le x
  have h : 40 * 2 ^ natBitLength x + 40 ≤ 120 * (x + 2) := by omega
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (natBitLength x + 2) * (120 * (x + 2)) :=
        Nat.mul_le_mul_left _ h
    _ = 120 * (natBitLength x + 2) * (x + 2) := by ring

section Bounds
variable (Wb : ℕ)
theorem popCost_le : popCost Wb ≤ 500 * (Wb + 1) ^ 2 := by
  unfold popCost; have := BinW.divCost_le Wb; nlinarith
theorem pushCost_le : pushCost Wb ≤ 400 * (Wb + 1) ^ 2 := by
  unfold pushCost; have := BinW.mulCost_le Wb; nlinarith
theorem pop2Cost_le : pop2Cost Wb ≤ 1100 * (Wb + 1) ^ 2 := by
  unfold pop2Cost; have := popCost_le Wb; nlinarith
theorem cmovCost_le : cmovCost Wb ≤ 100 * (Wb + 1) := by unfold cmovCost; omega
theorem negmCost_le : negmCost Wb ≤ 250 * (Wb + 1) := by unfold negmCost; omega
theorem mulmCost_le : mulmCost Wb ≤ 400 * (Wb + 1) ^ 2 := by
  unfold mulmCost; have := BinW.mulCost_le Wb; nlinarith
theorem readBinCost_le (ℓ : ℕ) : readBinCost Wb ℓ ≤ 200 * (ℓ + 1) * (Wb + 1) := by
  unfold readBinCost binStepCost; nlinarith
theorem readSizeCost_le (ℓ : ℕ) : readSizeCost Wb ℓ ≤ 300 * (ℓ + 1) * (Wb + 1) := by
  unfold readSizeCost sizeStepCost cmovCost; nlinarith
end Bounds

/-- The common shape of the bounds: with `S = Wb + L + 2`, `T = E + L + V + 2`. -/
theorem hcost_eq (Wb L E V : ℕ) : hcost Wb L E V = 5000 * ((E + L + V + 2) * (Wb + L + 2) ^ 2) := by
  unfold hcost; ring

/-- Monomial facts for the bounds. -/
theorem sq_facts (Wb L E V : ℕ) :
    (Wb + 1) ^ 2 ≤ (Wb + L + 2) ^ 2 ∧ Wb + 1 ≤ Wb + L + 2 ∧ Wb + L + 2 ≤ (Wb + L + 2) ^ 2 ∧
      (Wb + L + 2) ^ 2 ≤ (E + L + V + 2) * (Wb + L + 2) ^ 2 ∧
      (E + L + V + 2) * (Wb + L + 2) ≤ (E + L + V + 2) * (Wb + L + 2) ^ 2 := by
  refine ⟨Nat.pow_le_pow_left (by omega) 2, by omega, by nlinarith, by nlinarith, ?_⟩
  exact Nat.mul_le_mul_left _ (by nlinarith)

section Inst
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

theorem degHs (cap Wb K t L E V : ℕ) (hK : 1 ≤ K) (hcap : 2 * Wb + 1 ≤ cap) (hcapL : 2 ^ (L + 2) ≤ cap) :
    ∀ tok, TokOK L E V tok →
      HSpec U R cap Wb (K + 1) K t (degAlg K) ((degH U R).getD (tagOf tok) WMX.skip) tok (hcost Wb L E V) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := sq_facts Wb L E V
  have hL2 : L + 2 ≤ cap := le_trans (Nat.lt_two_pow_self).le hcapL
  have hp1 := popCost_le Wb; have hp2 := pushCost_le Wb; have hp3 := pop2Cost_le Wb; have hcm := cmovCost_le Wb
  rw [hcost_eq]
  intro tok hok
  cases tok with
  | const a =>
    simp only [TokOK] at hok
    refine (dConst_spec cap Wb K t _ a rfl hK hcap (by omega)).mono ?_
    unfold dConstCost Codec.skipIntCost
    have : natBitLength (if a < 0 then 1 else 0) ≤ 1 := by split_ifs <;> decide
    omega
  | var j =>
    simp only [TokOK] at hok
    refine (dVar_spec cap Wb K t _ j rfl hK hcap (by omega)).mono ?_
    unfold dVarCost; omega
  | add => exact (dMax_spec cap Wb K t _ (fun _ _ => ⟨rfl, rfl⟩) hK hcap .add (Or.inl rfl)).mono (by unfold dMaxCost; omega)
  | neg => exact (neg_spec cap Wb (K + 1) K t _ (fun _ => rfl)).mono (by omega)
  | sub => exact (dMax_spec cap Wb K t _ (fun _ _ => ⟨rfl, rfl⟩) hK hcap .sub (Or.inr rfl)).mono (by unfold dMaxCost; omega)
  | mul => exact (dMul_spec cap Wb K t _ (fun _ _ => rfl) hK hcap).mono (by unfold dMulCost; omega)
  | pow e =>
    simp only [TokOK] at hok
    refine (dPow_spec cap Wb K t _ e (fun _ => rfl) hK hcap
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcapL)).mono ?_
    unfold dPowCost powBodyCost
    have r1 := readNat_cost_le e
    have r2 : 120 * (natBitLength e + 2) * (e + 2) ≤ 120 * ((E + L + V + 2) * (Wb + L + 2)) := by
      have := Nat.mul_le_mul (show natBitLength e + 2 ≤ Wb + L + 2 by omega) (show e + 2 ≤ E + L + V + 2 by omega)
      nlinarith
    have r3 : e * (41 * Wb + 3 + 1 + cmovCost Wb + 4) ≤ (E + L + V + 2) * (150 * (Wb + L + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have r4 : (E + L + V + 2) * (150 * (Wb + L + 2)) = 150 * ((E + L + V + 2) * (Wb + L + 2)) := by ring
    omega

theorem wtHs (cap Wb K t L E V : ℕ) (hK : 1 ≤ K) (hW : 1 ≤ Wb) (hLW : L < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ (L + 2) ≤ cap) :
    ∀ tok, TokOK L E V tok →
      HSpec U R cap Wb (K + 1) K t (wtAlg K) ((wtH U R).getD (tagOf tok) WMX.skip) tok (hcost Wb L E V) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := sq_facts Wb L E V
  have hL2 : L + 2 ≤ cap := le_trans (Nat.lt_two_pow_self).le hcapL
  have hp1 := popCost_le Wb; have hp2 := pushCost_le Wb; have hp3 := pop2Cost_le Wb; have hcm := cmovCost_le Wb
  rw [hcost_eq]
  intro tok hok
  cases tok with
  | const a =>
    simp only [TokOK] at hok
    refine (wConst_spec cap Wb K t _ a rfl hK hW hcap (by omega) (by omega)).mono ?_
    unfold wConstCost
    have hrs := readSizeCost_le Wb (natBitLength a.natAbs)
    have : natBitLength (if a < 0 then 1 else 0) ≤ 1 := by split_ifs <;> decide
    have r : 300 * (natBitLength a.natAbs + 1) * (Wb + 1) ≤ 300 * (Wb + L + 2) ^ 2 := by
      have := Nat.mul_le_mul (show natBitLength a.natAbs + 1 ≤ Wb + L + 2 by omega) (show Wb + 1 ≤ Wb + L + 2 by omega)
      nlinarith
    omega
  | var j =>
    simp only [TokOK] at hok
    refine (dVar_spec cap Wb K t _ j rfl hK hcap (by omega)).mono ?_
    unfold dVarCost; omega
  | add => exact (wMax_spec cap Wb K t _ (fun _ _ => ⟨rfl, rfl⟩) hK hcap .add (Or.inl rfl)).mono (by unfold wMaxCost; omega)
  | neg => exact (neg_spec cap Wb (K + 1) K t _ (fun _ => rfl)).mono (by omega)
  | sub => exact (wMax_spec cap Wb K t _ (fun _ _ => ⟨rfl, rfl⟩) hK hcap .sub (Or.inr rfl)).mono (by unfold wMaxCost; omega)
  | mul => exact (dMul_spec cap Wb K t _ (fun _ _ => rfl) hK hcap).mono (by unfold dMulCost; omega)
  | pow e =>
    simp only [TokOK] at hok
    refine (dPow_spec cap Wb K t _ e (fun _ => rfl) hK hcap
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcapL)).mono ?_
    unfold dPowCost powBodyCost
    have r1 := readNat_cost_le e
    have r2 : 120 * (natBitLength e + 2) * (e + 2) ≤ 120 * ((E + L + V + 2) * (Wb + L + 2)) := by
      have := Nat.mul_le_mul (show natBitLength e + 2 ≤ Wb + L + 2 by omega) (show e + 2 ≤ E + L + V + 2 by omega)
      nlinarith
    have r3 : e * (41 * Wb + 3 + 1 + cmovCost Wb + 4) ≤ (E + L + V + 2) * (150 * (Wb + L + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have r4 : (E + L + V + 2) * (150 * (Wb + L + 2)) = 150 * ((E + L + V + 2) * (Wb + L + 2)) := by ring
    omega

theorem valHs (cap Wb W t L E V : ℕ) (hW : VOK Wb W) (ht : t < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ (L + 4) ≤ cap) :
    ∀ tok, TokOK L E V tok →
      HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) ((valH U R).getD (tagOf tok) WMX.skip) tok
        (hcost Wb L E V) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := sq_facts Wb L E V
  have hL2 : L + 4 ≤ cap := le_trans (Nat.lt_two_pow_self).le hcapL
  have hp1 := popCost_le Wb; have hp2 := pushCost_le Wb; have hp3 := pop2Cost_le Wb; have hcm := cmovCost_le Wb
  have hng := negmCost_le Wb; have hmm := mulmCost_le Wb
  rw [hcost_eq]
  intro tok hok
  cases tok with
  | const a =>
    simp only [TokOK] at hok
    refine (vConst_spec cap Wb W t a hW hcap (by omega)).mono ?_
    unfold vConstCost
    have hrb := readBinCost_le Wb (natBitLength a.natAbs)
    have hs1 : natBitLength (if a < 0 then 1 else 0) ≤ 1 := by split_ifs <;> decide
    have hs2 : 2 ^ natBitLength (if a < 0 then 1 else 0) ≤ 2 := by
      calc 2 ^ natBitLength (if a < 0 then 1 else 0) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hs1
        _ = 2 := by norm_num
    have r0 : (natBitLength (if a < 0 then 1 else 0) + 2) * (40 * 2 ^ natBitLength (if a < 0 then 1 else 0) + 40) ≤ 360 :=
      le_trans (Nat.mul_le_mul (show _ ≤ 3 by omega) (show _ ≤ 120 by omega)) (by norm_num)
    have r : 200 * (natBitLength a.natAbs + 1) * (Wb + 1) ≤ 200 * (Wb + L + 2) ^ 2 := by
      have := Nat.mul_le_mul (show natBitLength a.natAbs + 1 ≤ Wb + L + 2 by omega) (show Wb + 1 ≤ Wb + L + 2 by omega)
      nlinarith
    omega
  | var j =>
    simp only [TokOK] at hok
    refine (vVar_spec cap Wb W t j hW ht hcap (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcapL)).mono ?_
    unfold vVarCost
    have r1 := readNat_cost_le j
    have r2 : 120 * (natBitLength j + 2) * (j + 2) ≤ 120 * ((E + L + V + 2) * (Wb + L + 2)) := by
      have := Nat.mul_le_mul (show natBitLength j + 2 ≤ Wb + L + 2 by omega) (show j + 2 ≤ E + L + V + 2 by omega)
      nlinarith
    have r3 : j * (34 * Wb + 3 + 4) ≤ (E + L + V + 2) * (40 * (Wb + L + 2)) := Nat.mul_le_mul (by omega) (by omega)
    have r4 : (E + L + V + 2) * (40 * (Wb + L + 2)) = 40 * ((E + L + V + 2) * (Wb + L + 2)) := by ring
    omega
  | add => exact (vAdd_spec cap Wb W t hW hcap).mono (by unfold vAddCost; omega)
  | neg => exact (vNeg_spec cap Wb W t hW hcap).mono (by unfold vNegCost; omega)
  | sub => exact (vSub_spec cap Wb W t hW hcap).mono (by unfold vSubCost; omega)
  | mul => exact (vMul_spec cap Wb W t hW hcap).mono (by unfold vMulCost; omega)
  | pow e =>
    simp only [TokOK] at hok
    refine (vPow_spec cap Wb W t e hW hcap (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcapL)).mono ?_
    unfold vPowCost
    have r1 := readNat_cost_le e
    have r2 : 120 * (natBitLength e + 2) * (e + 2) ≤ 120 * ((E + L + V + 2) * (Wb + L + 2)) := by
      have := Nat.mul_le_mul (show natBitLength e + 2 ≤ Wb + L + 2 by omega) (show e + 2 ≤ E + L + V + 2 by omega)
      nlinarith
    have r3 : e * (mulmCost Wb + 4) ≤ (E + L + V + 2) * (410 * (Wb + L + 2) ^ 2) := Nat.mul_le_mul (by omega) (by nlinarith)
    have r4 : (E + L + V + 2) * (410 * (Wb + L + 2) ^ 2) = 410 * ((E + L + V + 2) * (Wb + L + 2) ^ 2) := by ring
    omega

end Inst

end NearCubicGates.Close.Expand
