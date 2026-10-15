import Proof.Gates.Expand.Cost3

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

def Pq (r : FormulaReq) : ℕ := (formulaWord r).length + r.2.size + r.2.weight + 1
def Vq (r : FormulaReq) : ℕ := r.1 + 2
def Mq (r : FormulaReq) : ℕ := Vq r ^ r.2.degree

/-- The size facts. -/
structure Facts (r : FormulaReq) : Prop where
  p1 : 1 ≤ Pq r
  v2 : 2 ≤ Vq r
  m1 : 1 ≤ Mq r
  L : Lw r ≤ Pq r
  wt : r.2.weight ≤ Pq r
  D : r.2.degree ≤ Pq r
  E : maxExp r.2 ≤ Pq r
  tb : tokBits r.2 ≤ Pq r
  N : (toks r.2).length ≤ Pq r
  nb : natBitLength r.1 ≤ Pq r
  V : r.1 + 2 = Vq r
  Wt : Wt r ≤ 3 * Pq r
  wb1 : Wb1 r + 1 ≤ 40 * (Vq r ^ 0 * Pq r ^ 2)
  wb1a : Wb1 r + tokBits r.2 + 2 ≤ 12 * (Vq r ^ 0 * Pq r ^ 2)
  wb2 : Wb2 r + 1 ≤ 40 * (Vq r ^ 1 * Pq r ^ 2)
  wb2a : Wb2 r + tokBits r.2 + 2 ≤ 41 * (Vq r ^ 1 * Pq r ^ 2)
  hE : maxExp r.2 + tokBits r.2 + r.1 + 2 ≤ 2 * (Vq r * Pq r)
  fam : (fam r.1 r.2.degree).length ≤ Mq r
  T : (termsWord (expandM r.2)).length ≤ 40 * (Mq r * Vq r * Pq r ^ 2)

theorem facts (r : FormulaReq) : Facts r := by
  have hL : Lw r ≤ Pq r := by unfold Lw Pq; omega
  have hwt : r.2.weight ≤ Pq r := by unfold Pq; omega
  have hD : r.2.degree ≤ Pq r := le_trans (degree_le_weight r.2) hwt
  have htb : tokBits r.2 ≤ Pq r := le_trans (tokBits_le r) hL
  have hp1 : 1 ≤ Pq r := by unfold Pq; omega
  have hv2 : 2 ≤ Vq r := by unfold Vq; omega
  have hp2 : Pq r ≤ Pq r ^ 2 := by nlinarith
  have hvp : Pq r ^ 2 ≤ Vq r * Pq r ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hvp1 : Vq r * Pq r ≤ Vq r * Pq r ^ 2 := Nat.mul_le_mul_left _ hp2
  have hWt : Wt r ≤ 3 * Pq r := by unfold Wt; omega
  have hW1 : Wb1 r = (Lw r + 2) * (Lw r + 2) := rfl
  have hL2 : (Lw r + 2) * (Lw r + 2) ≤ 9 * Pq r ^ 2 := by nlinarith
  have hfam : (fam r.1 r.2.degree).length ≤ Mq r :=
    le_trans (fam_length_le _ _) (Nat.pow_le_pow_left (by unfold Vq; omega) _)
  refine ⟨hp1, hv2, Nat.one_le_pow _ _ (by unfold Vq; omega), hL, hwt, hD,
    le_trans (maxExp_le_size r.2) (by unfold Pq; omega), htb, le_trans (toks_le_word r) hL,
    le_trans (nbl_V_le r) hL, rfl, hWt, ?_, ?_, ?_, ?_, ?_, hfam, ?_⟩
  · simp only [pow_zero, one_mul]; nlinarith
  · simp only [pow_zero, one_mul]; nlinarith
  · simp only [pow_one]
    have e : Wb2 r = (Wt r + Lw r + 2) * (Lw r + 2) + r.1 * (r.2.degree + 1) + r.2.degree + 4 := rfl
    have a1 : (Wt r + Lw r + 2) * (Lw r + 2) ≤ 18 * Pq r ^ 2 := by nlinarith
    have a2 : r.1 * (r.2.degree + 1) ≤ Vq r * (2 * Pq r) := Nat.mul_le_mul (by unfold Vq; omega) (by omega)
    nlinarith
  · simp only [pow_one]
    have e : Wb2 r = (Wt r + Lw r + 2) * (Lw r + 2) + r.1 * (r.2.degree + 1) + r.2.degree + 4 := rfl
    have a1 : (Wt r + Lw r + 2) * (Lw r + 2) ≤ 18 * Pq r ^ 2 := by nlinarith
    have a2 : r.1 * (r.2.degree + 1) ≤ Vq r * (2 * Pq r) := Nat.mul_le_mul (by unfold Vq; omega) (by omega)
    nlinarith
  · have : maxExp r.2 ≤ Pq r := le_trans (maxExp_le_size r.2) (by unfold Pq; omega)
    have : r.1 + 2 ≤ Vq r * Pq r := by unfold Vq; nlinarith
    nlinarith
  · have h := termsWord_le r.2
    have a : 2 * r.2.degree + 3 + r.2.degree * (2 * r.1 + 3) + 5 + (2 * (r.2.weight + 1) + 3) ≤
        20 * (Vq r * Pq r) := by
      have : r.2.degree * (2 * r.1 + 3) ≤ Pq r * (2 * Vq r) := Nat.mul_le_mul hD (by unfold Vq; omega)
      nlinarith
    have b : (fam r.1 r.2.degree).length * (2 * r.2.degree + 3 + r.2.degree * (2 * r.1 + 3) + 5 +
        (2 * (r.2.weight + 1) + 3)) ≤ Mq r * (20 * (Vq r * Pq r)) := Nat.mul_le_mul hfam a
    have c : Mq r * (20 * (Vq r * Pq r)) ≤ 20 * (Mq r * Vq r * Pq r ^ 2) := by
      have : Mq r * (Vq r * Pq r) ≤ Mq r * Vq r * Pq r ^ 2 := by
        rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hp2
      nlinarith
    have d : 2 * (fam r.1 r.2.degree).length + 3 ≤ 5 * (Mq r * Vq r * Pq r ^ 2) := by
      have : 1 ≤ Vq r * Pq r ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have : Mq r ≤ Mq r * Vq r * Pq r ^ 2 := by
        rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by omega)
      have := Nat.one_le_pow r.2.degree (Vq r) (by omega)
      unfold Mq at *; omega
    omega

end NearCubicGates.Close.Expand.Layout
