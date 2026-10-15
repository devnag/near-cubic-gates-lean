import Proof.Gates.ENP.TableSeedsRuns
import Proof.Gates.ENP.TableStageMachine

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.ENP.TableSearch

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicGates.Close.ENP.TEmit
open NearCubicGates.Close.CheckedPCPP.NodeEmit

/-- **Polynomially bounded** in the size `s` (constant and exponent existential). -/
def PB {α : Type} (s : α → ℕ) (f : α → ℕ) : Prop := ∃ K e : ℕ, ∀ a, f a ≤ K * (s a + 1) ^ e

section PBClosure

variable {α : Type} {s : α → ℕ}

theorem PB.mono {f g : α → ℕ} (h : ∀ a, f a ≤ g a) (hg : PB s g) : PB s f := by
  obtain ⟨K, e, hK⟩ := hg
  exact ⟨K, e, fun a => (h a).trans (hK a)⟩

theorem PB.const (c : ℕ) : PB s (fun _ => c) := ⟨c, 0, fun a => by simp⟩

theorem PB.size : PB s s := ⟨1, 1, fun a => by simp⟩

theorem PB.add {f g : α → ℕ} (hf : PB s f) (hg : PB s g) : PB s (fun a => f a + g a) := by
  obtain ⟨K1, e1, h1⟩ := hf
  obtain ⟨K2, e2, h2⟩ := hg
  refine ⟨K1 + K2, e1 + e2, fun a => ?_⟩
  have p1 : (s a + 1) ^ e1 ≤ (s a + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : (s a + 1) ^ e2 ≤ (s a + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have q1 := Nat.mul_le_mul_left K1 p1
  have q2 := Nat.mul_le_mul_left K2 p2
  have r1 := h1 a
  have r2 := h2 a
  show f a + g a ≤ (K1 + K2) * (s a + 1) ^ (e1 + e2)
  rw [Nat.add_mul]
  omega

theorem PB.mul {f g : α → ℕ} (hf : PB s f) (hg : PB s g) : PB s (fun a => f a * g a) := by
  obtain ⟨K1, e1, h1⟩ := hf
  obtain ⟨K2, e2, h2⟩ := hg
  refine ⟨K1 * K2, e1 + e2, fun a => ?_⟩
  calc f a * g a ≤ (K1 * (s a + 1) ^ e1) * (K2 * (s a + 1) ^ e2) := Nat.mul_le_mul (h1 a) (h2 a)
    _ = K1 * K2 * (s a + 1) ^ (e1 + e2) := by rw [pow_add]; ring

theorem two_pow_nbl_le (m : ℕ) : 2 ^ natBitLength m ≤ 2 * m + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    rw [pow_succ]
    omega

theorem PB.nbl {f : α → ℕ} (hf : PB s f) : PB s (fun a => natBitLength (f a)) :=
  PB.mono (fun a => natBitLength_le (f a)) (PB.add hf (PB.const 1))

theorem PB.pow2 {f : α → ℕ} (hf : PB s f) : PB s (fun a => 2 ^ natBitLength (f a)) :=
  PB.mono (fun a => two_pow_nbl_le (f a)) (PB.add (PB.mul (PB.const 2) hf) (PB.const 2))

theorem PB.sub {f g : α → ℕ} (hf : PB s f) : PB s (fun a => f a - g a) := PB.mono (fun a => Nat.sub_le _ _) hf

end PBClosure

/-- One closure step. -/
macro "pb_step" : tactic =>
  `(tactic| first
    | with_reducible assumption
    | with_reducible exact PB.const _
    | with_reducible apply PB.pow2
    | with_reducible apply PB.nbl
    | with_reducible apply PB.add
    | with_reducible apply PB.mul
    | with_reducible apply PB.sub)

/-! ## The atoms -/

/-- The inputs of builder T: an oracle circuit and the word's tail. -/
abbrev TIn := Σ ℓ : ℕ, OracleCircuit ℓ ℓ × List Bool

/-- The size: `2^ℓ + |word ++ post|`. -/
def tSize (a : TIn) : ℕ := 2 ^ a.1 + ((OracleOutput.word ⟨a.1, a.2.1⟩) ++ a.2.2).length

theorem pb_T : PB tSize (fun a => 2 ^ a.1) := PB.mono (fun a => by unfold tSize; omega) PB.size

theorem pb_ell : PB tSize (fun a => a.1) :=
  PB.mono (fun a => (Nat.lt_two_pow_self).le) pb_T

theorem pb_m : PB tSize (fun a => a.2.1.nodes.length) :=
  PB.mono (fun a => by
    have := nodes_le_word a.2.1
    have h1 : 1 ≤ 2 ^ a.1 := Nat.one_le_two_pow
    have h2 : (OracleOutput.word ⟨a.1, a.2.1⟩).length ≤ ((OracleOutput.word ⟨a.1, a.2.1⟩) ++ a.2.2).length := by simp
    unfold tSize
    omega) PB.size

theorem pb_out : PB tSize (fun a => a.2.1.output.val) :=
  PB.mono (fun a => a.2.1.output.isLt.le) pb_m

theorem pb_W : PB tSize (fun a => 8 * (tSize a + 1) ^ 4) := ⟨8, 4, fun a => le_rfl⟩

theorem pb_r7 : PB tSize (fun a => r7M a.2.1) := by
  have hW : PB tSize (fun a => 2 * ((8 * (tSize a + 1) ^ 4) * (6 * ((8 * (tSize a + 1) ^ 4) +
      (8 * (tSize a + 1) ^ 4) + 5) + 3))) := by
    exact PB.mul (PB.const 2) (PB.mul pb_W (PB.add (PB.mul (PB.const 6) (PB.add (PB.add pb_W pb_W)
      (PB.const 5))) (PB.const 3)))
  refine PB.mono (fun a => ?_) hW
  have hT : 2 ^ a.1 ≤ tSize a + 1 := by unfold tSize; omega
  have hm : a.2.1.nodes.length ≤ tSize a + 1 := by
    have := nodes_le_word a.2.1
    have h1 : 1 ≤ 2 ^ a.1 := Nat.one_le_two_pow
    have h2 : (OracleOutput.word ⟨a.1, a.2.1⟩).length ≤ ((OracleOutput.word ⟨a.1, a.2.1⟩) ++ a.2.2).length := by simp
    unfold tSize
    omega
  have hN := tNodes_le a.2.1 (tSize a + 1) hT hm
  have hTW : 2 ^ a.1 ≤ 8 * (tSize a + 1) ^ 4 := by
    have : tSize a + 1 ≤ (tSize a + 1) ^ 4 := Nat.le_self_pow (by omega) _
    omega
  have hg := RepairOrdinary.RecoveryBoundedGraphBudget.graph_bound (TCirc.tCircuit a.2.1) (8 * (tSize a + 1) ^ 4) hTW hN
  unfold r7M
  rw [RepairOrdinary.Streaming.marks_length]
  change 2 * (tGraph a.2.1).length ≤ _
  exact Nat.mul_le_mul_left 2 hg

/-! ## The seeds loop -/

theorem seedsCostPoly : TEmit.SeedsCostPoly := by
  have hT := pb_T
  have hl := pb_ell
  have hm := pb_m
  have ho := pb_out
  have hr := pb_r7
  have h : PB tSize (fun a => TCirc.T a.1 * (seedCostC a.2.1 + 4) + 1) := by
    simp only [seedCostC, nodeCostC, nodeCostB, oracleCost, argCost, groupsCost, groupCost, pairCost, nodeCost,
      fieldCost, fieldsCost, imgCost, plainCost, closeCost, vC, bzM, xm, TCirc.base, TCirc.S, TCirc.L, TCirc.K]
    repeat pb_step
  obtain ⟨K, e, hK⟩ := h
  exact ⟨K, e, fun {ℓ} C post => hK ⟨ℓ, C, post⟩⟩

end NearCubicGates.Close.ENP.TableSearch
