import Proof.Gates.WorkerArith.TermF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit circuitWord listWord)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix emptyCW)
open NearCubicGates.Close.Worker (Opd model1 model2)

variable {ns nr : ℕ}

section Exact
variable {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
  {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ} {σ : WState ns nr}

def exactEnd (E : TermEnv ns nr) (σ : WState ns nr) (hW : ℕ) (entry : List Bool) : WState ns nr :=
  appendO (((σ.seth E.WT hW).sets E.S2 []).sets E.G []) E.VI (E.R 9) (marks entry)

open Classical in
theorem exactEnd_simW (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hW : ℕ) (entry : List Bool) :
    SimW (termIdeal σ tmap E hW entry) (exactEnd E σ hW entry) := by
  obtain ⟨⟨cS, c1, c2, cT, cG, cL, cV, cW⟩, ⟨s1, s2, sT, sG, sL, sV, sW⟩, ⟨h12, h1T, h1G, h1L, h1V, h1W⟩,
    ⟨h2T, h2G, h2L, h2V, h2W⟩, ⟨hTG, hTL, hTV, hTW⟩, ⟨hGL, hGV, hGW⟩, ⟨hLV, hLW⟩, hVW⟩ := hB.dis
  have hVsp : ¬ ((∃ j, tmap j = E.VI) ∨ E.VI = E.TL ∨ E.VI = E.G ∨ E.VI = E.S1 ∨ E.VI = E.S2) := by
    rintro (⟨j, h⟩ | h | h | h | h)
    · exact (hB.tne j).2.2.2.2.2.2.2.1 h
    · exact hTV h.symm
    · exact hGV h.symm
    · exact h1V h.symm
    · exact h2V h.symm
  apply termIdeal_simW σ _ tmap E hW entry hVsp hVW
  · intro i hi
    simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_of_ne hi]
    by_cases hsp : (∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2
    · rw [if_pos hsp]
      have hiW : i ≠ E.WT := by
        rintro rfl
        rcases hsp with ⟨j, h⟩ | h | h | h | h
        · exact (hB.tne j).2.2.2.2.2.2.2.2 h
        · exact hTW h.symm
        · exact hGW h.symm
        · exact h1W h.symm
        · exact h2W h.symm
      rw [Function.update_of_ne hiW]
      rcases hsp with ⟨j, rfl⟩ | rfl | rfl | rfl | rfl
      · exact hB.ht j
      · exact hB.hTL
      · exact hB.hG
      · exact hB.h1
      · exact hB.h2
    · rw [if_neg hsp]
      by_cases iW : i = E.WT
      · subst iW; rw [if_pos rfl, Function.update_self]
      · rw [if_neg iW, Function.update_of_ne iW]
  · simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_self,
      Function.update_of_ne hVW]
  · intro i hi hsp
    have i2 : i ≠ E.S2 := fun h => hsp (Or.inr (Or.inr (Or.inr (Or.inr h))))
    have iG : i ≠ E.G := fun h => hsp (Or.inr (Or.inr (Or.inl h)))
    simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_of_ne hi,
      Function.update_of_ne i2, Function.update_of_ne iG]
  · intro i hsp
    have hiV : i ≠ E.VI := fun h => hVsp (h ▸ hsp)
    simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_of_ne hiV]
    by_cases iG : i = E.G
    · subst iG; rw [Function.update_self]; intro p; rfl
    rw [Function.update_of_ne iG]
    by_cases i2 : i = E.S2
    · subst i2; rw [Function.update_self]; intro p; rfl
    rw [Function.update_of_ne i2]
    rcases hsp with ⟨j, rfl⟩ | rfl | h | rfl | h
    · exact hB.bt j
    · exact hB.bTL
    · exact absurd h iG
    · exact hB.b1
    · exact absurd h i2
  · simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_self,
      Function.update_of_ne h2V.symm, Function.update_of_ne hGV.symm]
  · simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets]
  · simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets]

end Exact

/-! ## Cost fits -/

theorem pow4_13 (Z : ℕ) : (Z + 13) ^ 4 ≤ 28561 * (Z + 1) ^ 4 := by
  have h : Z + 13 ≤ 13 * (Z + 1) := by omega
  calc (Z + 13) ^ 4 ≤ (13 * (Z + 1)) ^ 4 := Nat.pow_le_pow_left h 4
    _ = 28561 * (Z + 1) ^ 4 := by ring

theorem call_cost_le (t Z B cw wl b n : ℕ) (hcw : cw ≤ 10 * Z + 40) (hw : wl ≤ Z) (hn : n ≤ 30 * Z + 100) :
    writerCost Z B + 1 + finCost t cw wl b n Z + 200 * (Z + 1) ≤ termCost t Z B b := by
  have hZ4 : Z + 1 ≤ (Z + 1) ^ 4 := by
    calc Z + 1 = (Z + 1) ^ 1 := (pow_one _).symm
      _ ≤ (Z + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hZB : Z + 1 ≤ (Z + 1) ^ 4 * (B + 1) := hZ4.trans (Nat.le_mul_of_pos_right _ (by omega))
  have ht : (Z + 1) ^ 4 * (B + 1) ≤ (t + 1) * ((Z + 1) ^ 4 * (B + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have e3 : (300 * t + 6000) * (11 * Z + 41) ≤ 300000 * ((t + 1) * ((Z + 1) ^ 4 * (B + 1))) := by
    have h1 : 11 * Z + 41 ≤ 41 * ((Z + 1) ^ 4 * (B + 1)) := by omega
    have h' : 300 * t + 6000 ≤ 6000 * (t + 1) := by omega
    calc (300 * t + 6000) * (11 * Z + 41) ≤ (6000 * (t + 1)) * (41 * ((Z + 1) ^ 4 * (B + 1))) :=
          Nat.mul_le_mul h' h1
      _ = 246000 * ((t + 1) * ((Z + 1) ^ 4 * (B + 1))) := by ring
      _ ≤ 300000 * ((t + 1) * ((Z + 1) ^ 4 * (B + 1))) := Nat.mul_le_mul_right _ (by omega)
  have e2 : (300 * t + 6000) * (cw + wl + b + 1) ≤ (300 * t + 6000) * (11 * Z + 41) + (300 * t + 6000) * b := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have e1 : 30000000 * (Z + 13) ^ 4 * (B + 1) ≤ 856830000000 * ((Z + 1) ^ 4 * (B + 1)) := by
    have h4 := Nat.mul_le_mul_right (B + 1) (pow4_13 Z)
    calc 30000000 * (Z + 13) ^ 4 * (B + 1) = 30000000 * ((Z + 13) ^ 4 * (B + 1)) := by ring
      _ ≤ 30000000 * (28561 * (Z + 1) ^ 4 * (B + 1)) := Nat.mul_le_mul_left _ h4
      _ = 856830000000 * ((Z + 1) ^ 4 * (B + 1)) := by ring
  have eq : termCost t Z B b = 10000000000000 * ((t + 1) * ((Z + 1) ^ 4 * (B + 1))) + (300 * t + 6000) * b := by
    unfold termCost; ring
  rw [eq]
  unfold writerCost finCost tailCost
  omega

theorem exact_cost_le (t Z B x : ℕ) (hx : x ≤ 2000000 * (Z + 1) ^ 2 * (B + 1)) : x ≤ termCost t Z B 0 := by
  unfold termCost
  have h1 : (Z + 1) ^ 2 ≤ (Z + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (Z + 1) ^ 2 * (B + 1) ≤ (Z + 1) ^ 4 * (B + 1) := Nat.mul_le_mul_right _ h1
  have ht : (Z + 1) ^ 4 * (B + 1) ≤ (t + 1) * ((Z + 1) ^ 4 * (B + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have eq : 10000000000000 * (t + 1) * (Z + 1) ^ 4 * (B + 1) = 10000000000000 * ((t + 1) * ((Z + 1) ^ 4 * (B + 1))) := by
    ring
  have eq2 : 2000000 * (Z + 1) ^ 2 * (B + 1) = 2000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
  rw [eq]; rw [eq2] at hx
  have := Nat.mul_le_mul_left 2000000 h2
  omega

end NearCubicGates.Close.WorkerArith
