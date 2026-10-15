import Proof.Gates.TabMachine.CompileM9

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem flatMap_filterMap {α β γ : Type} (l : List α) (f : α → Option β) (g : β → List γ) :
    (l.filterMap f).flatMap g = l.flatMap fun a => match f a with | some b => g b | none => [] := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [List.filterMap_cons, h, ih]

/-- The main branch's records are the levels' records. -/
theorem records_main (W : ℕ) (ws : List ℤ) (sh L : ℕ) :
    ((List.range L).reverse.flatMap fun bit => (List.range ws.length).reverse.filterMap fun i =>
      if (ws.getD i 0).natAbs.testBit bit then some (childL ws sh bit i) else none).flatMap
        (fun c => frame (recBits W c)) = (List.range L).reverse.flatMap (lvlRecs W ws sh) := by
  rw [List.flatMap_assoc]
  congr 1; funext bit
  rw [flatMap_filterMap]
  unfold lvlRecs
  congr 1; funext i
  unfold visitRec
  split <;> simp_all

section Levels
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- The level loop's invariant. -/
def LvInv (cap W : ℕ) (σ0 : WState ns nr) (ws : List ℤ) (sh L : ℕ) (out L0 : List Bool) (j : ℕ)
    (τ : WState ns nr) : Prop :=
  OutOn τ (S 2) (R 14) (out ++ (((List.range L).reverse).take j).flatMap (lvlRecs W ws sh)) L0 ∧
    BodyPre S R cap W τ (2 ^ (L - j)) ∧ ChildPre S R cap W τ ∧ (∃ v, NumOn τ (S 19) (W + 1) v) ∧
    (∃ v, NumOn τ (S 14) (W + 1) v) ∧ τ.val (R 10) = 0 ∧ τ.val (R 20) = 0 ∧ τ.val (R 21) = 0 ∧
    SameExcept σ0 τ [S 2, S 3, S 4, S 5, S 6, S 7, S 12, S 13, S 14, S 15, S 16, S 17, S 18, S 19] [R 8, R 9, R 14]

theorem lvInv_setv {cap W : ℕ} {σ0 τ : WState ns nr} {ws : List ℤ} {sh L : ℕ} {out L0 : List Bool} {j : ℕ}
    (h : LvInv S R cap W σ0 ws sh L out L0 j τ) (k : Fin 24) (hk : k = 8 ∨ k = 9) (v : ℕ) :
    LvInv S R cap W σ0 ws sh L out L0 j (τ.setv (R k) v) := by
  obtain ⟨hKD, hpre, hcp, hC, hTL, hIX, hK4, hF2, hfr⟩ := h
  have hne : ∀ m : Fin 24, m ≠ k → (τ.setv (R k) v).val (R m) = τ.val (R m) :=
    fun m hm => by simp [Function.update_of_ne (emb_ne R hm)]
  have h14 : (14 : Fin 24) ≠ k := by rcases hk with rfl | rfl <;> decide
  have h10 : (10 : Fin 24) ≠ k := by rcases hk with rfl | rfl <;> decide
  have h20 : (20 : Fin 24) ≠ k := by rcases hk with rfl | rfl <;> decide
  have h21 : (21 : Fin 24) ≠ k := by rcases hk with rfl | rfl <;> decide
  have hkb : k ∉ [(2 : Fin 24), 3, 4, 15, 16, 17] := by rcases hk with rfl | rfl <;> decide
  have hkc : k ∉ [(0 : Fin 24), 1, 11, 12, 22, 5] := by rcases hk with rfl | rfl <;> decide
  have hkl : R k ∈ [R 8, R 9, R 14] := by rcases hk with rfl | rfl <;> simp
  exact ⟨⟨by simpa using hKD.1, by simpa using hKD.2.1, by rw [hne 14 h14]; exact hKD.2.2⟩,
    bodyPre_setv S R hpre k hkb v, childPre_setv S R hcp k hkc v,
    hC.elim fun x h => ⟨x, BinW.numOn_setv h _ _⟩, hTL.elim fun x h => ⟨x, BinW.numOn_setv h _ _⟩,
    by rw [hne 10 h10]; exact hIX, by rw [hne 20 h20]; exact hK4, by rw [hne 21 h21]; exact hF2,
    hfr.trans (sameExcept_setv τ hkl v)⟩

end Levels

end NearCubicGates.Close.TabMachine
