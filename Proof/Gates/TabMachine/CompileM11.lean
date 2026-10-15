import Proof.Gates.TabMachine.CompileM10

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

theorem flatMap_take_length_le {α β : Type} (l : List α) (f : α → List β) (m : ℕ) :
    ((l.take m).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop m l]
  rw [List.flatMap_append, List.length_append]; omega

section AllLevels
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- Bounds of the levels, in one place. -/
structure LvBounds (cap W : ℕ) (ws : List ℤ) (sh L : ℕ) (out : List Bool) : Prop where
  shb : sh < 2 ^ (W + 1)
  tlb : ∀ bit < L, 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1 < 2 ^ W
  bitb : 2 ^ (L + 2) ≤ 2 ^ (W + 1)
  w : ∀ z ∈ ws, 2 * z.natAbs + 2 ≤ 2 ^ W
  sum : (ws.map fun z => 2 * z.natAbs + 1).sum < 2 ^ W
  capO : out.length + ((List.range L).reverse.flatMap (lvlRecs W ws sh)).length +
    (ws.length + 1) * (2 * (W + 1) + 1) + 1 ≤ cap
  capI : (ws.length + 1) * (2 * (W + 1) + 1) + 2 * ws.length + 2 ≤ cap
  capL : 2 * L ≤ cap

theorem levels_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (sh L : ℕ) (out L0 : List Bool)
    (hn : 0 < ws.length) (hpre : BodyPre S R cap W σ (2 ^ L)) (hcp : ChildPre S R cap W σ)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hMS : NumOn σ (S 23) (W + 1) sh) (hC : ∃ v, NumOn σ (S 19) (W + 1) v) (hTL : ∃ v, NumOn σ (S 14) (W + 1) v)
    (hNR : σ.val (R 13) = ws.length) (hIX : σ.val (R 10) = 0) (hK3 : σ.val (R 19) = 0) (hK4 : σ.val (R 20) = 0)
    (hF2 : σ.val (R 21) = 0) (hG : σ.val (R 6) = 0) (hLR : σ.val (R 9) = L) (hK2 : σ.val (R 8) = 0)
    (hKD : OutOn σ (S 2) (R 14) out L0) (hb : LvBounds cap W ws sh L out) :
    Runs cap (repK (R 9) (R 8) (lvl S R)) σ (L * (lvlCost W ws.length + 8) + 7 * L + 3) (fun τ =>
      LvInv S R cap W σ ws sh L out L0 L τ ∧ τ.val (R 9) = L ∧ τ.val (R 8) = 0) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have h0 : LvInv S R cap W σ ws sh L out L0 0 σ := ⟨by simpa using hKD, by simpa using hpre, hcp, hC, hTL, hIX, hK4,
    hF2, SameExcept.refl _ _ _⟩
  refine Runs.rep (cap := cap) (K := R 9) (K2 := R 8) (body := lvl S R) (hner (by decide)) (lvlCost W ws.length) L
    (LvInv S R cap W σ ws sh L out L0) hb.capL (fun k τ v h => lvInv_setv S R h 9 (Or.inr rfl) v)
    (fun k τ v h => lvInv_setv S R h 8 (Or.inl rfl) v) ?_ σ h0 hLR hK2
  intro j hj τ hInv
  obtain ⟨hKDj, hprej, hcpj, hCj, hTLj, hIXj, hK4j, hF2j, hfrj⟩ := hInv
  set bit := L - 1 - j with hbit
  have hLj : L - j = bit + 1 := by omega
  rw [hLj] at hprej
  have hpl : ((((List.range L).reverse).take j).flatMap (lvlRecs W ws sh)).length + (lvlRecs W ws sh bit).length ≤
      ((List.range L).reverse.flatMap (lvlRecs W ws sh)).length := by
    have := flatMap_take_length_le ((List.range L).reverse) (lvlRecs W ws sh) (j + 1)
    rw [take_succ_reverse L j hj, List.flatMap_append, List.flatMap_singleton, List.length_append] at this
    exact this
  have hl := lvl_spec S R cap W τ ws junk sh bit (out ++ (((List.range L).reverse).take j).flatMap (lvlRecs W ws sh)) L0
    hn hprej hcpj (by rw [hfrj.st (by simp [emb_eq_iff]), hWS]) (by rw [hfrj.sh (by simp [emb_eq_iff]), hWSh])
    (hfrj.numOn (by simp [emb_eq_iff]) hMS) hCj hTLj (by rw [hfrj.val (by simp [emb_eq_iff])]; exact hNR) hIXj
    (by rw [hfrj.val (by simp [emb_eq_iff])]; exact hK3) hK4j hF2j (by rw [hfrj.val (by simp [emb_eq_iff])]; exact hG)
    hKDj hb.shb (hb.tlb bit (by omega))
    (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hb.bitb)
    hb.w hb.sum (by rw [List.length_append]; have := hb.capO; omega) hb.capI
  refine hl.post fun τ' hτ' => ?_
  obtain ⟨hKD', hpre', hcp', hC', hTL', hIX', hK4', hF2', hfr'⟩ := hτ'
  have hLj' : L - (j + 1) = bit := by omega
  refine ⟨⟨?_, by rw [hLj']; exact hpre', hcp', hC', hTL', hIX', hK4', hF2', hfrj.trans (hfr'.weaken (by simp)
    (by simp))⟩, hfr'.val (by simp [emb_eq_iff]), hfr'.val (by simp [emb_eq_iff])⟩
  rw [take_succ_reverse L j hj, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]
  exact hKD'

end AllLevels

end NearCubicGates.Close.TabMachine
