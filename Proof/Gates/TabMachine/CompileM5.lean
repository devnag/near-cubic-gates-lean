import Proof.Gates.TabMachine.CompileM4

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

section Level5
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

theorem visitCost_mono (W n i : ℕ) (hi : i ≤ n) : visitCost W n i ≤ visitCost W n n := by
  unfold visitCost childCost; omega

/-- The visit loop's invariant. -/
def VInv (cap W : ℕ) (σ0 : WState ns nr) (ws : List ℤ) (sh bit : ℕ) (out L0 : List Bool) (k : ℕ)
    (τ : WState ns nr) : Prop :=
  OutOn τ (S 2) (R 14) (out ++ (((List.range ws.length).reverse).take k).flatMap (visitRec W ws sh bit)) L0 ∧
    BodyPre S R cap W τ (2 ^ bit) ∧ ChildPre S R cap W τ ∧ τ.val (R 10) = ws.length - 1 - k ∧ τ.val (R 20) = 0 ∧
    τ.val (R 21) = 0 ∧ SameExcept σ0 τ [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] [R 10, R 13, R 14, R 19]

theorem vInv_setv {cap W : ℕ} {σ0 τ : WState ns nr} {ws : List ℤ} {sh bit : ℕ} {out L0 : List Bool} {k : ℕ}
    (h : VInv S R cap W σ0 ws sh bit out L0 k τ) (j : Fin 24) (hj : j = 13 ∨ j = 19) (v : ℕ) :
    VInv S R cap W σ0 ws sh bit out L0 k (τ.setv (R j) v) := by
  obtain ⟨hKD, hpre, hcp, hIX, hK4, hF2, hfr⟩ := h
  have hne : ∀ m : Fin 24, m ≠ j → (τ.setv (R j) v).val (R m) = τ.val (R m) :=
    fun m hm => by simp [Function.update_of_ne (emb_ne R hm)]
  rcases hj with rfl | rfl
  · refine ⟨⟨by simpa using hKD.1, by simpa using hKD.2.1, by rw [hne 14 (by decide)]; exact hKD.2.2⟩,
      bodyPre_setv S R hpre 13 (by decide) v, childPre_setv S R hcp 13 (by decide) v,
      by rw [hne 10 (by decide)]; exact hIX, by rw [hne 20 (by decide)]; exact hK4, by rw [hne 21 (by decide)]; exact hF2,
      hfr.trans (sameExcept_setv τ (by simp) v)⟩
  · refine ⟨⟨by simpa using hKD.1, by simpa using hKD.2.1, by rw [hne 14 (by decide)]; exact hKD.2.2⟩,
      bodyPre_setv S R hpre 19 (by decide) v, childPre_setv S R hcp 19 (by decide) v,
      by rw [hne 10 (by decide)]; exact hIX, by rw [hne 20 (by decide)]; exact hK4, by rw [hne 21 (by decide)]; exact hF2,
      hfr.trans (sameExcept_setv τ (by simp) v)⟩

theorem lvl_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (sh bit : ℕ) (out L0 : List Bool)
    (hn : 0 < ws.length) (hpre : BodyPre S R cap W σ (2 ^ (bit + 1))) (hcp : ChildPre S R cap W σ)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hMS : NumOn σ (S 23) (W + 1) sh) (hC : ∃ v, NumOn σ (S 19) (W + 1) v) (hTL : ∃ v, NumOn σ (S 14) (W + 1) v)
    (hNR : σ.val (R 13) = ws.length) (hIX : σ.val (R 10) = 0) (hK3 : σ.val (R 19) = 0) (hK4 : σ.val (R 20) = 0)
    (hF2 : σ.val (R 21) = 0) (hG : σ.val (R 6) = 0) (hKD : OutOn σ (S 2) (R 14) out L0)
    (hshb : sh < 2 ^ (W + 1)) (htlb : 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1 < 2 ^ W)
    (hbit : 2 ^ (bit + 3) ≤ 2 ^ (W + 1))
    (hw : ∀ z ∈ ws, 2 * z.natAbs + 2 ≤ 2 ^ W) (hsum : (ws.map fun z => 2 * z.natAbs + 1).sum < 2 ^ W)
    (hcapO : out.length + (lvlRecs W ws sh bit).length + (ws.length + 1) * (2 * (W + 1) + 1) + 1 ≤ cap)
    (hcapI : (ws.length + 1) * (2 * (W + 1) + 1) + 2 * ws.length + 2 ≤ cap) :
    Runs cap (lvl S R) σ (lvlCost W ws.length) (fun τ =>
      OutOn τ (S 2) (R 14) (out ++ lvlRecs W ws sh bit) L0 ∧ BodyPre S R cap W τ (2 ^ bit) ∧ ChildPre S R cap W τ ∧
      (∃ v, NumOn τ (S 19) (W + 1) v) ∧ (∃ v, NumOn τ (S 14) (W + 1) v) ∧ τ.val (R 10) = 0 ∧ τ.val (R 20) = 0 ∧
      τ.val (R 21) = 0 ∧
      SameExcept σ τ [S 2, S 3, S 4, S 5, S 6, S 7, S 12, S 13, S 14, S 15, S 16, S 17, S 18, S 19] [R 14]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  set n := ws.length with hnn
  have hW1 : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 := lvlHead_spec S R cap W σ sh bit n hpre hMS hC hTL hNR hIX hcp.tmp hG hshb (by omega) hbit (by omega)
  refine Runs.seq' (c2 := n * (visitCost W n n + 8) + 7 * n + 3) h1 (fun τ1 hτ1 => ?_) (by unfold lvlCost; omega)
  obtain ⟨hpre1, hTL1, hC1, hIX1, hfr1⟩ := hτ1
  have hcp1 : ChildPre S R cap W τ1 := by
    obtain ⟨⟨nv, hnv⟩, ⟨yv, hyv⟩, ⟨nov, hnov⟩, hwkh, hwkl, hci, hcw, hdj, hpass, htmp, htg⟩ := hcp
    exact ⟨⟨nv, hfr1.numOn (by simp [emb_eq_iff]) hnv⟩, ⟨yv, hfr1.numOn (by simp [emb_eq_iff]) hyv⟩,
      ⟨nov, hfr1.numOn (by simp [emb_eq_iff]) hnov⟩, by rw [hfr1.sh (by simp [emb_eq_iff])]; exact hwkh,
      by rw [hfr1.st (by simp [emb_eq_iff])]; exact hwkl, by rw [hfr1.val (by simp [emb_eq_iff])]; exact hci,
      by rw [hfr1.val (by simp [emb_eq_iff])]; exact hcw, by rw [hfr1.val (by simp [emb_eq_iff])]; exact hdj,
      by rw [hfr1.val (by simp [emb_eq_iff])]; exact hpass, by rw [hfr1.val (by simp [emb_eq_iff])]; exact htmp,
      by rw [hfr1.val (by simp [emb_eq_iff])]; exact htg⟩
  have h0 : VInv S R cap W τ1 ws sh bit out L0 0 τ1 :=
    ⟨by simpa using ⟨by rw [hfr1.st (by simp [emb_eq_iff]), hKD.1], by rw [hfr1.sh (by simp [emb_eq_iff]), hKD.2.1],
        by rw [hfr1.val (by simp [emb_eq_iff]), hKD.2.2]⟩, hpre1, hcp1, by rw [hIX1]; omega,
      by rw [hfr1.val (by simp [emb_eq_iff])]; exact hK4, by rw [hfr1.val (by simp [emb_eq_iff])]; exact hF2,
      SameExcept.refl _ _ _⟩
  have hloop := Runs.rep (cap := cap) (K := R 13) (K2 := R 19) (body := iStep S R) (hner (by decide))
    (visitCost W n n) n (VInv S R cap W τ1 ws sh bit out L0) (by omega)
    (fun k τ v h => vInv_setv S R h 13 (Or.inl rfl) v) (fun k τ v h => vInv_setv S R h 19 (Or.inr rfl) v)
    (by
      intro k hk τ hInv
      obtain ⟨hKD', hpre', hcp', hIX', hK4', hF2', hfr'⟩ := hInv
      have hfr0 := SameExcept.comp' hfr1 hfr'
      have hi : n - 1 - k < n := by omega
      have hpl : ((((List.range n).reverse).take k).flatMap (visitRec W ws sh bit)).length ≤
          (lvlRecs W ws sh bit).length := by
        simp only [lvlRecs, ← hnn]
        conv_rhs => rw [← List.take_append_drop k ((List.range n).reverse)]
        rw [List.flatMap_append, List.length_append]; omega
      have hst := iStep_spec S R cap W τ ws junk sh bit (n - 1 - k) _ (out ++ (((List.range n).reverse).take k).flatMap
        (visitRec W ws sh bit)) L0 hi hpre' hcp' (by rw [hfr0.st (by simp [emb_eq_iff]), hWS])
        (by rw [hfr0.sh (by simp [emb_eq_iff]), hWSh]) (hfr'.numOn (by simp [emb_eq_iff]) hTL1) rfl htlb
        hIX' hK4' hF2' hKD' hw (by rw [show 2 ^ (bit + 3) = 2 * 2 ^ (bit + 2) by ring] at hbit; omega) hsum
        (by rw [List.length_append, ← hnn]; omega) hcapI
      refine (hst.post fun τ' hτ' => ?_).cost (visitCost_mono W n _ (by omega))
      obtain ⟨hKD2, hpre2, hcp2, hIX2, hK42, hF22, hfr2⟩ := hτ'
      refine ⟨⟨?_, hpre2, hcp2, by rw [hIX2]; omega, hK42, hF22, ?_⟩, ?_, ?_⟩
      · rw [take_succ_reverse n k hk, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]; exact hKD2
      · exact hfr'.trans (hfr2.weaken (by simp) (by simp))
      · exact hfr2.val (by simp [emb_eq_iff])
      · exact hfr2.val (by simp [emb_eq_iff]))
    τ1 h0 (by rw [hfr1.val (by simp [emb_eq_iff])]; exact hNR) (by rw [hfr1.val (by simp [emb_eq_iff])]; exact hK3)
  refine hloop.post fun τ hτ => ?_
  obtain ⟨⟨hKD', hpre', hcp', hIX', hK4', hF2', hfr'⟩, hNR', hK3'⟩ := hτ
  have hall : ((List.range n).reverse).take n = (List.range n).reverse := List.take_of_length_le (by simp)
  rw [hall] at hKD'
  have hfr0 := SameExcept.comp' hfr1 hfr'
  refine ⟨hKD', hpre', hcp', ⟨_, hfr'.numOn (by simp [emb_eq_iff]) hC1.choose_spec⟩,
    ⟨_, hfr'.numOn (by simp [emb_eq_iff]) hTL1⟩, by rw [hIX']; omega, hK4', hF2', ?_⟩
  have hys : ∀ y, y ∉ [S 2, S 3, S 4, S 5, S 6, S 7, S 12, S 13, S 14, S 15, S 16, S 17, S 18, S 19] →
      y ∉ [S 12, S 13, S 14, S 16, S 17, S 18, S 19] ++ [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] := by
    intro y hy
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
    tauto
  refine ⟨fun y hy => hfr0.1 y (hys y hy), fun r hr => ?_, hfr0.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  by_cases r10 : r = R 10
  · rw [r10, hIX', hIX]; omega
  · by_cases r13 : r = R 13
    · rw [r13, hNR', hNR]
    · by_cases r19 : r = R 19
      · rw [r19, hK3', hK3]
      · exact hfr0.val (by simp [r10, r13, r19, hr])

end Level5

end NearCubicGates.Close.TabMachine
