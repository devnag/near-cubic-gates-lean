import Proof.Gates.TabMachine.CompileM13

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

/-- The output of the compiler: the records of `compileL ws t`. -/
def compRecs (W : ℕ) (ws : List ℤ) (t : ℤ) : List Bool := (compileL ws t).flatMap fun c => frame (recBits W c)

/-- The anchor: the compiler's output is the shared exact children, record by record. -/
theorem compRecs_children {n : ℕ} (W : ℕ) (w : Fin n → ℤ) (t : ℤ) :
    compRecs W (List.ofFn w) t =
      (NearCubicWires.ThresholdCompiler.erratumSafeDisjointChildren w t).flatMap fun c => frame (recBits W (kidL c)) := by
  unfold compRecs; rw [← compileL_eq, List.flatMap_map]

theorem compRecs_neg (W : ℕ) (ws : List ℤ) (t : ℤ) (h : t + negMassL ws < 0) :
    compRecs W ws t = frame (recBits W (zeroL ws.length 0)) := by
  unfold compRecs compileL; rw [if_pos h]; simp

theorem compRecs_full (W : ℕ) (ws : List ℤ) (t : ℤ) (h1 : ¬ t + negMassL ws < 0)
    (h2 : (totalL ws : ℤ) ≤ t + negMassL ws) : compRecs W ws t = frame (recBits W (zeroL ws.length 1)) := by
  unfold compRecs compileL; rw [if_neg h1, if_pos h2]; simp

theorem compRecs_main (W : ℕ) (ws : List ℤ) (t : ℤ) (h1 : ¬ t + negMassL ws < 0)
    (h2 : ¬ (totalL ws : ℤ) ≤ t + negMassL ws) :
    compRecs W ws t = (List.range (levelsOf (maxL ws) (t + negMassL ws).toNat)).reverse.flatMap
      (lvlRecs W ws (t + negMassL ws).toNat) := by
  unfold compRecs compileL; rw [if_neg h1, if_neg h2]; exact records_main W ws _ _

theorem mainCost_mono (W n L : ℕ) (h : L ≤ W) : mainCost W n L ≤ mainCost W n W := by
  have h1 := Nat.mul_le_mul_right (41 * (W + 1) + 16) h
  have h2 := Nat.mul_le_mul_right (lvlCost W n + 8) h
  unfold mainCost; omega

/-- The compiler's cost. -/
def compileCost (W n : ℕ) : ℕ :=
  preCost W n + 1 + (n * (40 * (W + 1) + 3 + 8) + 7 * n + 3 + 1 + (40 * (W + 1) + 3 + 1 + 7) + mainCost W n W +
    200 * W + 300)

theorem setv_dec_back (σ : WState ns nr) (r : Fin nr) (h : σ.val r = 0) :
    (σ.setv r 1).setv r ((σ.setv r 1).val r - 1) = σ := by
  apply WState.eq <;> try rfl
  funext x; by_cases hx : x = r
  · subst hx; simp [h]
  · simp [Function.update_of_ne hx]

section Whole
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

theorem sameExcept_outSt (σ : WState ns nr) (out L0 : List Bool) :
    SameExcept σ (outSt σ (S 2) (R 14) out L0) [S 2] [R 14] :=
  ⟨fun x hx => by simp only [List.mem_singleton] at hx; simp [outSt, Function.update_of_ne hx],
    fun r hr => by simp only [List.mem_singleton] at hr; simp [outSt, Function.update_of_ne hr], by simp [outSt]⟩

theorem compPre_sets {cap W : ℕ} {σ : WState ns nr} (h : CompPre S R cap W σ) (k : Fin 24)
    (hk : k ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23]) (v : ℕ) :
    CompPre S R cap W (σ.sets (S k) (frame (binary (W + 1) v))) := by
  have hk3 : k ≠ 3 := by rintro rfl; exact absurd hk (by decide)
  have hk20 : k ≠ 20 := by rintro rfl; exact absurd hk (by decide)
  have hk21 : k ≠ 21 := by rintro rfl; exact absurd hk (by decide)
  refine compPre_frame S R h (sameExcept_sets σ (S := [S k]) (Rg := []) (by simp) _) ?_ ?_
    (by simp [emb_eq_iff, Ne.symm hk20]) (by simp [emb_eq_iff, Ne.symm hk21])
  · intro j _ hj
    simp only [List.mem_singleton, emb_eq_iff] at hj
    subst hj
    exact ⟨v, BinW.numOn_sets_self _ _ _ _ (h.words j hk).choose_spec.2⟩
  · intro h3; simp only [List.mem_singleton, emb_eq_iff] at h3; exact absurd h3.symm hk3

/-- **The exact-test compiler** (lem:exact): prologue, then `0 = 0` (target below the negative mass), or `0 = 1`
(target at least the total), or the first-crossing levels. -/
def compileP : WMX ns nr :=
  .seq (preP S R)
  (.ifr (R 21) (.seq (WMX.dec (R 21)) (zeroEq S R 20))
    (.seq (BinW.copy (S 23) (S 1) (R 2) (R 3))
    (.seq (BinW.half (S 23) (R 3))
    (.seq (BinW.lt (S 23) (S 9) (R 2) (R 3))
    (.ifr (R 2) (.seq (WMX.dec (R 2)) (mainP S R)) (zeroEq S R 21))))))

/-- The compiler's postcondition. -/
def CompPost (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (t : ℤ) (out L0 : List Bool) (τ : WState ns nr) : Prop :=
  OutOn τ (S 2) (R 14) (out ++ compRecs W ws t) L0 ∧ CompPre S R cap W τ ∧ (∃ v, NumOn τ (S 1) (W + 1) v) ∧
    τ.val (R 13) = ws.length ∧
    SameExcept σ τ [S 1, S 2, S 3, S 4, S 5, S 6, S 7, S 8, S 9, S 10, S 12, S 13, S 14, S 15, S 16, S 17, S 18,
      S 19, S 22, S 23] [R 14]

theorem compile_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (t : ℤ) (out L0 : List Bool)
    (hpre : CompPre S R cap W σ) (hS1 : ∃ v, NumOn σ (S 1) (W + 1) v) (hT : SNumOn σ (S 11) W t)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hNR : σ.val (R 13) = ws.length) (hKD : OutOn σ (S 2) (R 14) out L0)
    (hB : 4 * totalL ws + 2 * ws.length + 4 ≤ 2 ^ W) (ht : t.natAbs + totalL ws < 2 ^ W)
    (hcap : out.length + (compRecs W ws t).length + (ws.length + 1) * (2 * (W + 1) + 1) + 2 * ws.length + 4 * W + 8 ≤
      cap) :
    Runs cap (compileP S R) σ (compileCost W ws.length) (CompPost S R cap W σ ws t out L0) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have hreg := hpre.regs
  have hc1 : (ws.length + 1) * (2 * (W + 1) + 1) = ws.length * (2 * (W + 1) + 1) + (2 * (W + 1) + 1) := by ring
  have hp := preP_spec S R cap W σ ws junk t hpre hS1 hT hWS hWSh hB ht (by omega)
  refine (Runs.seq (c2 := ws.length * (40 * (W + 1) + 3 + 8) + 7 * ws.length + 3 + 1 + (40 * (W + 1) + 3 + 1 + 7) +
    mainCost W ws.length W + 200 * W + 300) hp fun τ hτ => ?_).cost (by unfold compileCost; omega)
  obtain ⟨hX, h21, h9, h10, hcp, hfr⟩ := hτ
  have hfr0 : SameExcept σ (τ.setv (R 21) 0) [S 1, S 3, S 4, S 6, S 7, S 8, S 9, S 10] [] :=
    sameExcept_clear hfr (hreg 21 (by decide) (by decide))
  have hzcap : out.length + (ws.length + 1) * (2 * (W + 1)) + 2 * ws.length + 2 ≤ cap := by
    have : (ws.length + 1) * (2 * (W + 1)) ≤ (ws.length + 1) * (2 * (W + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hframe : ∀ x, x ∈ [S 1, S 3, S 4, S 6, S 7, S 8, S 9, S 10] → x ∈ [S 1, S 2, S 3, S 4, S 5, S 6, S 7, S 8,
      S 9, S 10, S 12, S 13, S 14, S 15, S 16, S 17, S 18, S 19, S 22, S 23] := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> simp [h]
  by_cases hneg : t + negMassL ws < 0
  · -- the constant child `0 = 0`
    have hv : τ.val (R 21) ≠ 0 := by rw [h21]; simp [hneg]
    have hd := WXExec.dec cap (R 21) τ (by rw [h21]; simp [hneg]; have := hpre.cap; omega)
    have e : τ.setv (R 21) (τ.val (R 21) - 1) = τ.setv (R 21) 0 := by rw [h21]; simp [hneg]
    rw [e] at hd
    have hKD0 : OutOn (τ.setv (R 21) 0) (S 2) (R 14) out L0 :=
      ⟨by rw [hfr0.st (by simp [emb_eq_iff])]; exact hKD.1, by rw [hfr0.sh (by simp [emb_eq_iff])]; exact hKD.2.1,
        by rw [hfr0.val (by simp)]; exact hKD.2.2⟩
    have hz := zeroEq_spec S R cap W 20 (by decide) (τ.setv (R 21) 0) ws.length 0 out L0 hcp.zr
      (by rw [show encS 0 = 0 by simp [encS]]; exact hcp.zr) (by rw [hfr0.val (by simp)]; exact hNR)
      (hcp.regs 19 (by decide) (by decide)) (hcp.regs 15 (by decide) (by decide)) hKD0 hzcap
    have hfz := sameExcept_outSt S R (τ.setv (R 21) 0) (out ++ frame (recBits W (zeroL ws.length 0))) L0
    refine (Runs.ifrT hv (Runs.seqE hd (Runs.of hz ⟨?_, compPre_outSt S R hcp _ _,
      ⟨_, hfz.numOn (by simp [emb_eq_iff]) (BinW.numOn_setv hX.1 _ _)⟩, ?_, ?_⟩))).cost (by omega)
    · rw [compRecs_neg W ws t hneg]; exact outOn_outSt _ _ _ _ _
    · rw [hfz.val (by simp [emb_eq_iff]), hfr0.val (by simp)]; exact hNR
    · refine (hfr0.comp' hfz).weaken ?_ (by simp)
      intro x hx; rw [List.mem_append] at hx
      rcases hx with h | h
      · exact hframe x h
      · simp only [List.mem_singleton] at h; simp [h]
  have h21' : τ.val (R 21) = 0 := by rw [h21]; simp [hneg]
  have hτ0 : τ.setv (R 21) 0 = τ := BinW.setv_same h21'
  rw [hτ0] at hcp hfr0
  have hv0 : τ.val (R 21) = 0 := h21'
  obtain ⟨sh, hshd⟩ : ∃ sh, sh = (t + negMassL ws).toNat := ⟨_, rfl⟩
  have hsh2 : encS (t + negMassL ws) / 2 = sh := by rw [SInt.encS_div]; omega
  obtain ⟨m23, hm23⟩ := hcp.words 23 (by decide)
  have e1 := BinW.copy_spec (A := S 23) (B := S 1) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) τ m23 _ hm23 hX.1 (hcp.regs 2 (by decide) (by decide)) (hcp.regs 3 (by decide) (by decide))
    hcp.cap
  have e2 := BinW.half_spec (A := S 23) (R := R 3) cap (W + 1)
    (τ.sets (S 23) (frame (binary (W + 1) (encS (t + negMassL ws))))) (encS (t + negMassL ws))
    (BinW.numOn_sets_self _ _ _ _ hm23.2) (by simp; exact hcp.regs 3 (by decide) (by decide)) (SInt.SNumOn.lt hX)
    (by have := hcp.cap; omega)
  rw [hsh2, BinW.sets_sets] at e2
  have hfrb : SameExcept τ (τ.sets (S 23) (frame (binary (W + 1) sh))) [S 23] [] :=
    sameExcept_sets τ (by simp) _
  have hcpb : CompPre S R cap W (τ.sets (S 23) (frame (binary (W + 1) sh))) := compPre_sets S R hcp 23 (by decide) sh
  have hMSb : NumOn (τ.sets (S 23) (frame (binary (W + 1) sh))) (S 23) (W + 1) sh :=
    BinW.numOn_sets_self _ _ _ _ hm23.2
  have hmaxW : maxL ws < 2 ^ W := by have := maxL_le ws; omega
  have hW2 : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hshW : sh < 2 ^ (W + 1) := by
    have := SInt.SNumOn.lt hX; have := SInt.encS_div (t + negMassL ws); omega
  have e3 := BinW.lt_spec (A := S 23) (B := S 9) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) (τ.sets (S 23) (frame (binary (W + 1) sh))) sh (totalL ws) hMSb
    (hfrb.numOn (by simp [emb_eq_iff]) h9) (hcpb.regs 2 (by decide) (by decide))
    (hcpb.regs 3 (by decide) (by decide)) hshW (by omega) hcp.cap
  have hall : SameExcept σ (τ.sets (S 23) (frame (binary (W + 1) sh))) ([S 1, S 3, S 4, S 6, S 7, S 8, S 9, S 10] ++
      [S 23]) [] := by simpa using hfr0.comp' hfrb
  have hKDb : OutOn (τ.sets (S 23) (frame (binary (W + 1) sh))) (S 2) (R 14) out L0 :=
    ⟨by rw [hall.st (by simp [emb_eq_iff])]; exact hKD.1, by rw [hall.sh (by simp [emb_eq_iff])]; exact hKD.2.1,
      by rw [hall.val (by simp)]; exact hKD.2.2⟩
  have hNRb : (τ.sets (S 23) (frame (binary (W + 1) sh))).val (R 13) = ws.length := by
    rw [hall.val (by simp)]; exact hNR
  have hS1b : ∃ v, NumOn (τ.sets (S 23) (frame (binary (W + 1) sh))) (S 1) (W + 1) v :=
    ⟨_, hfrb.numOn (by simp [emb_eq_iff]) hX.1⟩
  have hframe' : ∀ x, x ∈ [S 1, S 3, S 4, S 6, S 7, S 8, S 9, S 10] ++ [S 23] → x ∈ [S 1, S 2, S 3, S 4, S 5, S 6,
      S 7, S 8, S 9, S 10, S 12, S 13, S 14, S 15, S 16, S 17, S 18, S 19, S 22, S 23] := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with h | h
    · exact hframe x h
    · simp only [List.mem_singleton] at h; simp [h]
  by_cases hlt : sh < totalL ws
  · -- the levels
    have hdec1 : (decide (sh < totalL ws)).toNat = 1 := by simp [hlt]
    rw [hdec1] at e3
    have hv : ((τ.sets (S 23) (frame (binary (W + 1) sh))).setv (R 2) 1).val (R 2) ≠ 0 := by simp
    have hd := WXExec.dec cap (R 2) ((τ.sets (S 23) (frame (binary (W + 1) sh))).setv (R 2) 1)
      (by simp; have := hpre.cap; omega)
    rw [setv_dec_back _ _ (hcpb.regs 2 (by decide) (by decide))] at hd
    have hn : 0 < ws.length := by
      rcases ws with _ | ⟨a, l⟩
      · simp [totalL] at hlt
      · simp
    have hz2 : ¬ (totalL ws : ℤ) ≤ t + negMassL ws := by omega
    have hrec := compRecs_main W ws t hneg hz2
    rw [← hshd] at hrec
    obtain ⟨hb, hL⟩ := lvBounds_of cap W ws sh out hB hlt (by rw [← hrec]; exact hcap)
    have hmain := mainP_spec S R cap W (τ.sets (S 23) (frame (binary (W + 1) sh))) ws junk sh (maxL ws) out L0 hn hcpb
      hMSb (hfrb.numOn (by simp [emb_eq_iff]) h10) (by rw [hall.st (by simp [emb_eq_iff]), hWS])
      (by rw [hall.sh (by simp [emb_eq_iff]), hWSh]) hNRb hKDb (by omega) hL hb (by omega)
    have hmc := mainCost_mono W ws.length (levelsOf (maxL ws) sh) (by omega)
    refine (Runs.ifrF hv0 (Runs.seqE e1 (Runs.seqE e2 (Runs.seqE e3 (Runs.ifrT hv (Runs.seqE hd
      (hmain.post fun ρ hρ => ?_))))))).cost (by omega)
    obtain ⟨hKDρ, hcpρ, hNRρ, hfrρ⟩ := hρ
    refine ⟨by rw [hrec]; exact hKDρ, hcpρ, hS1b.elim fun v h => ⟨v, hfrρ.numOn (by simp [emb_eq_iff]) h⟩, hNRρ, ?_⟩
    refine (hall.comp' hfrρ).weaken ?_ (by simp)
    intro x hx; rw [List.mem_append] at hx
    rcases hx with h | h
    · exact hframe' x h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · -- the constant child `0 = 1`
    have hr2 : (τ.sets (S 23) (frame (binary (W + 1) sh))).val (R 2) = 0 := hcpb.regs 2 (by decide) (by decide)
    have hdec0 : (decide (sh < totalL ws)).toNat = 0 := by simp [hlt]
    have hv : ((τ.sets (S 23) (frame (binary (W + 1) sh))).setv (R 2) (decide (sh < totalL ws)).toNat).val (R 2) = 0 :=
      by simp [hlt]
    have e4 : (τ.sets (S 23) (frame (binary (W + 1) sh))).setv (R 2) (decide (sh < totalL ws)).toNat =
        τ.sets (S 23) (frame (binary (W + 1) sh)) := by rw [hdec0]; exact BinW.setv_same hr2
    rw [e4] at e3
    rw [e4] at hv
    have hz := zeroEq_spec S R cap W 21 (by decide) (τ.sets (S 23) (frame (binary (W + 1) sh))) ws.length 1 out L0
      hcpb.zr (by rw [show encS 1 = 2 by simp [encS]]; exact hcpb.tw) hNRb (hcpb.regs 19 (by decide) (by decide))
      (hcpb.regs 15 (by decide) (by decide)) hKDb hzcap
    have hfz := sameExcept_outSt S R (τ.sets (S 23) (frame (binary (W + 1) sh)))
      (out ++ frame (recBits W (zeroL ws.length 1))) L0
    refine (Runs.ifrF hv0 (Runs.seqE e1 (Runs.seqE e2 (Runs.seqE e3 (Runs.ifrF hv (Runs.of hz ⟨?_,
      compPre_outSt S R hcpb _ _, hS1b.elim fun v h => ⟨v, hfz.numOn (by simp [emb_eq_iff]) h⟩, ?_, ?_⟩)))))).cost
      (by omega)
    · rw [compRecs_full W ws t hneg (by omega)]; exact outOn_outSt _ _ _ _ _
    · rw [hfz.val (by simp [emb_eq_iff])]; exact hNRb
    · refine (hall.comp' hfz).weaken ?_ (by simp)
      intro x hx; rw [List.mem_append] at hx
      rcases hx with h | h
      · exact hframe' x h
      · simp only [List.mem_singleton] at h; simp [h]

end Whole

end NearCubicGates.Close.TabMachine
