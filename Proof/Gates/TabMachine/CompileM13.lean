import Proof.Gates.TabMachine.CompileM12

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

/-! ## Arithmetic -/

theorem natAbs_le_totalL {ws : List ℤ} {z : ℤ} (hz : z ∈ ws) : z.natAbs ≤ totalL ws := by
  unfold totalL; exact List.le_sum_of_mem (List.mem_map.2 ⟨z, hz, rfl⟩)

theorem sum_odd (ws : List ℤ) : (ws.map fun z => 2 * z.natAbs + 1).sum = 2 * totalL ws + ws.length := by
  unfold totalL
  induction ws with
  | nil => simp
  | cons z l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem two_pow_levels_le (m T : ℕ) (hm : m ≤ T) (hT : 1 ≤ T) : 2 ^ (max 1 (Nat.size m)) ≤ 2 * T := by
  rcases Nat.lt_or_ge 1 (Nat.size m) with h | h
  · rw [max_eq_right h.le]
    have h1 : ¬ Nat.size m ≤ Nat.size m - 1 := by omega
    rw [Nat.size_le] at h1
    have e : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · rw [max_eq_left h]; omega

theorem lvBounds_of (cap W : ℕ) (ws : List ℤ) (sh : ℕ) (out : List Bool)
    (hB : 4 * totalL ws + 2 * ws.length + 4 ≤ 2 ^ W) (hsh : sh < totalL ws)
    (hcap : out.length + ((List.range (levelsOf (maxL ws) sh)).reverse.flatMap (lvlRecs W ws sh)).length +
      (ws.length + 1) * (2 * (W + 1) + 1) + 2 * ws.length + 4 * W + 8 ≤ cap) :
    LvBounds cap W ws sh (levelsOf (maxL ws) sh) out ∧ levelsOf (maxL ws) sh + 1 ≤ W := by
  set T := totalL ws with hTdef
  set L := levelsOf (maxL ws) sh with hL
  have hT : 1 ≤ T := by omega
  have hM : max (maxL ws) sh ≤ T := max_le (maxL_le ws) hsh.le
  have hpL : 2 ^ L ≤ 2 * T := two_pow_levels_le _ _ hM hT
  have hW2 : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
  have hLW : L + 1 ≤ W := by
    by_contra hc
    have : 2 ^ W ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨⟨by omega, fun bit hbit => ?_, ?_, fun z hz => ?_, ?_, by omega, by omega, by omega⟩, hLW⟩
  · have h1 : sh / 2 ^ bit * 2 ^ bit ≤ sh := Nat.div_mul_le_self sh (2 ^ bit)
    have h2 : 2 * 2 ^ bit ≤ 2 ^ L := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hbit
    have e : 2 * 2 ^ bit * (sh / 2 ^ bit + 1) = 2 * (sh / 2 ^ bit * 2 ^ bit) + 2 * 2 ^ bit := by ring
    rw [e]; omega
  · rw [show 2 ^ (L + 2) = 4 * 2 ^ L by ring]; omega
  · have := natAbs_le_totalL hz; omega
  · rw [sum_odd]; omega

/-! ## Frames of the working state -/

section Frames
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

theorem sameExcept_clear {σ τ : WState ns nr} {Ls : List (Fin (ns + 1))} {r : Fin nr} (h : SameExcept σ τ Ls [r])
    (h0 : σ.val r = 0) : SameExcept σ (τ.setv r 0) Ls [] :=
  ⟨fun x hx => by simpa using h.1 x hx, fun q _ => by
    by_cases hq : q = r
    · subst hq; simp [h0]
    · simp only [WState.setv_val, Function.update_of_ne hq]; exact h.2.1 q (by simpa using hq),
    by simpa using h.2.2⟩

theorem compPre_frame {cap W : ℕ} {σ τ : WState ns nr} {Ls : List (Fin (ns + 1))} (h : CompPre S R cap W σ)
    (hfr : SameExcept σ τ Ls [])
    (hw : ∀ k : Fin 24, k ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] →
      S k ∈ Ls → ∃ v, NumOn τ (S k) (W + 1) v)
    (h3 : S 3 ∈ Ls → τ.sh (S 3) = 0 ∧ (τ.st (S 3)).length ≤ 2 * (W + 1) + 1) (h20 : S 20 ∉ Ls)
    (h21 : S 21 ∉ Ls) : CompPre S R cap W τ where
  words k hk := by
    by_cases hm : S k ∈ Ls
    · exact hw k hk hm
    · obtain ⟨v, hv⟩ := h.words k hk; exact ⟨v, hfr.numOn hm hv⟩
  wkh := by
    by_cases hm : S 3 ∈ Ls
    · exact (h3 hm).1
    · rw [hfr.sh hm]; exact h.wkh
  wkl := by
    by_cases hm : S 3 ∈ Ls
    · exact (h3 hm).2
    · rw [hfr.st hm]; exact h.wkl
  zr := hfr.numOn h20 h.zr
  tw := hfr.numOn h21 h.tw
  regs k h13 h14 := by rw [hfr.val (by simp)]; exact h.regs k h13 h14
  cap := h.cap

theorem compPre_outSt {cap W : ℕ} {σ : WState ns nr} (h : CompPre S R cap W σ) (out L0 : List Bool) :
    CompPre S R cap W (outSt σ (S 2) (R 14) out L0) := by
  have hfr : SameExcept σ (outSt σ (S 2) (R 14) out L0) [S 2] [R 14] :=
    ⟨fun x hx => by simp only [List.mem_singleton] at hx; simp [outSt, Function.update_of_ne hx],
      fun r hr => by simp only [List.mem_singleton] at hr; simp [outSt, Function.update_of_ne hr], by simp [outSt]⟩
  exact ⟨fun k hk => (h.words k hk).elim fun v hv => ⟨v, hfr.numOn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp [emb_eq_iff]) hv⟩,
    by rw [hfr.sh (by simp [emb_eq_iff])]; exact h.wkh, by rw [hfr.st (by simp [emb_eq_iff])]; exact h.wkl,
    hfr.numOn (by simp [emb_eq_iff]) h.zr, hfr.numOn (by simp [emb_eq_iff]) h.tw,
    fun k h13 h14 => by rw [hfr.val (by simp [emb_eq_iff, h14])]; exact h.regs k h13 h14, h.cap⟩

/-! ## The prologue -/

def preP : WMX ns nr :=
  .seq (stats S R)
  (.seq (BinW.copy (S 1) (S 11) (R 2) (R 3))
  (.seq (BinW.copy (S 6) (S 8) (R 2) (R 3))
  (.seq (BinW.shl (S 6) (S 20) (R 2) (R 3))
  (.seq (SInt.sadd (S 1) (S 6) (S 4) (S 7) (R 4) (R 5) (R 2) (R 3))
  (.wm (SInt.sgnBitW (S 1) (R 21)))))))

/-- The prologue's cost. -/
def preCost (W n : ℕ) : ℕ :=
  3 * (41 * (W + 1) + 4) + n * (450 * W + 600 + (50 * (W + 1) + 30)) + 3 + 600 * W + 800

theorem preP_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (t : ℤ)
    (hpre : CompPre S R cap W σ) (hS1 : ∃ v, NumOn σ (S 1) (W + 1) v) (hT : SNumOn σ (S 11) W t)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hB : 4 * totalL ws + 2 * ws.length + 4 ≤ 2 ^ W) (ht : t.natAbs + totalL ws < 2 ^ W)
    (hcap : ws.length * (2 * (W + 1) + 1) + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap (preP S R) σ (preCost W ws.length) (fun τ =>
      SNumOn τ (S 1) W (t + negMassL ws) ∧ τ.val (R 21) = (decide (t + negMassL ws < 0)).toNat ∧
      NumOn τ (S 9) (W + 1) (totalL ws) ∧ NumOn τ (S 10) (W + 1) (maxL ws) ∧
      CompPre S R cap W (τ.setv (R 21) 0) ∧
      SameExcept σ τ [S 1, S 3, S 4, S 6, S 7, S 8, S 9, S 10] [R 21]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have hreg := hpre.regs
  have hw : ∀ z ∈ ws, z.natAbs < 2 ^ W := fun z hz => by have := natAbs_le_totalL hz; omega
  have hs := stats_spec S R cap W σ ws junk hWS hWSh (hreg 0 (by decide) (by decide)) (hreg 1 (by decide) (by decide))
    hpre.wkh hpre.wkl (hpre.words 4 (by decide)) (hpre.words 8 (by decide)) (hpre.words 9 (by decide))
    (hpre.words 10 (by decide)) hpre.zr (hreg 4 (by decide) (by decide)) (hreg 2 (by decide) (by decide))
    (hreg 3 (by decide) (by decide)) hw (by omega) hcap
  refine (Runs.seq (c2 := 41 * (W + 1) + 3 + 1 + (41 * (W + 1) + 3 + 1 + (41 * (W + 1) + 8 + 1 +
    (410 * W + 600 + 1 + 8)))) hs fun τ1 h1 => ?_).cost (by unfold preCost; omega)
  obtain ⟨h8, h9, h10, ⟨m4, h4⟩, hsh3, hlen3, hfr1⟩ := h1
  obtain ⟨v1, hv1⟩ := hS1
  have hv1' : NumOn τ1 (S 1) (W + 1) v1 := hfr1.numOn (by simp [emb_eq_iff]) hv1
  have hT1 : SNumOn τ1 (S 11) W t := SInt.SameExcept.sNumOn hfr1 (by simp [emb_eq_iff]) hT
  have hval1 : ∀ r, τ1.val r = σ.val r := fun r => hfr1.val (by simp)
  have hc : 2 * (W + 1) + 1 ≤ cap := hpre.cap
  have e1 := BinW.copy_spec (A := S 1) (B := S 11) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) τ1 v1 (encS t) hv1' hT1.1 (by rw [hval1]; exact hreg 2 (by decide) (by decide))
    (by rw [hval1]; exact hreg 3 (by decide) (by decide)) hc
  set τ2 := τ1.sets (S 1) (frame (binary (W + 1) (encS t))) with hτ2
  obtain ⟨x0, hx0⟩ := hpre.words 6 (by decide)
  have hx0' : NumOn τ2 (S 6) (W + 1) x0 :=
    BinW.numOn_sets_ne (hfr1.numOn (by simp [emb_eq_iff]) hx0) (hne (by decide)) _
  have e2 := BinW.copy_spec (A := S 6) (B := S 8) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) τ2 x0 (negN ws) hx0' (BinW.numOn_sets_ne h8 (hne (by decide)) _)
    (by simp [hτ2, hval1, hreg 2 (by decide) (by decide)]) (by simp [hτ2, hval1, hreg 3 (by decide) (by decide)]) hc
  set τ3 := τ2.sets (S 6) (frame (binary (W + 1) (negN ws))) with hτ3
  obtain ⟨z0, hz0⟩ := hpre.words 7 (by decide)
  have e3 := BinW.shl_spec (A := S 6) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) τ3 (negN ws) 0 (BinW.numOn_sets_self _ _ _ _ hx0'.2)
    (by
      refine BinW.numOn_sets_ne (BinW.numOn_sets_ne (hfr1.numOn (by simp [emb_eq_iff]) hpre.zr) (hne (by decide)) _)
        (hne (by decide)) _)
    (by simp [hτ3, hτ2, hval1, hreg 2 (by decide) (by decide)])
    (by simp [hτ3, hτ2, hval1, hreg 3 (by decide) (by decide)]) hc
  set τ4 := τ3.sets (S 6) (frame (binary (W + 1) (2 * negN ws))) with hτ4
  have hfr4 : SameExcept τ1 τ4 [S 1, S 6] [] := by
    refine ⟨fun y hy => ?_, fun r _ => by simp [hτ4, hτ3, hτ2], by simp [hτ4, hτ3, hτ2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hτ4, hτ3, hτ2, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
  have hnegW : negN ws < 2 ^ W := by have := negN_le ws; omega
  have hX4 : SNumOn τ4 (S 1) W t := ⟨BinW.numOn_sets_ne (BinW.numOn_sets_ne
    (BinW.numOn_sets_self _ _ _ _ hv1'.2) (hne (by decide)) _) (hne (by decide)) _, hT1.2⟩
  have hY4 : SNumOn τ4 (S 6) W (negN ws : ℤ) := ⟨by
      rw [encS_natCast]; exact BinW.numOn_sets_self _ _ _ _ (by
        simp [hτ3, hτ2, emb_eq_iff, (hfr1.numOn (by simp [emb_eq_iff]) hx0).2]),
    by simpa using hnegW⟩
  have hxy : (t + (negN ws : ℤ)).natAbs < 2 ^ W := by
    have := Int.natAbs_add_le t (negN ws : ℤ); have := negN_le ws; simp only [Int.natAbs_natCast] at *; omega
  have hsa := SInt.sadd_spec cap W (X := S 1) (Y := S 6) (M := S 4) (N := S 7) (S := R 4) (T := R 5) (F := R 2)
    (R := R 3) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) τ4 t (negN ws) m4 z0 hX4 hY4
    (hfr4.numOn (by simp [emb_eq_iff]) h4) (hfr4.numOn (by simp [emb_eq_iff]) (hfr1.numOn (by simp [emb_eq_iff]) hz0))
    (by rw [hfr4.val (by simp), hval1]; exact hreg 4 (by decide) (by decide))
    (by rw [hfr4.val (by simp), hval1]; exact hreg 5 (by decide) (by decide))
    (by rw [hfr4.val (by simp), hval1]; exact hreg 2 (by decide) (by decide))
    (by rw [hfr4.val (by simp), hval1]; exact hreg 3 (by decide) (by decide)) hxy hc
  refine Runs.seqE e1 (Runs.seqE e2 (Runs.seqE e3 (Runs.seq (c2 := 8) hsa fun τ5 h5 => ?_)))
  obtain ⟨hX5, ⟨a5, hM5⟩, ⟨b5, hN5⟩, hfr5⟩ := h5
  have hz : t + (negN ws : ℤ) = t + negMassL ws := by rw [negN_cast]
  rw [hz] at hX5
  have hR21 : τ5.val (R 21) = 0 := by
    rw [hfr5.val (by simp), hfr4.val (by simp), hval1]; exact hreg 21 (by decide) (by decide)
  set τ := τ5.setv (R 21) (encS (t + negMassL ws) % 2) with hτ
  have hF : SameExcept σ τ [S 1, S 3, S 4, S 6, S 7, S 8, S 9, S 10] [R 21] := by
    have hall := (hfr1.comp' hfr4).comp' hfr5
    refine (hall.comp' (sameExcept_setv τ5 (S := []) (Rg := [R 21]) (by simp) _)).weaken ?_ (by simp)
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with ((h | h | h | h | h) | (h | h)) | (h | h | h) <;> simp [h]
  have hfr45 : ∀ k : Fin 24, k ∉ [(1 : Fin 24), 4, 7] → ∀ {v : ℕ}, NumOn τ4 (S k) (W + 1) v →
      NumOn ((τ.setv (R 21) 0)) (S k) (W + 1) v := by
    intro k hk v hv
    refine BinW.numOn_setv (BinW.numOn_setv (hfr5.numOn ?_ hv) _ _) _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [emb_eq_iff, hk.1, hk.2.1, hk.2.2]
  have hcp : CompPre S R cap W (τ.setv (R 21) 0) := by
    refine compPre_frame S R hpre (sameExcept_clear hF (hreg 21 (by decide) (by decide))) ?_ ?_ (by simp [emb_eq_iff])
      (by simp [emb_eq_iff])
    · intro k hk hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)
      · exact ⟨a5, BinW.numOn_setv (BinW.numOn_setv hM5 _ _) _ _⟩
      · exact ⟨_, hfr45 6 (by decide) (BinW.numOn_sets_self _ _ _ _ (by
          simp [hτ3, hτ2, emb_eq_iff, (hfr1.numOn (by simp [emb_eq_iff]) hx0).2]))⟩
      · exact ⟨b5, BinW.numOn_setv (BinW.numOn_setv hN5 _ _) _ _⟩
      · exact ⟨_, hfr45 8 (by decide) (hfr4.numOn (by simp [emb_eq_iff]) h8)⟩
      · exact ⟨_, hfr45 9 (by decide) (hfr4.numOn (by simp [emb_eq_iff]) h9)⟩
      · exact ⟨_, hfr45 10 (by decide) (hfr4.numOn (by simp [emb_eq_iff]) h10)⟩
    · intro _
      have e1 : τ5.st (S 3) = τ1.st (S 3) := by
        rw [hfr5.st (by simp [emb_eq_iff]), hfr4.st (by simp [emb_eq_iff])]
      have e2 : τ5.sh (S 3) = τ1.sh (S 3) := by
        rw [hfr5.sh (by simp [emb_eq_iff]), hfr4.sh (by simp [emb_eq_iff])]
      exact ⟨by simp [hτ, e2, hsh3], by simp [hτ, e1, hlen3]⟩
  refine Runs.of (WXExec.wm (SInt.sgnBitW_spec cap τ5 W _ hX5.1 hR21 (by omega))) ⟨?_, ?_, ?_, ?_, hcp, hF⟩
  · exact ⟨BinW.numOn_setv hX5.1 _ _, hX5.2⟩
  · simp only [WState.setv_val, Function.update_self, SInt.encS_mod]
    by_cases h : t + negMassL ws < 0 <;> simp [h]
  · exact BinW.numOn_setv (hfr5.numOn (by simp [emb_eq_iff]) (hfr4.numOn (by simp [emb_eq_iff]) h9)) _ _
  · exact BinW.numOn_setv (hfr5.numOn (by simp [emb_eq_iff]) (hfr4.numOn (by simp [emb_eq_iff]) h10)) _ _

end Frames

end NearCubicGates.Close.TabMachine
