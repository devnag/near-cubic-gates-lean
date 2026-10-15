import Proof.Gates.TabMachine.CompileM11

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

section Main
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- The compiler's working state at rest: scratch words, constants, zero registers (`R 13 = n`, `R 14` the output
counter excepted). -/
structure CompPre (cap W : ℕ) (σ : WState ns nr) : Prop where
  words : ∀ k : Fin 24, k ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] →
    ∃ v, NumOn σ (S k) (W + 1) v
  wkh : σ.sh (S 3) = 0
  wkl : (σ.st (S 3)).length ≤ 2 * (W + 1) + 1
  zr : NumOn σ (S 20) (W + 1) 0
  tw : NumOn σ (S 21) (W + 1) 2
  regs : ∀ k : Fin 24, k ≠ 13 → k ≠ 14 → σ.val (R k) = 0
  cap : 2 * (W + 1) + 1 ≤ cap

/-- The main branch. -/
def mainP : WMX ns nr :=
  .seq (BinW.copy (S 22) (S 10) (R 2) (R 3))
  (.seq (BinW.lt (S 22) (S 23) (R 2) (R 3))
  (.seq (.ifr (R 2) (.seq (WMX.dec (R 2)) (BinW.copy (S 22) (S 23) (R 2) (R 3))) WMX.skip)
  (.seq (sizeP S R)
  (.seq (powP S R)
  (.seq (repK (R 9) (R 8) (lvl S R))
  (.wm (WM.clear (R 9))))))))

/-- The level count of the main branch. -/
def levelsOf (mx sh : ℕ) : ℕ := max 1 (Nat.size (max mx sh))

/-- The main branch's cost bound. -/
def mainCost (W n L : ℕ) : ℕ := 400 * W + 600 + ((W + 1) * (80 * W + 150) + 300 * W + 400) +
  (L * (41 * (W + 1) + 16) + 200 * W + 300) + (L * (lvlCost W n + 8) + 7 * L + 3) + 3 * L + 10

theorem compPre_word {cap W : ℕ} {σ : WState ns nr} (h : CompPre S R cap W σ) (k : Fin 24)
    (hk : k ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23]) :
    ∃ v, NumOn σ (S k) (W + 1) v := h.words k hk

theorem compPre_of {cap W : ℕ} {τ : WState ns nr} {pw : ℕ} (hb : BodyPre S R cap W τ pw)
    (hc : ChildPre S R cap W τ) (hC : ∃ v, NumOn τ (S 19) (W + 1) v) (hTL : ∃ v, NumOn τ (S 14) (W + 1) v)
    (h8 : ∃ v, NumOn τ (S 8) (W + 1) v) (h9 : ∃ v, NumOn τ (S 9) (W + 1) v) (h10 : ∃ v, NumOn τ (S 10) (W + 1) v)
    (h11 : ∃ v, NumOn τ (S 11) (W + 1) v) (h22 : ∃ v, NumOn τ (S 22) (W + 1) v)
    (h23 : ∃ v, NumOn τ (S 23) (W + 1) v) (htw : NumOn τ (S 21) (W + 1) 2)
    (hregs : ∀ k : Fin 24, k ≠ 13 → k ≠ 14 → τ.val (R k) = 0) : CompPre S R cap W τ where
  words := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [hb.m, hc.n, hb.x, hc.y, h8, h9, h10, h11, ⟨_, hb.hpw⟩, ⟨_, hb.hpw2⟩, hTL, hc.no, hb.q, hb.rm, hb.dx, hC,
      h22, h23]
  wkh := hc.wkh
  wkl := hc.wkl
  zr := hb.zr
  tw := htw
  regs := hregs
  cap := hb.cap

theorem mainP_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (sh mx : ℕ) (out L0 : List Bool)
    (hn : 0 < ws.length) (hpre : CompPre S R cap W σ) (hMS : NumOn σ (S 23) (W + 1) sh)
    (hMX : NumOn σ (S 10) (W + 1) mx)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hNR : σ.val (R 13) = ws.length) (hKD : OutOn σ (S 2) (R 14) out L0)
    (hmx : mx < 2 ^ (W + 1)) (hL : levelsOf mx sh + 1 ≤ W)
    (hb : LvBounds cap W ws sh (levelsOf mx sh) out) (hcapW : 4 * (W + 1) + 4 + 2 * levelsOf mx sh ≤ cap) :
    Runs cap (mainP S R) σ (mainCost W ws.length (levelsOf mx sh)) (fun τ =>
      OutOn τ (S 2) (R 14) (out ++ (List.range (levelsOf mx sh)).reverse.flatMap (lvlRecs W ws sh)) L0 ∧
      CompPre S R cap W τ ∧ τ.val (R 13) = ws.length ∧
      SameExcept σ τ [S 2, S 3, S 4, S 5, S 6, S 7, S 12, S 13, S 14, S 15, S 16, S 17, S 18, S 19, S 22] [R 14]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have hreg : ∀ k : Fin 24, k ≠ 13 → k ≠ 14 → σ.val (R k) = 0 := hpre.regs
  set L := levelsOf mx sh with hLdef
  obtain ⟨mm0, hmm0⟩ := hpre.words 22 (by decide)
  -- (1)-(3) `MM := max mx sh`
  have h1 := BinW.copy_spec (A := S 22) (B := S 10) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ mm0 mx hmm0 hMX (hreg 2 (by decide) (by decide)) (hreg 3 (by decide) (by decide)) hpre.cap
  set σ1 := σ.sets (S 22) (frame (binary (W + 1) mx)) with hσ1
  have hsh : sh < 2 ^ (W + 1) := hb.shb
  have h2 := BinW.lt_spec (A := S 22) (B := S 23) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ1 mx sh (BinW.numOn_sets_self _ _ _ _ hmm0.2) (BinW.numOn_sets_ne hMS (hne (by decide)) _)
    (by simp [hσ1, hreg 2 (by decide) (by decide)]) (by simp [hσ1, hreg 3 (by decide) (by decide)]) hmx hsh hpre.cap
  have h3 : WXExec cap (.ifr (R 2) (.seq (WMX.dec (R 2)) (BinW.copy (S 22) (S 23) (R 2) (R 3))) WMX.skip)
      (σ1.setv (R 2) (decide (mx < sh)).toNat) (σ1.sets (S 22) (frame (binary (W + 1) (max mx sh)))) (41 * W + 50) := by
    by_cases hlt : mx < sh
    · have hv : (σ1.setv (R 2) (decide (mx < sh)).toNat).val (R 2) ≠ 0 := by simp [hlt]
      have hd := WXExec.dec cap (R 2) (σ1.setv (R 2) (decide (mx < sh)).toNat) (by simp [hlt]; have := hpre.cap; omega)
      have e : (σ1.setv (R 2) (decide (mx < sh)).toNat).setv (R 2)
          ((σ1.setv (R 2) (decide (mx < sh)).toNat).val (R 2) - 1) = σ1 := by
        apply WState.eq <;> try rfl
        funext r; by_cases hr : r = R 2
        · subst hr; simp [hlt, hσ1, hreg 2 (by decide) (by decide)]
        · simp [Function.update_of_ne hr]
      rw [e] at hd
      have hc := BinW.copy_spec (A := S 22) (B := S 23) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
        (hner (by decide)) σ1 mx sh (BinW.numOn_sets_self _ _ _ _ hmm0.2) (BinW.numOn_sets_ne hMS (hne (by decide)) _)
        (by simp [hσ1, hreg 2 (by decide) (by decide)]) (by simp [hσ1, hreg 3 (by decide) (by decide)]) hpre.cap
      refine (WXExec.ifrT hv (WXExec.seq hd hc)).cast cap ?_ (by omega)
      simp only [hσ1, BinW.sets_sets, max_eq_right hlt.le]
    · have hv : (σ1.setv (R 2) (decide (mx < sh)).toNat).val (R 2) = 0 := by simp [hlt]
      refine (WXExec.ifrF hv (WXExec.skip cap _)).cast cap ?_ (by omega)
      rw [max_eq_left (by omega)]
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = S 22
        · subst hi; simp [hσ1]
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = R 2
        · subst hr; simp [hlt, hσ1, hreg 2 (by decide) (by decide)]
        · simp [Function.update_of_ne hr]
  set σ3 := σ1.sets (S 22) (frame (binary (W + 1) (max mx sh))) with hσ3
  have hσ3fr : SameExcept σ σ3 [S 22] [] := ⟨fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [hσ3, hσ1, Function.update_of_ne hy], fun r _ => by simp [hσ3, hσ1], rfl⟩
  -- (4) `LR := L`
  obtain ⟨x0, hx0⟩ := hpre.words 6 (by decide)
  have h4 := sizeP_spec S R cap W σ3 (max mx sh) x0 (BinW.numOn_sets_self _ _ _ _ (by simp [hσ1, hmm0.2]))
    (hσ3fr.numOn (by simp [emb_eq_iff]) hx0) (hσ3fr.numOn (by simp [emb_eq_iff]) hpre.zr)
    (by rw [hσ3fr.val (by simp)]; exact hreg 2 (by decide) (by decide))
    (by rw [hσ3fr.val (by simp)]; exact hreg 3 (by decide) (by decide))
    (by rw [hσ3fr.val (by simp)]; exact hreg 9 (by decide) (by decide))
    (by rw [hσ3fr.val (by simp)]; exact hreg 18 (by decide) (by decide))
    (by rw [hσ3fr.val (by simp)]; exact hreg 19 (by decide) (by decide)) (max_lt hmx hsh) (by omega)
  set σ4 := (σ3.sets (S 6) (frame (binary (W + 1) 0))).setv (R 9) L with hσ4
  -- (5) the powers
  obtain ⟨p0, hp0⟩ := hpre.words 12 (by decide)
  obtain ⟨p1, hp1⟩ := hpre.words 13 (by decide)
  have hσ4fr : SameExcept σ σ4 [S 6, S 22] [R 9] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hσ4, hσ3, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hσ4, hσ3, hσ1, Function.update_of_ne hr]
  have h5 := powP_spec S R cap W σ4 L p0 p1 (hσ4fr.numOn (by simp [emb_eq_iff]) hp0)
    (hσ4fr.numOn (by simp [emb_eq_iff]) hp1) (hσ4fr.numOn (by simp [emb_eq_iff]) hpre.zr)
    (by rw [hσ4fr.val (by simp [emb_eq_iff])]; exact hreg 2 (by decide) (by decide))
    (by rw [hσ4fr.val (by simp [emb_eq_iff])]; exact hreg 3 (by decide) (by decide)) (by simp [hσ4])
    (by rw [hσ4fr.val (by simp [emb_eq_iff])]; exact hreg 19 (by decide) (by decide)) hL (by omega)
  set σ5 := (σ4.sets (S 12) (frame (binary (W + 1) (2 ^ L)))).sets (S 13) (frame (binary (W + 1) (2 ^ (L + 1))))
    with hσ5
  have hσ5fr : SameExcept σ σ5 [S 6, S 12, S 13, S 22] [R 9] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hσ5, hσ4, hσ3, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1,
        Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hσ5, hσ4, hσ3, hσ1, Function.update_of_ne hr]
  have hr5 : ∀ k : Fin 24, k ≠ 9 → k ≠ 13 → k ≠ 14 → σ5.val (R k) = 0 := fun k h9 h13 h14 => by
    rw [hσ5fr.val (by simp [emb_eq_iff, h9])]; exact hreg k h13 h14
  have hw5 : ∀ k : Fin 24, k ∈ [(4 : Fin 24), 5, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 23] →
      ∃ v, NumOn σ5 (S k) (W + 1) v := by
    intro k hk
    obtain ⟨v, hv⟩ := hpre.words k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)
    refine ⟨v, hσ5fr.numOn ?_ hv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [emb_eq_iff]
  have hpre5 : BodyPre S R cap W σ5 (2 ^ L) :=
    ⟨hw5 4 (by decide), ⟨0, by simp [hσ5, hσ4, emb_eq_iff], by simp [hσ5, hσ4, hσ3, hσ1, emb_eq_iff, hx0.2]⟩,
      hw5 16 (by decide), hw5 17 (by decide), hw5 18 (by decide),
      ⟨by simp [hσ5, emb_eq_iff], by simp [hσ5, hσ4, hσ3, hσ1, emb_eq_iff, hp0.2]⟩,
      by rw [show 2 * 2 ^ L = 2 ^ (L + 1) by ring]
         exact ⟨by simp [hσ5], by simp [hσ5, hσ4, hσ3, hσ1, emb_eq_iff, hp1.2]⟩,
      hσ5fr.numOn (by simp [emb_eq_iff]) hpre.zr, hr5 4 (by decide) (by decide) (by decide),
      hr5 2 (by decide) (by decide) (by decide), hr5 3 (by decide) (by decide) (by decide),
      hr5 16 (by decide) (by decide) (by decide), hr5 17 (by decide) (by decide) (by decide),
      hr5 15 (by decide) (by decide) (by decide), hpre.cap⟩
  have hcp5 : ChildPre S R cap W σ5 :=
    ⟨hw5 5 (by decide), hw5 7 (by decide), hw5 15 (by decide),
      by rw [hσ5fr.sh (by simp [emb_eq_iff])]; exact hpre.wkh,
      by rw [hσ5fr.st (by simp [emb_eq_iff])]; exact hpre.wkl,
      hr5 0 (by decide) (by decide) (by decide), hr5 1 (by decide) (by decide) (by decide),
      hr5 11 (by decide) (by decide) (by decide), hr5 12 (by decide) (by decide) (by decide),
      hr5 22 (by decide) (by decide) (by decide), hr5 5 (by decide) (by decide) (by decide)⟩
  have hKD5 : OutOn σ5 (S 2) (R 14) out L0 :=
    ⟨by rw [hσ5fr.st (by simp [emb_eq_iff])]; exact hKD.1, by rw [hσ5fr.sh (by simp [emb_eq_iff])]; exact hKD.2.1,
      by rw [hσ5fr.val (by simp [emb_eq_iff])]; exact hKD.2.2⟩
  have hl := levels_spec S R cap W σ5 ws junk sh L out L0 hn hpre5 hcp5
    (by rw [hσ5fr.st (by simp [emb_eq_iff]), hWS]) (by rw [hσ5fr.sh (by simp [emb_eq_iff]), hWSh])
    (hσ5fr.numOn (by simp [emb_eq_iff]) hMS) (hw5 19 (by decide)) (hw5 14 (by decide))
    (by rw [hσ5fr.val (by simp [emb_eq_iff])]; exact hNR) (hr5 10 (by decide) (by decide) (by decide))
    (hr5 19 (by decide) (by decide) (by decide)) (hr5 20 (by decide) (by decide) (by decide))
    (hr5 21 (by decide) (by decide) (by decide)) (hr5 6 (by decide) (by decide) (by decide))
    (by simp [hσ5, hσ4]) (hr5 8 (by decide) (by decide) (by decide)) hKD5 hb
  have h4' : WXExec cap (sizeP S R) σ3 σ4 ((W + 1) * (80 * W + 150) + 300 * W + 400) := h4
  refine (Runs.seqE h1 (Runs.seqE h2 (Runs.seqE h3 (Runs.seqE h4' (Runs.seqE h5 (Runs.seq (c2 := 3 * L + 1) hl fun τ hτ => ?_)))))).cost
    ?_
  · obtain ⟨⟨hKDτ, hpreτ, hcpτ, hCτ, hTLτ, hIXτ, hK4τ, hF2τ, hfrτ⟩, h9, h8⟩ := hτ
    have hall := hσ5fr.comp' hfrτ
    refine Runs.of (WXExec.wm (wclear_spec (cap := cap) (R 9) L τ h9 (by rw [h9]; omega))) ⟨?_, ?_, ?_, ?_⟩
    · rw [List.take_of_length_le (by simp)] at hKDτ
      exact ⟨by simpa using hKDτ.1, by simpa using hKDτ.2.1, by
        rw [WState.setv_val, Function.update_of_ne (hner (by decide))]; exact hKDτ.2.2⟩
    · have hregτ : ∀ k : Fin 24, k ≠ 13 → k ≠ 14 → (τ.setv (R 9) 0).val (R k) = 0 := by
        intro k h13 h14
        by_cases k9 : k = 9
        · subst k9; simp
        · rw [WState.setv_val, Function.update_of_ne (hner k9)]
          by_cases k8 : k = 8
          · subst k8; exact h8
          · rw [hall.val (by simp [emb_eq_iff, k8, k9, h14])]; exact hreg k h13 h14
      have hwτ : ∀ k : Fin 24, k ∈ [(8 : Fin 24), 9, 10, 11, 23] →
          ∃ v, NumOn (τ.setv (R 9) 0) (S k) (W + 1) v := by
        intro k hk
        obtain ⟨v, hv⟩ := hpre.words k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)
        refine ⟨v, BinW.numOn_setv (hall.numOn ?_ hv) _ _⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [emb_eq_iff]
      have h22 : NumOn σ5 (S 22) (W + 1) (max mx sh) :=
        ⟨by simp [hσ5, hσ4, hσ3, emb_eq_iff], by simp [hσ5, hσ4, hσ3, hσ1, emb_eq_iff, hmm0.2]⟩
      exact compPre_of S R (bodyPre_setv S R hpreτ 9 (by decide) 0) (childPre_setv S R hcpτ 9 (by decide) 0)
        (hCτ.elim fun x h => ⟨x, BinW.numOn_setv h _ _⟩) (hTLτ.elim fun x h => ⟨x, BinW.numOn_setv h _ _⟩)
        (hwτ 8 (by decide)) (hwτ 9 (by decide)) (hwτ 10 (by decide)) (hwτ 11 (by decide))
        ⟨max mx sh, BinW.numOn_setv (hfrτ.numOn (by simp [emb_eq_iff]) h22) _ _⟩
        (hwτ 23 (by decide)) (BinW.numOn_setv (hall.numOn (by simp [emb_eq_iff]) hpre.tw) _ _) hregτ
    · rw [WState.setv_val, Function.update_of_ne (hner (by decide)), hall.val (by simp [emb_eq_iff])]; exact hNR
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hall.cell]⟩
      · have hx' : x ∉ [S 6, S 12, S 13, S 22] ++ [S 2, S 3, S 4, S 5, S 6, S 7, S 12, S 13, S 14, S 15, S 16, S 17,
            S 18, S 19] := by
          intro hm; apply hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
          rcases hm with (h | h | h | h) | (h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h]
        simpa using hall.1 x hx'
      · by_cases r9 : r = R 9
        · subst r9; simp [hreg 9 (by decide) (by decide)]
        · rw [WState.setv_val, Function.update_of_ne r9]
          by_cases r8 : r = R 8
          · subst r8; rw [h8, hreg 8 (by decide) (by decide)]
          · refine hall.val ?_
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
            exact ⟨r9, r8, r9, hr⟩
  · simp only [mainCost]; omega

end Main

end NearCubicGates.Close.TabMachine
