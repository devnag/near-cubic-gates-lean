import Proof.Gates.TabMachine.CompileM3

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
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Level
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- The head of a level: the powers halved, the target literal, `IX := n − 1`. -/
def lvlHead : WMX ns nr :=
  .seq (BinW.copy (S 13) (S 12) (R 2) (R 3))
  (.seq (BinW.half (S 12) (R 3))
  (.seq (BinW.divmod (S 23) (S 12) (S 16) (S 17) (S 18) (R 2) (R 3) (R 16) (R 17))
  (.seq (BinW.inc (S 16) (S 20) (R 2) (R 3))
  (.seq (BinW.mul (S 12) (S 16) (S 19) (S 18) (R 2) (R 3) (R 6))
  (.seq (BinW.copy (S 14) (S 19) (R 2) (R 3))
  (.seq (BinW.shl (S 14) (S 20) (R 2) (R 3))
  (.seq (BinW.inc (S 14) (S 20) (R 2) (R 3))
  (.seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup (R 13) (R 10) (R 22)))
  (.seq (.wm (WM.move (R 22) (R 13)))
  (.ifr (R 10) (WMX.dec (R 10)) WMX.skip))))))))))

/-- The head's cost bound. -/
def headCost (W n : ℕ) : ℕ := 6 * (41 * (W + 1) + 8) + 34 * (W + 1) + 3 + BinW.divCost (W + 1) + mulCost (W + 1) +
  18 * n + 40

theorem lvlHead_spec (cap W : ℕ) (σ : WState ns nr) (sh bit n : ℕ) (hpre : BodyPre S R cap W σ (2 ^ (bit + 1)))
    (hMS : NumOn σ (S 23) (W + 1) sh) (hC : ∃ v, NumOn σ (S 19) (W + 1) v) (hTL : ∃ v, NumOn σ (S 14) (W + 1) v)
    (hNR : σ.val (R 13) = n) (hIX : σ.val (R 10) = 0) (hTMP : σ.val (R 22) = 0) (hG : σ.val (R 6) = 0)
    (hshb : sh < 2 ^ (W + 1)) (htlb : 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1 < 2 ^ (W + 1))
    (hbit : 2 ^ (bit + 3) ≤ 2 ^ (W + 1)) (hcapn : 2 * n + 2 ≤ cap) :
    Runs cap (lvlHead S R) σ (headCost W n) (fun τ =>
      BodyPre S R cap W τ (2 ^ bit) ∧ NumOn τ (S 14) (W + 1) (2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1) ∧
      (∃ v, NumOn τ (S 19) (W + 1) v) ∧ τ.val (R 10) = n - 1 ∧
      SameExcept σ τ [S 12, S 13, S 14, S 16, S 17, S 18, S 19] [R 10]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have hp1 : 2 ^ (bit + 1) = 2 * 2 ^ bit := by ring
  have hp2 : 2 ^ (bit + 2) = 2 * 2 ^ (bit + 1) := by ring
  have hp3 : 2 ^ (bit + 3) = 2 * 2 ^ (bit + 2) := by ring
  have hpos : 0 < 2 ^ bit := Nat.pow_pos (by norm_num)

  have h1 := BinW.copy_spec (A := S 13) (B := S 12) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ _ _ hpre.hpw2 hpre.hpw hpre.f hpre.r hpre.cap
  set σ1 := σ.sets (S 13) (frame (binary (W + 1) (2 ^ (bit + 1)))) with hσ1
  have h2 := BinW.half_spec (A := S 12) (R := R 3) cap (W + 1) σ1 (2 ^ (bit + 1))
    (BinW.numOn_sets_ne hpre.hpw (hne (by decide)) _) (by simp [hσ1, hpre.r]) (by omega) (by have := hpre.cap; omega)
  have hhalf : 2 ^ (bit + 1) / 2 = 2 ^ bit := by rw [hp1]; omega
  rw [hhalf] at h2
  set σ2 := σ1.sets (S 12) (frame (binary (W + 1) (2 ^ bit))) with hσ2
  -- (3) `Q := sh / 2^bit`
  obtain ⟨q0, hq0⟩ := hpre.q
  obtain ⟨r0, hr0⟩ := hpre.rm
  obtain ⟨d0, hd0⟩ := hpre.dx
  have hl2 : ∀ (k : Fin 24) (v : ℕ), k ≠ 12 → k ≠ 13 → NumOn σ (S k) (W + 1) v → NumOn σ2 (S k) (W + 1) v :=
    fun k v h12 h13 h => BinW.numOn_sets_ne (BinW.numOn_sets_ne h (hne h13) _) (hne h12) _
  have hPW2 : NumOn σ2 (S 12) (W + 1) (2 ^ bit) := BinW.numOn_sets_self _ _ _ _ (by simp [hσ1, hpre.hpw.2])
  have h3 := BinW.divmod_spec (A := S 23) (B := S 12) (Q := S 16) (M := S 17) (X := S 18) (F := R 2) (R := R 3)
    (K := R 16) (T := R 17) cap (W + 1) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hner (by decide))
    (hner (by decide)) (hner (by decide)) (hner (by decide)) σ2 sh (2 ^ bit) q0 r0 d0
    (hl2 _ _ (by decide) (by decide) hMS) hPW2 (hl2 _ _ (by decide) (by decide) hq0)
    (hl2 _ _ (by decide) (by decide) hr0) (hl2 _ _ (by decide) (by decide) hd0) (by simp [hσ2, hσ1, hpre.f])
    (by simp [hσ2, hσ1, hpre.r]) (by simp [hσ2, hσ1, hpre.dk]) (by simp [hσ2, hσ1, hpre.dt]) hshb hpos
    (by rw [hp3, hp2, hp1] at hbit; omega) (by have := hpre.cap; omega)
  set σ3 := ((σ2.sets (S 16) (frame (binary (W + 1) (sh / 2 ^ bit)))).sets (S 17)
    (frame (binary (W + 1) (sh % 2 ^ bit)))).sets (S 18) (frame (binary (W + 1) 0)) with hσ3
  set q := sh / 2 ^ bit with hq
  have hqle : q ≤ sh := Nat.div_le_self _ _
  have hprod : 2 ^ bit * (q + 1) < 2 ^ W := by
    have : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
    nlinarith
  have hW1 : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTLv : 2 * (2 ^ bit * (q + 1)) + 1 = 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1 := by rw [hq]; ring
  have hl3 : ∀ (k : Fin 24) (v : ℕ), k ≠ 12 → k ≠ 13 → k ≠ 16 → k ≠ 17 → k ≠ 18 → NumOn σ (S k) (W + 1) v →
      NumOn σ3 (S k) (W + 1) v := fun k v h12 h13 h16 h17 h18 h =>
    BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (hl2 k v h12 h13 h) (hne h16) _) (hne h17) _) (hne h18) _
  have hZR3 : NumOn σ3 (S 20) (W + 1) 0 := hl3 _ _ (by decide) (by decide) (by decide) (by decide) (by decide) hpre.zr
  have hR3 : ∀ k : Fin 24, σ3.val (R k) = σ.val (R k) := fun k => by simp [hσ3, hσ2, hσ1]
  -- (4) `Q := q + 1`
  have h4 := BinW.inc_spec (A := S 16) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ3 q 0 (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _
      (by simp [hσ2, hσ1, hq0.2])) (hne (by decide)) _) (hne (by decide)) _) hZR3 (by rw [hR3]; exact hpre.f)
    (by rw [hR3]; exact hpre.r) (by nlinarith [hW1]) (by have := hpre.cap; omega)
  set σ4 := σ3.sets (S 16) (frame (binary (W + 1) (q + 1))) with hσ4
  -- (5) `C := 2^bit · (q + 1)`
  obtain ⟨c0, hc0⟩ := hC
  have h5 := BinW.mul_spec (A := S 12) (B := S 16) (C := S 19) (S := S 18) (F := R 2) (R := R 3) (G := R 6) cap
    (W + 1) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hner (by decide)) (hner (by decide)) (hner (by decide)) σ4 (2 ^ bit) (q + 1) c0 0
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hPW2 (hne (by decide)) _)
      (hne (by decide)) _) (hne (by decide)) _) (hne (by decide)) _)
    (BinW.numOn_sets_self _ _ _ _ (by simp [hσ3, hσ2, hσ1, hq0.2]))
    (BinW.numOn_sets_ne (hl3 _ _ (by decide) (by decide) (by decide) (by decide) (by decide) hc0) (hne (by decide)) _)
    (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by simp [hσ2, hσ1, hd0.2])) (hne (by decide)) _)
    (by simp [hσ4, hR3, hpre.f]) (by simp [hσ4, hR3, hpre.r]) (by simp [hσ4, hR3, hG])
    (by omega) (by nlinarith [hW1]) (by have := hpre.cap; omega)
  set σ5 := (σ4.sets (S 19) (frame (binary (W + 1) (2 ^ bit * (q + 1))))).sets (S 18) (frame (binary (W + 1) 0))
    with hσ5
  have hR5 : ∀ k : Fin 24, σ5.val (R k) = σ.val (R k) := fun k => by simp [hσ5, hσ4, hR3]
  have hZR5 : NumOn σ5 (S 20) (W + 1) 0 :=
    BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hZR3 (hne (by decide)) _) (hne (by decide)) _)
      (hne (by decide)) _
  -- (6)-(8) `TL := 2·C + 1`
  obtain ⟨t0, ht0⟩ := hTL
  have hTL5 : NumOn σ5 (S 14) (W + 1) t0 :=
    BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (hl3 _ _ (by decide) (by decide) (by decide) (by decide) (by decide) ht0) (hne (by decide)) _) (hne (by decide)) _)
      (hne (by decide)) _
  have h6 := BinW.copy_spec (A := S 14) (B := S 19) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ5 t0 _ hTL5 (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by simp [hσ4, hσ3, hσ2, hσ1,
      hc0.2])) (hne (by decide)) _) (by rw [hR5]; exact hpre.f) (by rw [hR5]; exact hpre.r) (by have := hpre.cap; omega)
  set σ6 := σ5.sets (S 14) (frame (binary (W + 1) (2 ^ bit * (q + 1)))) with hσ6
  have h7 := BinW.shl_spec (A := S 14) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ6 _ 0 (BinW.numOn_sets_self _ _ _ _ (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, ht0.2]))
    (BinW.numOn_sets_ne hZR5 (hne (by decide)) _) (by simp [hσ6, hR5, hpre.f]) (by simp [hσ6, hR5, hpre.r])
    (by have := hpre.cap; omega)
  set σ7 := σ6.sets (S 14) (frame (binary (W + 1) (2 * (2 ^ bit * (q + 1))))) with hσ7
  have h8 := BinW.inc_spec (A := S 14) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ7 _ 0 (BinW.numOn_sets_self _ _ _ _ (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, ht0.2]))
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne hZR5 (hne (by decide)) _) (hne (by decide)) _)
    (by simp [hσ7, hσ6, hR5, hpre.f]) (by simp [hσ7, hσ6, hR5, hpre.r])
    (by omega) (by have := hpre.cap; omega)
  set σ8 := σ7.sets (S 14) (frame (binary (W + 1) (2 * (2 ^ bit * (q + 1)) + 1))) with hσ8
  have hR8 : ∀ k : Fin 24, σ8.val (R k) = σ.val (R k) := fun k => by simp [hσ8, hσ7, hσ6, hR5]
  -- (9)-(11) `IX := n − 1`
  have h9 := WXExec.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup_spec (cap := cap) (R 13) (R 10) (R 22)
    (hner (by decide)) (hner (by decide)) (hner (by decide)) n σ8 (by rw [hR8]; exact hNR) (by omega)
    (by rw [hR8, hIX]; omega) (by rw [hR8, hTMP]; omega))
  set σ9 := ((σ8.setv (R 13) 0).setv (R 10) (σ8.val (R 10) + n)).setv (R 22) (σ8.val (R 22) + n) with hσ9
  have h10 := WXExec.wm (wmove_spec (cap := cap) (R 22) (R 13) (hner (by decide)) n σ9
    (by simp [hσ9, hR8, hTMP]) (by simp [hσ9, hR8, hTMP]; omega)
    (by simp [hσ9, hR8, hTMP, Function.update_apply, emb_eq_iff]; omega))
  set σ10 := (σ9.setv (R 22) 0).setv (R 13) (σ9.val (R 13) + σ9.val (R 22)) with hσ10
  have hIX10 : σ10.val (R 10) = n := by simp [hσ10, hσ9, emb_eq_iff, hR8, hIX]
  have h11 := decIf_spec cap (R 10) σ10 n hIX10 (by omega)
  refine ⟨_, WXExec.mono (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 (WXExec.seq h6
    (WXExec.seq h7 (WXExec.seq h8 (WXExec.seq h9 (WXExec.seq h10 h11)))))))))) (by unfold headCost; omega), ?_⟩
  set σ11 := σ10.setv (R 10) (n - 1) with hσ11
  have hsh : ∀ y, σ11.sh y = σ.sh y := fun y => by
    simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
  have hst : ∀ k : Fin 24, k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 16 → k ≠ 17 → k ≠ 18 → k ≠ 19 →
      σ11.st (S k) = σ.st (S k) := fun k h12 h13 h14 h16 h17 h18 h19 => by
    simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, h12, h13, h14, h16, h17, h18, h19]
  have hval : ∀ r, r ≠ R 10 → σ11.val r = σ.val r := by
    intro r hr
    by_cases r13 : r = R 13
    · rw [r13]; simp [hσ11, hσ10, hσ9, emb_eq_iff, hR8, hTMP, hNR]
    · by_cases r22 : r = R 22
      · rw [r22]; simp [hσ11, hσ10, hσ9, emb_eq_iff, hTMP]
      · simp [hσ11, hσ10, hσ9, Function.update_of_ne hr, Function.update_of_ne r13, Function.update_of_ne r22,
          hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
  have hnum : ∀ (k : Fin 24) (v : ℕ), σ11.st (S k) = frame (binary (W + 1) v) → σ.sh (S k) = 0 →
      NumOn σ11 (S k) (W + 1) v := fun k v h1 h2 => ⟨h1, by rw [hsh, h2]⟩
  refine ⟨⟨hpre.m.elim fun v h => ⟨v, ⟨by rw [hst 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h.1], by rw [hsh, h.2]⟩⟩,
    hpre.x.elim fun v h => ⟨v, ⟨by rw [hst 6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h.1], by rw [hsh, h.2]⟩⟩,
    ⟨q + 1, hnum 16 _ (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, emb_eq_iff]) hq0.2⟩,
    ⟨sh % 2 ^ bit, hnum 17 _ (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, emb_eq_iff]) hr0.2⟩,
    ⟨0, hnum 18 _ (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5]) hd0.2⟩,
    hnum 12 _ (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, emb_eq_iff]) hpre.hpw.2,
    hnum 13 _ (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hp1]) hpre.hpw2.2,
    ⟨by rw [hst 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.zr.1],
      by rw [hsh, hpre.zr.2]⟩,
    by rw [hval _ (hner (by decide))]; exact hpre.sg, by rw [hval _ (hner (by decide))]; exact hpre.f,
    by rw [hval _ (hner (by decide))]; exact hpre.r, by rw [hval _ (hner (by decide))]; exact hpre.dk,
    by rw [hval _ (hner (by decide))]; exact hpre.dt, by rw [hval _ (hner (by decide))]; exact hpre.cs, hpre.cap⟩,
    hnum 14 _ (by simp [hσ11, hσ10, hσ9, hσ8, emb_eq_iff]; ring_nf) ht0.2,
    ⟨2 ^ bit * (q + 1), hnum 19 _ (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, emb_eq_iff]) hc0.2⟩, by simp [hσ11],
    ?_⟩
  refine ⟨fun y hy => ⟨?_, hsh y⟩, fun r hr => hval r (by simpa using hr), by simp [hσ11, hσ10, hσ9, hσ8, hσ7,
    hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1,
    Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2.1,
    Function.update_of_ne hy.2.2.2.2.2.1, Function.update_of_ne hy.2.2.2.2.2.2]

/-- One level: the head, then the `n` visits. -/
def lvl : WMX ns nr := .seq (lvlHead S R) (repK (R 13) (R 19) (iStep S R))

/-- The records of a level, in the compiler's order (`i = n−1, …, 0`). -/
def lvlRecs (W : ℕ) (ws : List ℤ) (sh bit : ℕ) : List Bool :=
  ((List.range ws.length).reverse).flatMap (visitRec W ws sh bit)

theorem range_reverse_getElem (n k : ℕ) (hk : k < n) :
    ((List.range n).reverse)[k]'(by simpa using hk) = n - 1 - k := by
  rw [List.getElem_reverse]; simp

theorem take_succ_reverse (n k : ℕ) (hk : k < n) :
    ((List.range n).reverse).take (k + 1) = ((List.range n).reverse).take k ++ [n - 1 - k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk), range_reverse_getElem n k hk]; rfl

/-- The cost bound of a level. -/
def lvlCost (W n : ℕ) : ℕ := headCost W n + 1 + (n * (visitCost W n n + 8) + 7 * n + 3)

end Level

end NearCubicGates.Close.TabMachine
