import Proof.Gates.TabMachine.CompileM

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

section Child
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- What the child emission keeps besides `BodyPre`: two more scratch words, the zero counters. -/
structure ChildPre (cap W : ℕ) (σ : WState ns nr) : Prop where
  n : ∃ v, NumOn σ (S 5) (W + 1) v
  y : ∃ v, NumOn σ (S 7) (W + 1) v
  no : ∃ v, NumOn σ (S 15) (W + 1) v
  wkh : σ.sh (S 3) = 0
  wkl : (σ.st (S 3)).length ≤ 2 * (W + 1) + 1
  ci : σ.val (R 0) = 0
  cw : σ.val (R 1) = 0
  dj : σ.val (R 11) = 0
  pass : σ.val (R 12) = 0
  tmp : σ.val (R 22) = 0
  tg : σ.val (R 5) = 0

theorem emitChild_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (sh bit i tl : ℕ)
    (out L0 : List Bool) (hi : i < ws.length) (hpre : BodyPre S R cap W σ (2 ^ bit)) (hcp : ChildPre S R cap W σ)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hTL : NumOn σ (S 14) (W + 1) tl) (htl : tl = 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1) (htlb : tl < 2 ^ W)
    (hIX : σ.val (R 10) = i) (hKD : OutOn σ (S 2) (R 14) out L0)
    (hw : ∀ z ∈ ws, 2 * z.natAbs + 2 ≤ 2 ^ W) (hbit : 2 ^ (bit + 2) ≤ 2 ^ (W + 1))
    (hsum : (ws.map fun z => 2 * z.natAbs + 1).sum < 2 ^ W)
    (hcapO : out.length + (ws.length + 1) * (2 * (W + 1) + 1) + 1 ≤ cap) (hcapI : 2 * i + 2 ≤ cap) :
    Runs cap (emitChild S R) σ (childCost W ws.length i) (fun τ =>
      OutOn τ (S 2) (R 14) (out ++ frame (recBits W (childL ws sh bit i))) L0 ∧ BodyPre S R cap W τ (2 ^ bit) ∧
      ChildPre S R cap W τ ∧ τ.val (R 10) = i ∧
      SameExcept σ τ [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] [R 14]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have hi' : i < ws.length := hi
  set n := ws.length with hn
  -- (1) `NO := 0`
  obtain ⟨no0, hno0⟩ := hcp.no
  have h1 := BinW.zero_spec (A := S 15) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ no0 0 hno0 hpre.zr hpre.f hpre.r hpre.cap
  set σ1 := σ.sets (S 15) (frame (binary (W + 1) 0)) with hσ1
  -- (2) `DJ := i`, `TMP := i`, `IX := 0`; (3) `IX := i`, `TMP := 0`
  have h2 := WXExec.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup_spec (cap := cap) (R 10) (R 11) (R 22)
    (hner (by decide)) (hner (by decide)) (hner (by decide)) i σ1 (by simp [hσ1, hIX]) (by omega)
    (by simp [hσ1, hcp.dj]; omega) (by simp [hσ1, hcp.tmp]; omega))
  set σ2 := ((σ1.setv (R 10) 0).setv (R 11) (σ1.val (R 11) + i)).setv (R 22) (σ1.val (R 22) + i) with hσ2
  have h3 := WXExec.wm (wmove_spec (cap := cap) (R 22) (R 10) (hner (by decide)) i σ2
    (by simp [hσ2, hσ1, hcp.tmp]) (by simp [hσ2, hσ1, hcp.tmp]; omega)
    (by simp [hσ2, hσ1, hcp.tmp, Function.update_apply, emb_eq_iff]; omega))
  set σ3 := (σ2.setv (R 22) 0).setv (R 10) (σ2.val (R 10) + σ2.val (R 22)) with hσ3
  have hσ3f : SameExcept σ σ3 [S 15] [R 11] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      simp [hσ3, hσ2, hσ1, Function.update_of_ne hy]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      by_cases h10 : r = R 10
      · rw [h10]; simp [hσ3, hσ2, hσ1, emb_eq_iff, hIX, hcp.tmp]
      · by_cases h22 : r = R 22
        · rw [h22]; simp [hσ3, hσ2, hσ1, emb_eq_iff, hcp.tmp]
        · simp [hσ3, hσ2, hσ1, Function.update_of_ne h10, Function.update_of_ne h22, Function.update_of_ne hr]
  have hσ3dj : σ3.val (R 11) = i := by simp [hσ3, hσ2, hσ1, emb_eq_iff, hcp.dj]
  have hσ3no : NumOn σ3 (S 15) (W + 1) 0 := ⟨by simp [hσ3, hσ2, hσ1], by simp [hσ3, hσ2, hσ1, hno0.2]⟩
  -- (4) the scan
  have hpre3 : BodyPre S R cap W σ3 (2 ^ bit) := by
    obtain ⟨⟨m, hm⟩, ⟨x, hx⟩, ⟨q, hq⟩, ⟨rm, hrm⟩, ⟨dx, hdx⟩, hpw, hpw2, hzr, hsg, hf, hr, hdk, hdt, hcs, hcap⟩ := hpre
    have f := hσ3f
    exact ⟨⟨m, f.numOn (by simp [emb_eq_iff]) hm⟩, ⟨x, f.numOn (by simp [emb_eq_iff]) hx⟩,
      ⟨q, f.numOn (by simp [emb_eq_iff]) hq⟩, ⟨rm, f.numOn (by simp [emb_eq_iff]) hrm⟩,
      ⟨dx, f.numOn (by simp [emb_eq_iff]) hdx⟩, f.numOn (by simp [emb_eq_iff]) hpw, f.numOn (by simp [emb_eq_iff]) hpw2,
      f.numOn (by simp [emb_eq_iff]) hzr, by rw [f.val (by simp [emb_eq_iff])]; exact hsg,
      by rw [f.val (by simp [emb_eq_iff])]; exact hf, by rw [f.val (by simp [emb_eq_iff])]; exact hr,
      by rw [f.val (by simp [emb_eq_iff])]; exact hdk, by rw [f.val (by simp [emb_eq_iff])]; exact hdt,
      by rw [f.val (by simp [emb_eq_iff])]; exact hcs, hcap⟩
  have h0 : ChildInv S R cap W σ3 ws bit i out L0 0 σ3 :=
    ⟨by simpa [prefixFields] using ⟨by rw [hσ3f.st (by simp [emb_eq_iff]), hKD.1],
        by rw [hσ3f.sh (by simp [emb_eq_iff]), hKD.2.1], by rw [hσ3f.val (by simp [emb_eq_iff]), hKD.2.2]⟩,
      by simpa [negSum] using hσ3no, by rw [hσ3dj]; rfl,
      by rw [hσ3f.val (by simp [emb_eq_iff]), hcp.pass]; simp, hpre3,
      by rw [hσ3f.sh (by simp [emb_eq_iff]), hcp.wkh], by rw [hσ3f.st (by simp [emb_eq_iff])]; exact hcp.wkl,
      SameExcept.refl _ _ _⟩
  have hwl : ∀ w ∈ ws.map (fun z => binary (W + 1) (encS z)), w.length = W + 1 := by
    intro w hw'; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hw'; simp
  obtain ⟨τ, hInv, hτI, hτCW, hloop⟩ := recLoopJ_spec (cap := cap) (L := W + 1) (I := S 0) (Wk := S 3) (CI := R 0)
    (CW := R 1) (body := cBody S R) (hne (by decide)) (hner (by decide)) hwl (by omega)
    (by simp only [List.length_map]; nlinarith)
    (childScan_body S R cap W σ3 ws junk bit i out L0 hw hbit hsum (by nlinarith) (by omega)) σ3 h0
    (by rw [hσ3f.st (by simp [emb_eq_iff]), hWS]) (by rw [hσ3f.sh (by simp [emb_eq_iff]), hWSh])
    (by rw [hσ3f.val (by simp [emb_eq_iff]), hcp.ci]) (by rw [hσ3f.val (by simp [emb_eq_iff]), hcp.cw])
    (by rw [hσ3f.sh (by simp [emb_eq_iff]), hcp.wkh]) (by rw [hσ3f.st (by simp [emb_eq_iff])]; exact hcp.wkl)
  simp only [List.length_map] at hInv hloop
  obtain ⟨hKD4, hNO4, hDJ4, hPASS4, hpre4, hWkh4, hWkl4, hfr4⟩ := hInv
  set σ4 := (τ.setv (R 0) 0).seth (S 0) 0 with hσ4
  -- facts on `σ4`
  have hσ4f : SameExcept σ σ4 [S 0, S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] [R 0, R 1, R 11, R 12, R 14] := by
    have h1 : SameExcept τ σ4 [S 0] [R 0] := ⟨fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [hσ4, Function.update_of_ne hy],
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp [hσ4, Function.update_of_ne hr],
      rfl⟩
    exact ((hσ3f.weaken (by simp) (by simp)).trans hfr4).trans (h1.weaken (by simp) (by simp))
  have hσ4v : ∀ k : Fin 24, k ≠ 0 → k ≠ 1 → k ≠ 11 → k ≠ 12 → k ≠ 14 → σ4.val (R k) = σ.val (R k) := by
    intro k h0 h1 h11 h12 h14; exact hσ4f.val (by simp [emb_eq_iff, h0, h1, h11, h12, h14])
  have hKD4' : OutOn σ4 (S 2) (R 14) (out ++ prefixFields W ws bit i n) L0 :=
    ⟨by simp [hσ4, hKD4.1, hn], by simp [hσ4, emb_eq_iff, hKD4.2.1, hn], by simp [hσ4, emb_eq_iff, hKD4.2.2, hn]⟩
  have hNO4' : NumOn σ4 (S 15) (W + 1) (negSum ws bit i n) :=
    ⟨by simp [hσ4, hNO4.1, hn], by simp [hσ4, emb_eq_iff, hNO4.2]⟩
  have hpre4' : BodyPre S R cap W σ4 (2 ^ bit) := by
    have f : SameExcept τ σ4 [S 0] [R 0] := ⟨fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [hσ4, Function.update_of_ne hy],
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp [hσ4, Function.update_of_ne hr],
      rfl⟩
    obtain ⟨⟨m, hm⟩, ⟨x, hx⟩, ⟨q, hq⟩, ⟨rm, hrm⟩, ⟨dx, hdx⟩, hpw, hpw2, hzr, hsg, hf, hr, hdk, hdt, hcs, hcap⟩ := hpre4
    exact ⟨⟨m, f.numOn (by simp [emb_eq_iff]) hm⟩, ⟨x, f.numOn (by simp [emb_eq_iff]) hx⟩,
      ⟨q, f.numOn (by simp [emb_eq_iff]) hq⟩, ⟨rm, f.numOn (by simp [emb_eq_iff]) hrm⟩,
      ⟨dx, f.numOn (by simp [emb_eq_iff]) hdx⟩, f.numOn (by simp [emb_eq_iff]) hpw, f.numOn (by simp [emb_eq_iff]) hpw2,
      f.numOn (by simp [emb_eq_iff]) hzr, by rw [f.val (by simp [emb_eq_iff])]; exact hsg,
      by rw [f.val (by simp [emb_eq_iff])]; exact hf, by rw [f.val (by simp [emb_eq_iff])]; exact hr,
      by rw [f.val (by simp [emb_eq_iff])]; exact hdk, by rw [f.val (by simp [emb_eq_iff])]; exact hdt,
      by rw [f.val (by simp [emb_eq_iff])]; exact hcs, hcap⟩
  set nsum := negSum ws bit i n with hnsum
  have hnsb : nsum < 2 ^ W := by
    have := negSum_le ws bit i n
    have := sumRange_le ws n le_rfl
    omega
  -- (5) `X := 2·tl`, `Y := 2·nsum`
  obtain ⟨x0, hx0⟩ := hpre4'.x
  have hTL4 : NumOn σ4 (S 14) (W + 1) tl := hσ4f.numOn (by simp [emb_eq_iff]) hTL
  have t1 := BinW.copy_spec (A := S 6) (B := S 14) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ4 x0 tl hx0 hTL4 hpre4'.f hpre4'.r hpre4'.cap
  set σ5 := σ4.sets (S 6) (frame (binary (W + 1) tl)) with hσ5
  have t2 := BinW.shl_spec (A := S 6) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ5 tl 0 (BinW.numOn_sets_self _ _ _ _ hx0.2) (BinW.numOn_sets_ne hpre4'.zr (hne (by decide)) _)
    (by simp [hσ5, hpre4'.f]) (by simp [hσ5, hpre4'.r]) hpre4'.cap
  set σ6 := σ5.sets (S 6) (frame (binary (W + 1) (2 * tl))) with hσ6
  obtain ⟨y0, hy0⟩ := hcp.y
  have hy4 : NumOn σ4 (S 7) (W + 1) y0 := hσ4f.numOn (by simp [emb_eq_iff]) hy0
  have t3 := BinW.copy_spec (A := S 7) (B := S 15) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ6 y0 nsum (BinW.numOn_sets_ne (BinW.numOn_sets_ne hy4 (hne (by decide)) _) (hne (by decide)) _)
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne hNO4' (hne (by decide)) _) (hne (by decide)) _)
    (by simp [hσ6, hσ5, hpre4'.f]) (by simp [hσ6, hσ5, hpre4'.r]) hpre4'.cap
  set σ7 := σ6.sets (S 7) (frame (binary (W + 1) nsum)) with hσ7
  have t4 := BinW.shl_spec (A := S 7) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ7 nsum 0 (BinW.numOn_sets_self _ _ _ _ (by simp [hσ6, hσ5, hy4.2]))
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hpre4'.zr (hne (by decide)) _) (hne (by decide)) _)
      (hne (by decide)) _)
    (by simp [hσ7, hσ6, hσ5, hpre4'.f]) (by simp [hσ7, hσ6, hσ5, hpre4'.r]) hpre4'.cap
  set σ8 := σ7.sets (S 7) (frame (binary (W + 1) (2 * nsum))) with hσ8
  -- (6) `X := tl − nsum`
  obtain ⟨m0, hm0⟩ := hpre4'.m
  obtain ⟨n0, hn0⟩ := hcp.n
  have hn4 : NumOn σ4 (S 5) (W + 1) n0 := hσ4f.numOn (by simp [emb_eq_iff]) hn0
  have hX8 : SNumOn σ8 (S 6) W (tl : ℤ) := ⟨⟨by simp [hσ8, hσ7, hσ6, emb_eq_iff, encS_natCast],
    by simp [hσ8, hσ7, hσ6, hσ5, hx0.2]⟩, by simpa using htlb⟩
  have hY8 : SNumOn σ8 (S 7) W (nsum : ℤ) := ⟨⟨by simp [hσ8, encS_natCast], by simp [hσ8, hσ7, hσ6, hσ5, hy4.2]⟩,
    by simpa using hnsb⟩
  have hR8 : ∀ k : Fin 24, σ8.val (R k) = σ4.val (R k) := fun k => by simp [hσ8, hσ7, hσ6, hσ5]
  have hTg8 : σ8.val (R 5) = 0 := by
    rw [hR8, hσ4v 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcp.tg
  have t5 := SInt.ssub_spec (X := S 6) (Y := S 7) (M := S 4) (N := S 5) (S := R 4) (T := R 5) (F := R 2) (R := R 3)
    cap W (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) σ8 (tl : ℤ) (nsum : ℤ) m0 n0 hX8 hY8
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hm0 (hne (by decide)) _)
      (hne (by decide)) _) (hne (by decide)) _) (hne (by decide)) _)
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hn4 (hne (by decide)) _)
      (hne (by decide)) _) (hne (by decide)) _) (hne (by decide)) _)
    (by rw [hR8]; exact hpre4'.sg) hTg8 (by rw [hR8]; exact hpre4'.f) (by rw [hR8]; exact hpre4'.r) (by omega)
    hpre4'.cap
  obtain ⟨τ5, e5, hX5, ⟨m5, hm5⟩, ⟨n5, hn5⟩, hfr5⟩ := t5
  have h85 : ∀ k : Fin 24, k ≠ 4 → k ≠ 5 → k ≠ 6 → τ5.st (S k) = σ8.st (S k) ∧ τ5.sh (S k) = σ8.sh (S k) :=
    fun k h4 h5 h6 => hfr5.1 _ (by simp [emb_eq_iff, h4, h5, h6])
  have hKD5 : OutOn τ5 (S 2) (R 14) (out ++ prefixFields W ws bit i n) L0 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [(h85 2 (by decide) (by decide) (by decide)).1]; simp [hσ8, hσ7, hσ6, hσ5, emb_eq_iff, hKD4'.1]
    · rw [(h85 2 (by decide) (by decide) (by decide)).2]; simp [hσ8, hσ7, hσ6, hσ5, hKD4'.2.1]
    · rw [hfr5.val (by simp), hR8]; exact hKD4'.2.2
  -- (7) the target field, the end marker, `PASS := 0`
  set tz : ℤ := (tl : ℤ) - (nsum : ℤ) with htz
  have t6 := fieldO_spec cap (hne (show (6 : Fin 24) ≠ 2 by decide)) (hner (show (15 : Fin 24) ≠ 14 by decide)) τ5
    (binary (W + 1) (encS tz)) [] (out ++ prefixFields W ws bit i n) L0 (by rw [hX5.1.1, BinW.frame_frameP])
    hX5.1.2 (by rw [hfr5.val (by simp), hR8]; exact hpre4'.cs) hKD5
    (by rw [List.length_append, prefixFields_length, binary_length]; nlinarith)
  set σ9 := outSt τ5 (S 2) (R 14) (out ++ prefixFields W ws bit i n ++ frameP (binary (W + 1) (encS tz))) L0
    with hσ9
  have t7 := emitO_spec cap σ9 (out ++ prefixFields W ws bit i n ++ frameP (binary (W + 1) (encS tz))) L0 false
    (outOn_outSt _ _ _ _ _)
    (by rw [List.length_append, List.length_append, prefixFields_length, frameP_len, binary_length]; nlinarith)
  rw [hσ9, outSt_outSt] at t7
  set σ10 := outSt τ5 (S 2) (R 14) (out ++ prefixFields W ws bit i n ++ frameP (binary (W + 1) (encS tz)) ++ [false])
    L0 with hσ10
  have hPASS10 : σ10.val (R 12) = 1 := by
    simp [hσ10, outSt, emb_eq_iff]; rw [hfr5.val (by simp), hR8]; simp [hσ4, emb_eq_iff, hPASS4]; exact hi
  have t8 := WXExec.wm (wclear_spec (cap := cap) (R 12) 1 σ10 hPASS10 (by rw [hPASS10]; omega))
  -- the composition
  have hloopc : n * (bodyCost W + (50 * (W + 1) + 30)) + 3 + 1 + (41 * (W + 1) + 3) + 1 + (41 * (W + 1) + 8) + 1 +
      (41 * (W + 1) + 3) + 1 + (41 * (W + 1) + 8) + 1 + (420 * W + 610) + 1 + (40 * (W + 1) + 3) + 1 + 7 + 1 +
      (3 * 1 + 1) + (41 * (W + 1) + 3) + 1 + (11 * i + 1) + 1 + (7 * i + 1) + 1 ≤ childCost W n i := by
    unfold childCost; nlinarith
  simp only [binary_length] at t6
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  rw [← hn] at hloop
  refine ⟨_, WXExec.mono (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq (WXExec.mono hloop le_rfl)
    (WXExec.seq t1 (WXExec.seq t2 (WXExec.seq t3 (WXExec.seq t4 (WXExec.seq e5 (WXExec.seq t6 (WXExec.seq t7
      t8))))))))))) ?_, ?_⟩
  · omega
  -- the post
  set σ11 := σ10.setv (R 12) 0 with hσ11
  have F48 : SameExcept σ4 σ8 [S 6, S 7] [] := ⟨fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne hy.1, Function.update_of_ne hy.2], fun r _ => by
    simp [hσ8, hσ7, hσ6, hσ5], rfl⟩
  have F511 : SameExcept τ5 σ11 [S 2] [R 12, R 14] := ⟨fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [hσ11, hσ10, outSt, Function.update_of_ne hy], fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hσ11, hσ10, outSt, Function.update_of_ne hr.1, Function.update_of_ne hr.2], rfl⟩
  have F411 : SameExcept σ4 σ11 [S 2, S 4, S 5, S 6, S 7] [R 12, R 14] :=
    ((F48.weaken (by simp) (by simp)).trans (hfr5.weaken (by simp) (by simp))).trans (F511.weaken (by simp) (by simp))
  have hrec : out ++ prefixFields W ws bit i n ++ frameP (binary (W + 1) (encS tz)) ++ [false] =
      out ++ frame (recBits W (childL ws sh bit i)) := by
    rw [frame_recBits, childL_eq, List.flatMap_append]
    have ht : (2 * 2 ^ bit * ((sh / 2 ^ bit + 1 : ℕ) : ℤ) + 1 - (negSum ws bit i ws.length : ℤ)) = tz := by
      rw [htz, htl, hnsum]; push_cast; ring
    rw [ht]
    simp [prefixFields, List.append_assoc, hn]
  have hS0 : σ11.st (S 0) = σ.st (S 0) ∧ σ11.sh (S 0) = σ.sh (S 0) := by
    rw [(F411.1 _ (by simp [emb_eq_iff])).1, (F411.1 _ (by simp [emb_eq_iff])).2, hWS, hWSh]
    exact ⟨by simp [hσ4, hτI], by simp [hσ4]⟩
  have hR0 : σ11.val (R 0) = 0 := by rw [F411.val (by simp [emb_eq_iff])]; simp [hσ4]
  have hR1 : σ11.val (R 1) = 0 := by rw [F411.val (by simp [emb_eq_iff])]; simp [hσ4, emb_eq_iff, hτCW]
  have hR11 : σ11.val (R 11) = 0 := by
    rw [F411.val (by simp [emb_eq_iff])]; simp [hσ4, emb_eq_iff, hDJ4]; omega
  have hR12 : σ11.val (R 12) = 0 := by simp [hσ11]
  have hfin : SameExcept σ σ11 [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] [R 14] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, by rw [F411.cell, hσ4f.cell]⟩
    · by_cases hy0 : y = S 0
      · rw [hy0]; exact hS0
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        have hy1 : y ∉ [S 0, S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hy0, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1,
            hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2⟩
        have hy2 : y ∉ [S 2, S 4, S 5, S 6, S 7] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hy.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1⟩
        have h1 := hσ4f.1 y hy1
        have h2 := F411.1 y hy2
        exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      by_cases r0 : r = R 0
      · rw [r0, hR0, hcp.ci]
      · by_cases r1 : r = R 1
        · rw [r1, hR1, hcp.cw]
        · by_cases r11 : r = R 11
          · rw [r11, hR11, hcp.dj]
          · by_cases r12 : r = R 12
            · rw [r12, hR12, hcp.pass]
            · rw [F411.val (by simp [r12, hr]), hσ4f.val (by simp [r0, r1, r11, r12, hr])]
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · rw [← hrec]; exact ⟨by simp [hσ11, hσ10, outSt], by simp [hσ11, hσ10, outSt], by simp [hσ11, hσ10, outSt, emb_eq_iff]⟩
  · obtain ⟨_, _, ⟨q, hq⟩, ⟨rm, hrm⟩, ⟨dx, hdx⟩, hpw, hpw2, hzr, hsg, hf, hr, hdk, hdt, hcs, hcap⟩ := hpre4'
    have f := F411
    exact ⟨⟨m5, F511.numOn (by simp [emb_eq_iff]) hm5⟩, ⟨_, F511.numOn (by simp [emb_eq_iff]) hX5.1⟩,
      ⟨q, f.numOn (by simp [emb_eq_iff]) hq⟩, ⟨rm, f.numOn (by simp [emb_eq_iff]) hrm⟩,
      ⟨dx, f.numOn (by simp [emb_eq_iff]) hdx⟩, f.numOn (by simp [emb_eq_iff]) hpw, f.numOn (by simp [emb_eq_iff]) hpw2,
      f.numOn (by simp [emb_eq_iff]) hzr, by rw [f.val (by simp [emb_eq_iff])]; exact hsg,
      by rw [f.val (by simp [emb_eq_iff])]; exact hf, by rw [f.val (by simp [emb_eq_iff])]; exact hr,
      by rw [f.val (by simp [emb_eq_iff])]; exact hdk, by rw [f.val (by simp [emb_eq_iff])]; exact hdt,
      by rw [f.val (by simp [emb_eq_iff])]; exact hcs, hcap⟩
  · refine ⟨⟨n5, F511.numOn (by simp [emb_eq_iff]) hn5⟩, ⟨2 * nsum, ?_⟩, ⟨nsum, F411.numOn (by simp [emb_eq_iff]) hNO4'⟩,
      ?_, ?_, hR0, hR1, hR11, hR12, ?_, ?_⟩
    · have : NumOn σ8 (S 7) (W + 1) (2 * nsum) := ⟨by simp [hσ8], by simp [hσ8, hσ7, hσ6, hσ5, hy4.2]⟩
      exact F511.numOn (by simp [emb_eq_iff]) (hfr5.numOn (by simp [emb_eq_iff]) this)
    · rw [(F411.1 _ (by simp [emb_eq_iff])).2]; simp [hσ4, emb_eq_iff, hWkh4]
    · rw [(F411.1 _ (by simp [emb_eq_iff])).1]; simp [hσ4, emb_eq_iff]; exact hWkl4
    · rw [F411.val (by simp [emb_eq_iff]), hσ4v 22 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcp.tmp
    · rw [F411.val (by simp [emb_eq_iff]), hσ4v 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcp.tg
  · rw [F411.val (by simp [emb_eq_iff]), hσ4v 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hIX

end Child

end NearCubicGates.Close.TabMachine
