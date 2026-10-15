import Proof.Gates.TabMachine.Occ

/-! # One variable occurrence, part 2: **`occA_spec`** (restriction, compiler input, compiler) -/

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
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section OccA2
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

theorem ixS_not_mem (j : Fin 24) (hj : j ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23])
    (h11 : j ≠ 11) : ixS j ∉ [(47 : Fin 64), 48, 49, 50, 51, 52, 11, 0] := by
  revert j; decide

theorem ixR_ne (j : Fin 24) : ixR j ≠ 77 := by revert j; decide

def occACost (W n s k p kd : ℕ) : ℕ :=
  restrictCost W n k p + 1 + (s * (copyStep (W + 1) n + 8) + 7 * s + 3 + 1 + (5 * (s * (2 * (W + 1) + 1)) + 3 + 1 +
    (compileCost W s + 1 + (5 * kd + 3))))

theorem occA_spec (cap W s k : ℕ) (σ : WState ns nr) (xs : List ℕ) (junk : List Bool) (p c : ℕ) (o : Occ)
    (hrest : GRest Z Y cap W s k σ)
    (hpg : σ.st (Z 46) = recStream (xs.map (binary (W + 1))) ++ junk) (hpgh : σ.sh (Z 46) = 0)
    (hblk : (xs.drop p).take (occLen o) = occRecs o) (hk : o.inW.length = k) (hs : o.outW.length = s)
    (hIDX : σ.val (Y 77) = p) (hCX : NumOn σ (Z 54) (W + 1) c) (hc : c < 2 ^ (W + 1))
    (hbound : (o.inW.map Int.natAbs).sum + o.thr.natAbs + 1 < 2 ^ W)
    (hB : 4 * totalL o.outW + 2 * s + 4 ≤ 2 ^ W) (ht : (rTarget o c).natAbs + totalL o.outW < 2 ^ W)
    (hcap : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * xs.length + 2 * k + 2 * s ≤ cap)
    (hcapC : (compRecs W o.outW (rTarget o c)).length + (s + 1) * (2 * (W + 1) + 1) + 2 * s + 4 * W + 8 ≤ cap) :
    Runs cap (occA Z Y) σ (occACost W xs.length s k p (compRecs W o.outW (rTarget o c)).length) (fun τ =>
      GRest Z Y cap W s k τ ∧ (∃ junk', τ.st (Z 2) = recStream ((o.kids c).map (recBits W)) ++ junk') ∧
        τ.sh (Z 2) = 0 ∧ τ.val (Y 77) = p + occLen o ∧ SameExcept σ τ (occAStreams Z) [Y 77]) := by
  have hne : ∀ {a b : Fin 64}, a ≠ b → Z a ≠ Z b := fun h => emb_ne Z h
  have hner : ∀ {a b : Fin 112}, a ≠ b → Y a ≠ Y b := fun h => emb_ne Y h
  obtain ⟨hseg, hout, hlen⟩ := drop_take_seg xs p o hblk
  rw [hk] at hseg hout
  rw [hs] at hout
  have hz := hrest.zero
  -- (1) the restriction
  have h1 := restrictP_spec (zA Z) (yB Y) cap W xs σ p c o (by rw [hk]; exact hseg) hbound hc
    (hrest.rPre Z Y xs ⟨junk, hpg⟩ hpgh) hIDX hCX (by rw [hk]; exact hrest.r84) (hz 85 (by decide))
    (hz 86 (by decide)) (by rw [hk]; omega)
  rw [hk] at h1
  refine Runs.seq h1 fun τ1 hτ1 => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hτ1
  have hv1 : ∀ r : Fin 112, r ≠ 77 → τ1.val (Y r) = σ.val (Y r) := fun r hr => a7.val (by
    simp only [yB_apply, List.mem_singleton]; intro e; exact hr (Y.injective e ▸ rfl))
  have hs1 : ∀ i : Fin 64, i ∉ [(47 : Fin 64), 48, 49, 50, 51, 52, 11] → τ1.st (Z i) = σ.st (Z i) ∧
      τ1.sh (Z i) = σ.sh (Z i) := fun i hi => a7.1 _ (by
    simp only [zA_apply, List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hi ⊢
    simpa [ixA] using hi)
  -- (2) the outer weights into the compiler's input stream
  have hO1 : OutOn τ1 (Z 0) (Y 88) [] (τ1.st (Z 0)) := outOn_start τ1 (Z 0) (Y 88)
    (by rw [(hs1 0 (by decide)).2]; exact hrest.closed 0 (by simp)) (by rw [hv1 88 (by decide)]; exact hz 88 (by decide))
  have hsegR : segRecs (W + 1) xs (p + 2 + k) s = (o.outW.map fun z => binary (W + 1) (encS z)).flatMap frame := by
    unfold segRecs; rw [show p + 2 + k = p + (2 + k) by ring, hout, List.flatMap_map, List.flatMap_map]
  have h2 := copyN_spec cap (A := Z 46) (Wk := Z 47) (O := Z 0) (CA := Y 75) (CW := Y 76) (CUR := Y 77) (K2 := Y 78)
    (CS := Y 87) (CO := Y 88) (KC := Y 89) (KC2 := Y 90) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) (W + 1)
    (by omega) xs (p + 2 + k) s (by unfold occLen at hlen; omega) τ1 junk [] (τ1.st (Z 0))
    (by rw [(hs1 46 (by decide)).1]; exact hpg) (by rw [(hs1 46 (by decide)).2]; exact hpgh)
    (a1.zero 0 (by simp)) (a1.zero 1 (by simp)) (a1.zero 3 (by simp))
    (by rw [hv1 87 (by decide)]; exact hz 87 (by decide)) a1.wh a1.wl a3
    (by rw [hv1 89 (by decide)]; exact hrest.r89) (by rw [hv1 90 (by decide)]; exact hz 90 (by decide)) hO1
    (by omega) (by simp; nlinarith)
  refine Runs.seq h2 fun τ2 hτ2 => ?_
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hτ2
  rw [hsegR] at b1
  -- (3) close the compiler's input stream
  set out0 := (o.outW.map fun z => binary (W + 1) (encS z)).flatMap frame with hout0
  have hlen0 : out0.length = s * (2 * (W + 1) + 1) := by
    rw [← hsegR, segRecs_length _ _ _ _ (by unfold occLen at hlen; omega)]
  have hc3 := closeOut_spec cap (O := Z 0) (CO := Y 88) τ2 out0 (τ1.st (Z 0)) b1 (by rw [hlen0]; nlinarith)
  rw [hlen0] at hc3
  refine Runs.seqE (WXExec.wm hc3) ?_
  set τ3 := ((τ2.sets (Z 0) (overlay (out0 ++ [false]) (τ1.st (Z 0)))).seth (Z 0) 0).setv (Y 88) 0 with hτ3
  have hst3 : ∀ i : Fin 64, i ∉ [(47 : Fin 64), 48, 49, 50, 51, 52, 11, 0] → τ3.st (Z i) = σ.st (Z i) ∧
      τ3.sh (Z i) = σ.sh (Z i) := by
    intro i hi
    have hi0 : Z i ≠ Z 0 := by rw [Ne, emb_eq_iff]; rintro rfl; simp at hi
    have hi47 : Z i ∉ [Z 47, Z 0] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, emb_eq_iff]
      exact ⟨by rintro rfl; simp at hi, by rintro rfl; simp at hi⟩
    have e2 := b7.1 _ hi47
    have e1 := hs1 i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; tauto)
    simp only [hτ3, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh,
      Function.update_of_ne hi0]
    exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
  have hv3 : ∀ r : Fin 112, r ≠ 77 → τ3.val (Y r) = σ.val (Y r) := by
    intro r hr
    by_cases r88 : r = 88
    · subst r88; simp [hτ3]; exact (hz 88 (by decide)).symm
    · have hY : Y r ≠ Y 88 := by rw [Ne, emb_eq_iff]; exact r88
      simp only [hτ3, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_of_ne hY]
      rw [b7.val (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, emb_eq_iff]; exact ⟨hr, r88⟩),
        hv1 r hr]
  -- (4) the compiler
  have hT3 : SNumOn τ3 (Z 11) W (rTarget o c) := by
    have e1 : τ3.st (Z 11) = τ1.st (Z 11) ∧ τ3.sh (Z 11) = τ1.sh (Z 11) := by
      have hn : Z 11 ∉ [Z 47, Z 0] := by simp [emb_eq_iff]
      have e2 := b7.1 _ hn
      have hn0 : Z 11 ≠ Z 0 := by simp [emb_eq_iff]
      simp only [hτ3, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh,
        Function.update_of_ne hn0]
      exact e2
    exact ⟨⟨by rw [e1.1]; exact a2.1.1, by rw [e1.2]; exact a2.1.2⟩, a2.2⟩
  have hcp : CompPre (zS Z) (yR Y) cap W τ3 := by
    have hc0 := hrest.compPre Z Y
    refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, fun j h13 h14 => ?_, hc0.cap⟩
    · by_cases j11 : j = 11
      · subst j11; exact ⟨_, hT3.1⟩
      · obtain ⟨v, hv⟩ := hc0.words j hj
        have hn := ixS_not_mem j hj j11
        have e1 := (hst3 _ hn).1
        have e2 := (hst3 _ hn).2
        exact ⟨v, by rw [zS_apply, e1]; exact hv.1, by rw [zS_apply, e2]; exact hv.2⟩
    · rw [zS_apply, (hst3 _ (by decide)).2]; exact hc0.wkh
    · rw [zS_apply, (hst3 _ (by decide)).1]; exact hc0.wkl
    · have e1 := (hst3 (ixS 20) (by decide)).1
      have e2 := (hst3 (ixS 20) (by decide)).2
      exact ⟨by rw [zS_apply, e1]; exact hc0.zr.1, by rw [zS_apply, e2]; exact hc0.zr.2⟩
    · have e1 := (hst3 (ixS 21) (by decide)).1
      have e2 := (hst3 (ixS 21) (by decide)).2
      exact ⟨by rw [zS_apply, e1]; exact hc0.tw.1, by rw [zS_apply, e2]; exact hc0.tw.2⟩
    · rw [yR_apply, hv3 _ (ixR_ne j)]; exact hc0.regs j h13 h14
  have hWS3 : τ3.st (zS Z 0) = recStream (o.outW.map fun z => binary (W + 1) (encS z)) ++
      (τ1.st (Z 0)).drop (out0 ++ [false]).length := by
    simp only [zS_apply, hτ3, WState.setv_st, WState.seth_st, WState.sets_st]
    rw [show ixS 0 = (0 : Fin 64) from rfl, Function.update_self, overlay, recStream, hout0, List.append_assoc]
  have hWSh3 : τ3.sh (zS Z 0) = 0 := by
    simp only [zS_apply, hτ3, WState.setv_sh, WState.seth_sh]
    rw [show ixS 0 = (0 : Fin 64) from rfl, Function.update_self]
  have hS13 : ∃ v, NumOn τ3 (zS Z 1) (W + 1) v := by
    obtain ⟨v, hv⟩ := hrest.s1 Z Y
    have e1 := hst3 (ixS 1) (by decide)
    exact ⟨v, by rw [zS_apply, e1.1]; exact hv.1, by rw [zS_apply, e1.2]; exact hv.2⟩
  have hNR : τ3.val (yR Y 13) = o.outW.length := by rw [yR_apply, hv3 _ (ixR_ne 13), hs]; exact hrest.r13
  have hKD : OutOn τ3 (zS Z 2) (yR Y 14) [] (τ3.st (zS Z 2)) := outOn_start τ3 _ _
    (by rw [zS_apply, (hst3 (ixS 2) (by decide)).2]; exact hrest.closed 2 (by simp))
    (by rw [yR_apply, hv3 _ (ixR_ne 14)]; exact hz 14 (by decide))
  have h4 := compile_spec (zS Z) (yR Y) cap W τ3 o.outW _ (rTarget o c) [] (τ3.st (zS Z 2)) hcp hS13 hT3 hWS3 hWSh3
    hNR hKD (by rw [hs]; exact hB) ht (by simp only [List.length_nil, hs]; omega)
  rw [hs] at h4
  refine Runs.seq h4 fun τ4 hτ4 => ?_
  obtain ⟨d1, d2, d3, d4, d5⟩ := hτ4
  simp only [List.nil_append] at d1
  -- (5) close the child stream
  have hkd : (compRecs W o.outW (rTarget o c)).length ≤ cap := by omega
  have hc5 := closeOut_spec cap (O := zS Z 2) (CO := yR Y 14) τ4 (compRecs W o.outW (rTarget o c))
    (τ3.st (zS Z 2)) d1 hkd
  refine Runs.of (WXExec.wm hc5) ?_
  set τ5 := ((τ4.sets (zS Z 2) (overlay (compRecs W o.outW (rTarget o c) ++ [false]) (τ3.st (zS Z 2)))).seth
    (zS Z 2) 0).setv (yR Y 14) 0 with hτ5
  -- the frames, as index lists
  have f1 : SameExcept σ τ1 ((([1, 2, 3, 4, 5, 6, 7] : List (Fin 10)).map ixA).map Z) [Y 77] := a7
  have f2 : SameExcept τ1 τ2 (([47, 0] : List (Fin 64)).map Z) [Y 77, Y 88] := b7
  have f3 : SameExcept τ2 τ3 (([0] : List (Fin 64)).map Z) [Y 88] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ3]⟩
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
      simp [hτ3, Function.update_of_ne hx]
    · simp only [List.mem_singleton] at hr
      simp [hτ3, Function.update_of_ne hr]
  have f4 : SameExcept τ3 τ4 ((([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] :
      List (Fin 24)).map ixS).map Z) [Y 14] := d5
  have f5 : SameExcept τ4 τ5 (([2] : List (Fin 64)).map Z) [Y 14] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ5]⟩
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
      have hx' : x ≠ Z (ixS 2) := hx
      simp [hτ5, zS_apply, Function.update_of_ne hx']
    · simp only [List.mem_singleton] at hr
      have hr' : r ≠ Y (ixR 14) := hr
      simp [hτ5, Function.update_of_ne hr']
  have hall := (((f1.comp' f2).comp' f3).comp' f4).comp' f5
  have hfr : SameExcept σ τ5 (occAStreams Z) [Y 77, Y 88, Y 14] := by
    refine hall.weaken ?_ ?_
    · intro x hx
      simp only [List.mem_append] at hx
      unfold occAStreams
      rcases hx with (((h | h) | h) | h) | h
      · exact map_subset Z (([1, 2, 3, 4, 5, 6, 7] : List (Fin 10)).map ixA) occAIdx (by decide) x h
      · exact map_subset Z ([47, 0] : List (Fin 64)) occAIdx (by decide) x h
      · exact map_subset Z ([0] : List (Fin 64)) occAIdx (by decide) x h
      · exact map_subset Z (([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] :
          List (Fin 24)).map ixS) occAIdx (by decide) x h
      · exact map_subset Z ([2] : List (Fin 64)) occAIdx (by decide) x h
    · intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
  -- (6) the post-state
  have hZ2 : zS Z 2 = Z 2 := rfl
  have hY14 : yR Y 14 = Y 14 := rfl
  have hmem : ∀ i : Fin 64, Z i ∈ occAStreams Z ↔ i ∈ occAIdx := fun i => by
    unfold occAStreams; rw [List.mem_map]
    exact ⟨fun ⟨j, hj, e⟩ => Z.injective e ▸ hj, fun h => ⟨i, h, rfl⟩⟩
  have hs5 : ∀ i : Fin 64, i ≠ 2 → τ5.st (Z i) = τ4.st (Z i) ∧ τ5.sh (Z i) = τ4.sh (Z i) := fun i hi =>
    f5.1 _ (by simp only [List.map_cons, List.map_nil, List.mem_singleton, emb_eq_iff]; exact hi)
  have hs4 : ∀ i : Fin 64, i ∉ (([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] :
      List (Fin 24)).map ixS) → τ4.st (Z i) = τ3.st (Z i) ∧ τ4.sh (Z i) = τ3.sh (Z i) := fun i hi =>
    f4.1 _ (by rw [List.map_map]; intro hm; obtain ⟨j, hj, e⟩ := List.mem_map.mp hm
               exact hi (List.mem_map.mpr ⟨j, hj, Z.injective e⟩))
  have hs3 : ∀ i : Fin 64, i ≠ 0 → τ3.st (Z i) = τ2.st (Z i) ∧ τ3.sh (Z i) = τ2.sh (Z i) := fun i hi =>
    f3.1 _ (by simp only [List.map_cons, List.map_nil, List.mem_singleton, emb_eq_iff]; exact hi)
  have hs2 : ∀ i : Fin 64, i ≠ 47 → i ≠ 0 → τ2.st (Z i) = τ1.st (Z i) ∧ τ2.sh (Z i) = τ1.sh (Z i) :=
    fun i h47 h0 => f2.1 _ (by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff]
      exact fun h => h.elim h47 h0)
  have hv5 : ∀ r : Fin 112, r ≠ 14 → τ5.val (Y r) = τ4.val (Y r) := fun r hr =>
    f5.2.1 _ (by simp only [List.mem_singleton, emb_eq_iff]; exact hr)
  have hv4 : ∀ r : Fin 112, r ≠ 14 → τ4.val (Y r) = τ3.val (Y r) := fun r hr =>
    f4.2.1 _ (by simp only [List.mem_singleton, emb_eq_iff]; exact hr)
  have h14 : τ5.val (Y 14) = 0 := by simp [hτ5, hY14]
  have h88 : τ5.val (Y 88) = 0 := by
    rw [hv5 88 (by decide), hv4 88 (by decide), hv3 88 (by decide)]; exact hz 88 (by decide)
  have h77 : τ5.val (Y 77) = p + occLen o := by
    rw [hv5 77 (by decide), hv4 77 (by decide)]
    have e3 : τ3.val (Y 77) = τ2.val (Y 77) := by
      simp only [hτ3, WState.setv_val, WState.seth_val, WState.sets_val]
      rw [Function.update_of_ne (by rw [Ne, emb_eq_iff]; decide)]
    rw [e3, b2]; unfold occLen; rw [hk, hs]; omega
  -- the w1 words
  have hwS : ∀ j : Fin 24, j ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] →
      ∃ v, NumOn τ5 (Z (ixS j)) (W + 1) v := by
    intro j hj
    have hj2 : ixS j ≠ 2 := by revert j hj; decide
    obtain ⟨v, hv⟩ := d2.words j hj
    exact ⟨v, by rw [(hs5 _ hj2).1]; exact hv.1, by rw [(hs5 _ hj2).2]; exact hv.2⟩
  have hwA : ∀ j : Fin 10, j ∈ [(2 : Fin 10), 3, 4, 5, 6] → ∃ v, NumOn τ5 (Z (ixA j)) (W + 1) v := by
    intro j hj
    have hj' : j ∈ [(2 : Fin 10), 3, 4, 5, 6, 7] := by revert j hj; decide
    have n2 : ixA j ≠ 2 := by revert j hj; decide
    have n0 : ixA j ≠ 0 := by revert j hj; decide
    have n47 : ixA j ≠ 47 := by revert j hj; decide
    have nS : ixA j ∉ (([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] :
      List (Fin 24)).map ixS) := by revert j hj; decide
    obtain ⟨v, hv⟩ := a1.words j hj'
    refine ⟨v, ?_, ?_⟩
    · rw [(hs5 _ n2).1, (hs4 _ nS).1, (hs3 _ n0).1, (hs2 _ n47 n0).1]; exact hv.1
    · rw [(hs5 _ n2).2, (hs4 _ nS).2, (hs3 _ n0).2, (hs2 _ n47 n0).2]; exact hv.2
  have hw1cases : ∀ i ∈ w1List, i = 1 ∨
      (∃ j : Fin 24, j ∈ [(4 : Fin 24), 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] ∧ ixS j = i) ∨
      (∃ j : Fin 10, j ∈ [(2 : Fin 10), 3, 4, 5, 6] ∧ ixA j = i) := by decide
  have hGR : GRest Z Y cap W s k τ5 := by
    refine grest_frame Z Y hrest hfr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi _
      rcases hw1cases i hi with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · obtain ⟨v, hv⟩ := d3
        exact ⟨v, by rw [(hs5 1 (by decide)).1]; exact hv.1, by rw [(hs5 1 (by decide)).2]; exact hv.2⟩
      · exact hwS j hj
      · exact hwA j hj
    · intro i hi hm; rw [hmem] at hm
      exact absurd hm ((by decide : ∀ i ∈ wcList, i ∉ occAIdx) i hi)
    · intro i hi hm; rw [hmem] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(20 : Fin 64), 21, 53, 26, 44, 45, 55], i ∉ occAIdx) i hi)
    · intro i hi _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [(hs5 3 (by decide)).1, (hs5 3 (by decide)).2]; exact ⟨d2.wkh, d2.wkl⟩
      · have nS : (47 : Fin 64) ∉ (([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] :
          List (Fin 24)).map ixS) := by decide
        rw [(hs5 47 (by decide)).1, (hs5 47 (by decide)).2, (hs4 47 nS).1, (hs4 47 nS).2,
          (hs3 47 (by decide)).1, (hs3 47 (by decide)).2]
        exact ⟨b3, b4⟩
    · intro i hi hm; rw [hmem] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(24 : Fin 64), 33], i ∉ occAIdx) i hi)
    · intro i hi hm
      rw [hmem] at hm
      have hi' : i = 0 ∨ i = 2 := (by decide : ∀ i ∈ [(0 : Fin 64), 2, 30, 31, 32], i ∈ occAIdx → i = 0 ∨ i = 2) i hi hm
      rcases hi' with rfl | rfl
      · have nS : (0 : Fin 64) ∉ (([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23] :
          List (Fin 24)).map ixS) := by decide
        rw [(hs5 0 (by decide)).2, (hs4 0 nS).2]
        simp [hτ3]
      · simp [hτ5, hZ2]
    · intro r hr hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      rcases hm with rfl | rfl | rfl
      · exact absurd hr (by decide)
      · exact h88
      · exact h14
    · intro r hr hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      exact absurd hm ((by decide : ∀ r ∈ [(13 : Fin 112), 32, 41, 66, 84, 89], ¬ (r = 77 ∨ r = 88 ∨ r = 14)) r hr)
  refine ⟨hGR, ⟨(τ3.st (zS Z 2)).drop (compRecs W o.outW (rTarget o c) ++ [false]).length, ?_⟩, ?_, h77, ?_⟩
  · simp only [hτ5, WState.setv_st, WState.seth_st, WState.sets_st, ← hZ2, Function.update_self]
    rw [overlay, compRecs_stream]; rfl
  · simp [hτ5, hZ2]
  · refine ⟨hfr.1, fun r hr => ?_, hfr.2.2⟩
    by_cases r88 : r = Y 88
    · subst r88; rw [h88]; exact (hz 88 (by decide)).symm
    · by_cases r14 : r = Y 14
      · subst r14; rw [h14]; exact (hz 14 (by decide)).symm
      · exact hfr.2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)

end OccA2

end NearCubicGates.Close.TabMachine
