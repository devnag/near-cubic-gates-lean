import Proof.Gates.TabMachine.CompileM2

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
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn split split_spec)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Visit
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- `BodyPre` through any frame that keeps its constants and registers. -/
theorem bodyPre_frame' {cap W : ℕ} {σ τ : WState ns nr} {pw : ℕ} {Ls : List (Fin (ns + 1))} {Rs : List (Fin nr)}
    (h : BodyPre S R cap W σ pw) (hfr : SameExcept σ τ Ls Rs) (h12 : S 12 ∉ Ls) (h13 : S 13 ∉ Ls) (h20 : S 20 ∉ Ls)
    (r2 : R 2 ∉ Rs) (r3 : R 3 ∉ Rs) (r4 : R 4 ∉ Rs) (r15 : R 15 ∉ Rs) (r16 : R 16 ∉ Rs) (r17 : R 17 ∉ Rs)
    (hm : ∃ v, NumOn τ (S 4) (W + 1) v) (hx : ∃ v, NumOn τ (S 6) (W + 1) v) (hq : ∃ v, NumOn τ (S 16) (W + 1) v)
    (hrm : ∃ v, NumOn τ (S 17) (W + 1) v) (hdx : ∃ v, NumOn τ (S 18) (W + 1) v) : BodyPre S R cap W τ pw :=
  ⟨hm, hx, hq, hrm, hdx, hfr.numOn h12 h.hpw, hfr.numOn h13 h.hpw2, hfr.numOn h20 h.zr,
    by rw [hfr.val r4]; exact h.sg, by rw [hfr.val r2]; exact h.f, by rw [hfr.val r3]; exact h.r,
    by rw [hfr.val r16]; exact h.dk, by rw [hfr.val r17]; exact h.dt, by rw [hfr.val r15]; exact h.cs, h.cap⟩

theorem decIf_spec (cap : ℕ) (r : Fin nr) (τ : WState ns nr) (i : ℕ) (hi : τ.val r = i) (hcap : i ≤ cap) :
    WXExec cap (.ifr r (WMX.dec r) WMX.skip) τ (τ.setv r (i - 1)) 2 := by
  by_cases h0 : i = 0
  · have hv : τ.val r = 0 := by rw [hi, h0]
    exact (WXExec.ifrF hv (WXExec.skip cap τ)).cast cap (BinW.setv_same (by rw [hi, h0])).symm (by omega)
  · have hv : τ.val r ≠ 0 := by rw [hi]; exact h0
    exact (WXExec.ifrT hv (WXExec.dec cap r τ (by omega))).cast cap (by rw [hi]) (by omega)

theorem bodyPre_setv {cap W : ℕ} {τ : WState ns nr} {pw : ℕ} (h : BodyPre S R cap W τ pw) (k : Fin 24)
    (hk : k ∉ [(2 : Fin 24), 3, 4, 15, 16, 17]) (v : ℕ) : BodyPre S R cap W (τ.setv (R k) v) pw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  have e : ∀ j : Fin 24, j ≠ k → (τ.setv (R k) v).val (R j) = τ.val (R j) :=
    fun j hj => by simp [Function.update_of_ne (emb_ne R hj)]
  exact ⟨h.m.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩, h.x.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩,
    h.q.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩, h.rm.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩,
    h.dx.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩, BinW.numOn_setv h.hpw _ _, BinW.numOn_setv h.hpw2 _ _,
    BinW.numOn_setv h.zr _ _, by rw [e 4 (Ne.symm hk.2.2.1)]; exact h.sg, by rw [e 2 (Ne.symm hk.1)]; exact h.f,
    by rw [e 3 (Ne.symm hk.2.1)]; exact h.r, by rw [e 16 (Ne.symm hk.2.2.2.2.1)]; exact h.dk,
    by rw [e 17 (Ne.symm hk.2.2.2.2.2)]; exact h.dt, by rw [e 15 (Ne.symm hk.2.2.2.1)]; exact h.cs, h.cap⟩

theorem childPre_setv {cap W : ℕ} {τ : WState ns nr} (h : ChildPre S R cap W τ) (k : Fin 24)
    (hk : k ∉ [(0 : Fin 24), 1, 11, 12, 22, 5]) (v : ℕ) : ChildPre S R cap W (τ.setv (R k) v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  have e : ∀ j : Fin 24, j ≠ k → (τ.setv (R k) v).val (R j) = τ.val (R j) :=
    fun j hj => by simp [Function.update_of_ne (emb_ne R hj)]
  exact ⟨h.n.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩, h.y.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩,
    h.no.elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩, by simpa using h.wkh, by simpa using h.wkl,
    by rw [e 0 (Ne.symm hk.1)]; exact h.ci, by rw [e 1 (Ne.symm hk.2.1)]; exact h.cw,
    by rw [e 11 (Ne.symm hk.2.2.1)]; exact h.dj, by rw [e 12 (Ne.symm hk.2.2.2.1)]; exact h.pass,
    by rw [e 22 (Ne.symm hk.2.2.2.2.1)]; exact h.tmp, by rw [e 5 (Ne.symm hk.2.2.2.2.2)]; exact h.tg⟩

/-- One visit `(bit, i)`, `i = IX`. -/
def iStep : WMX ns nr :=
  .seq (getAt (S 0) (S 3) (R 0) (R 1) (R 10) (R 20))
  (.seq (split (S 3) (S 4) (R 4) (R 2) (R 3))
  (.seq (.ifr (R 4) (WMX.dec (R 4)) WMX.skip)
  (.seq (BinW.divmod (S 4) (S 12) (S 16) (S 17) (S 18) (R 2) (R 3) (R 16) (R 17))
  (.seq (.wm (SInt.sgnBitW (S 16) (R 21)))
  (.seq (.ifr (R 21) (.seq (WMX.dec (R 21)) (emitChild S R)) WMX.skip)
  (.ifr (R 10) (WMX.dec (R 10)) WMX.skip))))))

/-- The record of the visit `(bit, i)`: the child if bit `bit` of `|w_i|` is set. -/
def visitRec (W : ℕ) (ws : List ℤ) (sh bit i : ℕ) : List Bool :=
  if (ws.getD i 0).natAbs.testBit bit then frame (recBits W (childL ws sh bit i)) else []

/-- The cost bound of a visit. -/
def visitCost (W n i : ℕ) : ℕ := (n + 1) * (40 * (W + 1) + 40) + 10 * (n + 1) * (2 * (W + 1) + 1) + 10 +
  76 * W + 125 + 5 + BinW.divCost (W + 1) + 8 + childCost W n i + 10 + 20

theorem testBit_eq_div (a b : ℕ) : a.testBit b = (a / 2 ^ b % 2 == 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ b) with h | h <;> simp [h]

theorem iStep_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool) (sh bit i tl : ℕ)
    (out L0 : List Bool) (hi : i < ws.length) (hpre : BodyPre S R cap W σ (2 ^ bit)) (hcp : ChildPre S R cap W σ)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hTL : NumOn σ (S 14) (W + 1) tl) (htl : tl = 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1) (htlb : tl < 2 ^ W)
    (hIX : σ.val (R 10) = i) (hK4 : σ.val (R 20) = 0) (hF2 : σ.val (R 21) = 0)
    (hKD : OutOn σ (S 2) (R 14) out L0)
    (hw : ∀ z ∈ ws, 2 * z.natAbs + 2 ≤ 2 ^ W) (hbit : 2 ^ (bit + 2) ≤ 2 ^ (W + 1))
    (hsum : (ws.map fun z => 2 * z.natAbs + 1).sum < 2 ^ W)
    (hcapO : out.length + (ws.length + 1) * (2 * (W + 1) + 1) + 1 ≤ cap)
    (hcapI : (ws.length + 1) * (2 * (W + 1) + 1) + 2 * ws.length + 2 ≤ cap) :
    Runs cap (iStep S R) σ (visitCost W ws.length i) (fun τ =>
      OutOn τ (S 2) (R 14) (out ++ visitRec W ws sh bit i) L0 ∧ BodyPre S R cap W τ (2 ^ bit) ∧
      ChildPre S R cap W τ ∧ τ.val (R 10) = i - 1 ∧ τ.val (R 20) = 0 ∧ τ.val (R 21) = 0 ∧
      SameExcept σ τ [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] [R 10, R 14]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  set x := ws.getD i 0 with hx
  set a := x.natAbs with ha
  have hxmem : x ∈ ws := by rw [hx, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  -- (1) `Wk := encS w_i`
  have h1 := getAt_spec (A := S 0) (Wk := S 3) (CA := R 0) (CW := R 1) (N := R 10) (K2 := R 20) cap (hne (by decide))
    (by simp [emb_eq_iff]) (W + 1) (by omega) (ws.map encS) i (by simpa using hi) σ junk
    (by rw [hWS, List.map_map]; rfl) hWSh hcp.ci hcp.wkh hcp.wkl hcp.cw hIX hK4 (by simp; nlinarith)
  have hgi : (ws.map encS)[i]'(by simpa using hi) = encS x := by
    rw [List.getElem_map, hx, List.getD_eq_getElem _ _ hi]
  rw [hgi] at h1
  set σ1 := σ.sets (S 3) (frame (binary (W + 1) (encS x))) with hσ1
  -- (2) `M := |w_i|`, `Sg := [w_i < 0]`; (3) `Sg := 0`
  obtain ⟨m0, hm0⟩ := hpre.m
  have h2 := split_spec (X := S 3) (M := S 4) (S := R 4) (F := R 2) (R := R 3) cap W (hne (by decide)) (hner (by decide)) σ1 x m0
    ⟨BinW.numOn_sets_self _ _ _ _ hcp.wkh, by have := hw x hxmem; omega⟩
    (BinW.numOn_sets_ne hm0 (hne (by decide)) _) (by simp [hσ1, hpre.sg]) (by simp [hσ1, hpre.f])
    (by simp [hσ1, hpre.r]) hpre.cap
  set σ2 := (σ1.sets (S 4) (frame (binary (W + 1) a))).setv (R 4) (decide (x < 0)).toNat with hσ2
  have h3 : WXExec cap (.ifr (R 4) (WMX.dec (R 4)) WMX.skip) σ2 (σ1.sets (S 4) (frame (binary (W + 1) a))) 2 := by
    by_cases hneg : x < 0
    · have hv : σ2.val (R 4) ≠ 0 := by simp [hσ2, hneg]
      refine (WXExec.ifrT hv (WXExec.dec cap (R 4) σ2 (by simp [hσ2, hneg]; have := hpre.cap; omega))).cast cap ?_
        (by omega)
      apply WState.eq <;> try rfl
      funext r; by_cases hr : r = R 4
      · subst hr; simp [hσ2, hσ1, hneg, hpre.sg]
      · simp [hσ2, Function.update_of_ne hr]
    · have hv : σ2.val (R 4) = 0 := by simp [hσ2, hneg]
      refine (WXExec.ifrF hv (WXExec.skip cap σ2)).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; by_cases hr : r = R 4
      · subst hr; simp [hσ2, hσ1, hneg, hpre.sg]
      · simp [hσ2, Function.update_of_ne hr]
  set σ3 := σ1.sets (S 4) (frame (binary (W + 1) a)) with hσ3
  -- (4) `Q := a / 2^bit`
  obtain ⟨q0, hq0⟩ := hpre.q
  obtain ⟨r0, hr0⟩ := hpre.rm
  obtain ⟨d0, hd0⟩ := hpre.dx
  have hlift : ∀ (k : Fin 24) (v : ℕ), k ≠ 3 → k ≠ 4 → NumOn σ (S k) (W + 1) v → NumOn σ3 (S k) (W + 1) v :=
    fun k v h3 h4 h => BinW.numOn_sets_ne (BinW.numOn_sets_ne h (hne h3) _) (hne h4) _
  have h4 := BinW.divmod_spec (A := S 4) (B := S 12) (Q := S 16) (M := S 17) (X := S 18) (F := R 2) (R := R 3)
    (K := R 16) (T := R 17) cap (W + 1) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hner (by decide))
    (hner (by decide)) (hner (by decide)) (hner (by decide)) σ3 a (2 ^ bit) q0 r0 d0
    (BinW.numOn_sets_self _ _ _ _ (by simp [hσ1, hm0.2])) (hlift _ _ (by decide) (by decide) hpre.hpw)
    (hlift _ _ (by decide) (by decide) hq0) (hlift _ _ (by decide) (by decide) hr0)
    (hlift _ _ (by decide) (by decide) hd0) (by simp [hσ3, hσ1, hpre.f]) (by simp [hσ3, hσ1, hpre.r])
    (by simp [hσ3, hσ1, hpre.dk]) (by simp [hσ3, hσ1, hpre.dt]) (by have := hw x hxmem; omega)
    (Nat.pow_pos (by norm_num)) (by rw [pow_succ] at hbit; omega) (by have := hpre.cap; omega)
  set σ4 := ((σ3.sets (S 16) (frame (binary (W + 1) (a / 2 ^ bit)))).sets (S 17)
    (frame (binary (W + 1) (a % 2 ^ bit)))).sets (S 18) (frame (binary (W + 1) 0)) with hσ4

  have h5 := WXExec.wm (SInt.sgnBitW_spec cap (X := S 16) (S := R 21) σ4 W (a / 2 ^ bit)
    ⟨by simp [hσ4], by simp [hσ4, hσ3, hσ1, hq0.2]⟩ (by simp [hσ4, hσ3, hσ1, hF2]) (by have := hpre.cap; omega))
  set σ5 := σ4.setv (R 21) (a / 2 ^ bit % 2) with hσ5
  set σ5' := σ4.setv (R 21) 0 with hσ5'
  have hfr5 : SameExcept σ σ5' [S 3, S 4, S 16, S 17, S 18] [R 21] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hσ5', hσ4, hσ3, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1,
        Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hσ5', hσ4, hσ3, hσ1, Function.update_of_ne hr]
  have hpre5 : BodyPre S R cap W σ5' (2 ^ bit) :=
    bodyPre_frame' S R hpre hfr5 (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) (by simp [emb_eq_iff])
      (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) (by simp [emb_eq_iff])
      (by simp [emb_eq_iff]) (by simp [emb_eq_iff])
      ⟨a, by simp [hσ5', hσ4, hσ3, emb_eq_iff], by simp [hσ5', hσ4, hσ3, hσ1, hm0.2]⟩
      (hpre.x.elim fun v hv => ⟨v, hfr5.numOn (by simp [emb_eq_iff]) hv⟩)
      ⟨a / 2 ^ bit, by simp [hσ5', hσ4, emb_eq_iff], by simp [hσ5', hσ4, hσ3, hσ1, hq0.2]⟩
      ⟨a % 2 ^ bit, by simp [hσ5', hσ4, emb_eq_iff], by simp [hσ5', hσ4, hσ3, hσ1, hr0.2]⟩
      ⟨0, by simp [hσ5', hσ4], by simp [hσ5', hσ4, hσ3, hσ1, hd0.2]⟩
  have hcp5 : ChildPre S R cap W σ5' :=
    ⟨hcp.n.elim fun v hv => ⟨v, hfr5.numOn (by simp [emb_eq_iff]) hv⟩,
      hcp.y.elim fun v hv => ⟨v, hfr5.numOn (by simp [emb_eq_iff]) hv⟩,
      hcp.no.elim fun v hv => ⟨v, hfr5.numOn (by simp [emb_eq_iff]) hv⟩, by simp [hσ5', hσ4, hσ3, hσ1, hcp.wkh],
      by simp [hσ5', hσ4, hσ3, hσ1, emb_eq_iff, frame_length],
      by rw [hfr5.val (by simp [emb_eq_iff])]; exact hcp.ci, by rw [hfr5.val (by simp [emb_eq_iff])]; exact hcp.cw,
      by rw [hfr5.val (by simp [emb_eq_iff])]; exact hcp.dj, by rw [hfr5.val (by simp [emb_eq_iff])]; exact hcp.pass,
      by rw [hfr5.val (by simp [emb_eq_iff])]; exact hcp.tmp, by rw [hfr5.val (by simp [emb_eq_iff])]; exact hcp.tg⟩
  have hKD5 : OutOn σ5' (S 2) (R 14) out L0 :=
    ⟨by rw [hfr5.st (by simp [emb_eq_iff]), hKD.1], by rw [hfr5.sh (by simp [emb_eq_iff]), hKD.2.1],
      by rw [hfr5.val (by simp [emb_eq_iff]), hKD.2.2]⟩
  -- (6) the child, if the bit is set
  set P6 : WState ns nr → Prop := fun τ =>
    OutOn τ (S 2) (R 14) (out ++ visitRec W ws sh bit i) L0 ∧ BodyPre S R cap W τ (2 ^ bit) ∧
      ChildPre S R cap W τ ∧ τ.val (R 10) = i ∧ τ.val (R 20) = 0 ∧ τ.val (R 21) = 0 ∧
      SameExcept σ5' τ [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] [R 14] with hP6
  have h6 : Runs cap (.ifr (R 21) (.seq (WMX.dec (R 21)) (emitChild S R)) WMX.skip) σ5
      (childCost W ws.length i + 3) P6 := by
    have hbt : a.testBit bit = (a / 2 ^ bit % 2 == 1) := testBit_eq_div a bit
    rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ bit) with hb | hb
    · have hv : σ5.val (R 21) = 0 := by simp [hσ5, hb]
      have e : σ5 = σ5' := by rw [hσ5, hσ5', hb]
      refine (Runs.ifrF hv (Runs.of (WXExec.skip cap σ5) ?_)).cost (by omega)
      rw [e]
      have hvr : visitRec W ws sh bit i = [] := by
        unfold visitRec; rw [← hx, ← ha, hbt, hb]; rfl
      refine ⟨by rw [hvr, List.append_nil]; exact hKD5, hpre5, hcp5, ?_, ?_, by simp [hσ5'], SameExcept.refl _ _ _⟩
      · rw [hfr5.val (by simp [emb_eq_iff])]; exact hIX
      · rw [hfr5.val (by simp [emb_eq_iff])]; exact hK4
    · have hv : σ5.val (R 21) ≠ 0 := by simp [hσ5, hb]
      have hd := WXExec.dec cap (R 21) σ5 (by simp [hσ5, hb]; have := hpre.cap; omega)
      have e : σ5.setv (R 21) (σ5.val (R 21) - 1) = σ5' := by
        rw [hσ5']; apply WState.eq <;> try rfl
        funext r; by_cases hr : r = R 21
        · subst hr; simp [hσ5, hb]
        · simp [hσ5, Function.update_of_ne hr]
      rw [e] at hd
      have hc := emitChild_spec S R cap W σ5' ws junk sh bit i tl out L0 hi hpre5 hcp5
        (by rw [hfr5.st (by simp [emb_eq_iff]), hWS]) (by rw [hfr5.sh (by simp [emb_eq_iff]), hWSh])
        (hfr5.numOn (by simp [emb_eq_iff]) hTL) htl htlb (by rw [hfr5.val (by simp [emb_eq_iff])]; exact hIX) hKD5
        hw hbit hsum hcapO (by omega)
      refine (Runs.ifrT hv (Runs.seqE hd (hc.post fun τ hτ => ?_))).cost (by omega)
      obtain ⟨hKDτ, hpreτ, hcpτ, hIXτ, hfrτ⟩ := hτ
      have hvr : visitRec W ws sh bit i = frame (recBits W (childL ws sh bit i)) := by
        unfold visitRec; rw [← hx, ← ha, hbt, hb]; rfl
      refine ⟨by rw [hvr]; exact hKDτ, hpreτ, hcpτ, hIXτ, ?_, ?_, hfrτ⟩
      · rw [hfrτ.val (by simp [emb_eq_iff])]; simp [hσ5', hσ4, hσ3, hσ1, emb_eq_iff, hK4]
      · rw [hfrτ.val (by simp [emb_eq_iff])]; simp [hσ5']
  -- (7) `IX := i − 1`
  refine (Runs.seqE h1 (Runs.seqE h2 (Runs.seqE h3 (Runs.seqE h4 (Runs.seqE h5 (Runs.seq (c2 := 2) h6
    (fun τ hτ => ?_))))))).cost ?_
  · obtain ⟨hKDτ, hpreτ, hcpτ, hIXτ, hK4τ, hF2τ, hfrτ⟩ := hτ
    refine Runs.of (decIf_spec cap (R 10) τ i hIXτ (by omega)) ⟨?_, bodyPre_setv S R hpreτ 10 (by decide) _,
      childPre_setv S R hcpτ 10 (by decide) _, by simp, ?_, ?_, ?_⟩
    · exact ⟨by simp [hKDτ.1], by simp [hKDτ.2.1], by
        simp [Function.update_of_ne (hner (show (14 : Fin 24) ≠ 10 by decide)), hKDτ.2.2]⟩
    · simp [Function.update_of_ne (hner (show (20 : Fin 24) ≠ 10 by decide)), hK4τ]
    · simp [Function.update_of_ne (hner (show (21 : Fin 24) ≠ 10 by decide)), hF2τ]
    · have h1' := hfr5.comp' hfrτ
      refine ⟨fun y hy => ?_, fun r hr => ?_, by simp [h1'.cell]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        have hy' : y ∉ [S 3, S 4, S 16, S 17, S 18] ++ [S 2, S 3, S 4, S 5, S 6, S 7, S 15, S 16, S 17, S 18] := by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨⟨hy.2.1, hy.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2⟩,
            hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1,
            hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2⟩
        simpa using h1'.1 y hy'
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [WState.setv_val, Function.update_of_ne hr.1]
        by_cases r21 : r = R 21
        · rw [r21, hF2τ, hF2]
        · exact h1'.val (by simp [r21, hr.2])
  · unfold visitCost; nlinarith

end Visit

end NearCubicGates.Close.TabMachine
