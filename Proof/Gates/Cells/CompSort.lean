import Proof.Gates.Cells.CompBase
import Proof.Gates.WordPrograms.Sort

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

variable {V M : ℕ}

section SortOp
variable {t : ℕ}

/-- Copy store `m` onto its shadow, record by record. -/
def copyLoopP (m : Fin M) : WMX (NS M t V) (NR M) :=
  .whs (sM m) (.seq (.wm (copyRec (sM m) sTP (rM m) rC1)) (.wm (appendRec sTP (sS m) rC1 rC2)))

/-- The program of `srtM m`. -/
def srtP (m : Fin M) : WMX (NS M t V) (NR M) :=
  .seq (copyLoopP m) (.seq (.wm (closeOut (sS m) rC2)) (.seq (.wm (WM.rewind (sM m) (rM m)))
    (sortRecs (sM m) (sS m) rC1 rC2 rG)))

end SortOp

/-! ## The copy loop -/

section Loop
variable (C : Ctx) (cap : ℕ) {σ0 : WState (NS M (TS C) V) (NR M)} (m : Fin M) (l : List ℕ) (L0 : List Bool)

/-- The state of the copy loop after `j` records. -/
structure CopyInv (j : ℕ) (τ : WState (NS M (TS C) V) (NR M)) : Prop where
  st : τ.st (sM m) = encR C.Wd l
  sh : τ.sh (sM m) = (2 * C.Wd + 1) * j
  rv : τ.val (rM m) = (2 * C.Wd + 1) * j
  tp : ∃ v, τ.st sTP = frame (binary C.Wd v)
  tph : τ.sh sTP = 0
  out : OutOn τ (sS m) rC2 (enc C.Wd (l.take j)) L0
  c1 : τ.val rC1 = 0
  other : ∀ i, i ≠ sM m → i ≠ sTP → i ≠ sS m → τ.st i = σ0.st i ∧ τ.sh i = σ0.sh i
  oval : ∀ r, r ≠ rM m → r ≠ rC2 → τ.val r = σ0.val r
  cell : τ.cell = σ0.cell

theorem take_succ_enc (W : ℕ) (j : ℕ) (hj : j < l.length) :
    enc W (l.take (j + 1)) = enc W (l.take j) ++ frame (binary W (l.getD j 0)) := by
  rw [List.take_add_one, enc_append, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  simp [enc]

theorem copyLoop_ok (hW : 1 ≤ C.Wd)
    (hcap : (2 * C.Wd + 1) * (l.length + 1) + 1 ≤ cap) :
    ∀ k j (τ : WState (NS M (TS C) V) (NR M)), j + k = l.length → CopyInv C (σ0 := σ0) m l L0 j τ →
      ∃ τ', CopyInv C (σ0 := σ0) m l L0 l.length τ' ∧
        WXExec cap (copyLoopP m) τ τ' (k * (80 * C.Wd + 40) + 1) := by
  intro k
  induction k with
  | zero =>
    intro j τ hj hi
    simp only [add_zero] at hj; subst hj
    refine ⟨τ, hi, ?_⟩
    have hb : wbit τ (sM m) = false := by
      simp only [wbit]; rw [hi.st, hi.sh]; exact encR_end_false C.Wd l
    simpa [copyLoopP] using WXExec.whsF (P := (.seq (.wm (copyRec (sM m) sTP (rM m) rC1))
      (.wm (appendRec sTP (sS m) rC1 rC2)) : WMX (NS M (TS C) V) (NR M))) (cap := cap) hb
  | succ k ih =>
    intro j τ hj hi
    have hjl : j < l.length := by omega
    have hb : wbit τ (sM m) = true := by
      simp only [wbit]; rw [hi.st, hi.sh]; exact enc_frame_true C.Wd hW l j hjl
    set v := l.getD j 0
    have hlen := enc_take_length C.Wd l j hjl.le
    obtain ⟨v0, hv0⟩ := hi.tp
    have c1 := copyRec_spec cap (I := sM m) (Wk := sTP) (CI := rM m) (CW := rC1) (by lay_ne) (by lay_ne) τ
      (enc C.Wd (l.take j)) (binary C.Wd v) (encR C.Wd (l.drop (j + 1))) (by rw [hi.st]; exact encR_split C.Wd l j hjl)
      (by rw [hi.sh, hlen]) (by rw [hi.rv, hlen]) hi.tph hi.c1
      (by rw [hv0, frame_binary_length, binary_length]) (by rw [hlen, binary_length]; nlinarith)
    set τ1 := ((τ.sets sTP (frame (binary C.Wd v))).seth (sM m)
      ((enc C.Wd (l.take j)).length + 2 * (binary C.Wd v).length + 1)).setv (rM m)
      ((enc C.Wd (l.take j)).length + 2 * (binary C.Wd v).length + 1) with hτ1
    have hO1 : OutOn τ1 (sS m) rC2 (enc C.Wd (l.take j)) L0 := by
      obtain ⟨o1, o2, o3⟩ := hi.out
      refine ⟨?_, ?_, ?_⟩
      · simp only [hτ1, WState.setv_st, WState.seth_st, WState.sets_st]
        rw [Function.update_of_ne (by lay_ne)]; exact o1
      · simp only [hτ1, WState.setv_sh, WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne (by have := m.isLt; lay_ne)]; exact o2
      · simp only [hτ1, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (by lay_ne)]; exact o3
    have c2 := appendRec_spec cap (Src := sTP) (O := sS m) (CS := rC1) (CO := rC2) (by lay_ne) (by lay_ne) τ1
      (binary C.Wd v) [] (enc C.Wd (l.take j)) L0
      (by simp only [hτ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
          rw [frame_eq_frameP])
      (by simp only [hτ1, WState.setv_sh, WState.seth_sh, WState.sets_sh]
          rw [Function.update_of_ne (by lay_ne)]; exact hi.tph)
      (by simp only [hτ1, WState.setv_val, WState.seth_val, WState.sets_val]
          rw [Function.update_of_ne (by lay_ne)]; exact hi.c1)
      hO1 (by rw [hlen, binary_length]; nlinarith)
    set τ2 := ((τ1.sets (sS m) (overlay (enc C.Wd (l.take j) ++ frame (binary C.Wd v)) L0)).seth (sS m)
      (enc C.Wd (l.take j) ++ frame (binary C.Wd v)).length).setv rC2
      (enc C.Wd (l.take j) ++ frame (binary C.Wd v)).length with hτ2
    have hpos : (enc C.Wd (l.take j)).length + 2 * (binary C.Wd v).length + 1 = (2 * C.Wd + 1) * (j + 1) := by
      rw [hlen, binary_length]; ring
    have he2 : enc C.Wd (l.take j) ++ frame (binary C.Wd v) = enc C.Wd (l.take (j + 1)) :=
      (take_succ_enc l C.Wd j hjl).symm
    have hinv : CopyInv C (σ0 := σ0) m l L0 (j + 1) τ2 := by
      refine ⟨?_, ?_, ?_, ⟨v, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hτ2, hτ1, WState.setv_st, WState.seth_st, WState.sets_st]
        rw [Function.update_of_ne (by have := m.isLt; lay_ne), Function.update_of_ne (by lay_ne)]; exact hi.st
      · simp only [hτ2, hτ1, WState.setv_sh, WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne (by have := m.isLt; lay_ne), Function.update_self, hpos]
      · simp only [hτ2, hτ1, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (by lay_ne), Function.update_self, hpos]
      · simp only [hτ2, hτ1, WState.setv_st, WState.seth_st, WState.sets_st]
        rw [Function.update_of_ne (by lay_ne), Function.update_self]
      · simp only [hτ2, hτ1, WState.setv_sh, WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne (by lay_ne), Function.update_of_ne (by lay_ne)]; exact hi.tph
      · rw [← he2]; exact appendRec_out τ1 (sS m) rC2 (enc C.Wd (l.take j)) L0 (binary C.Wd v)
      · simp only [hτ2, hτ1, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (by lay_ne), Function.update_of_ne (by lay_ne)]; exact hi.c1
      · intro i h1 h2 h3
        simp only [hτ2, hτ1, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          WState.sets_sh]
        rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1]
        exact hi.other i h1 h2 h3
      · intro r h1 h2
        simp only [hτ2, hτ1, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne h2, Function.update_of_ne h1]; exact hi.oval r h1 h2
      · simp only [hτ2, hτ1, WState.setv_cell, WState.seth_cell, WState.sets_cell]; exact hi.cell
    obtain ⟨τ', hi', r'⟩ := ih (j + 1) τ2 (by omega) hinv
    refine ⟨τ', hi', ?_⟩
    have body := WXExec.seq' cap (WXExec.wm c1) (WXExec.wm c2) le_rfl
    exact WXExec.mono (WXExec.whsT hb body r') (by rw [binary_length]; nlinarith)

end Loop

/-! ## `srtM` -/

section Srt
variable (C : Ctx) (cap : ℕ) {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

theorem srtM_ok (he : Enc C a σ) (ha : Valid C a) (hW : 1 ≤ C.Wd) (m : Fin M) (h0 : a.rc m = 0)
    (hcapM : (2 * C.Wd + 1) * ((a.ram m).length + 1) + 1 ≤ cap) :
    ∃ τ, Enc C (a.srt m) τ ∧ WXExec cap (srtP m) σ τ (((a.ram m).length + 1) * KC C) := by
  set l := a.ram m with hlm
  set B := 2 * C.Wd + 1 with hB
  set L0 := σ.st (sS m) with hL0
  have hK := KC_ge2 C
  -- the copy loop
  have hinv0 : CopyInv C (σ0 := σ) m l L0 0 σ := by
    refine ⟨he.ramS m, by rw [he.ramH m, h0], by rw [he.ramR m, h0], he.tpS, he.tpH, ?_, he.zC1,
      fun i _ _ _ => ⟨rfl, rfl⟩, fun r _ _ => rfl, rfl⟩
    refine ⟨by simp [overlay, enc, hL0], by simp [enc, he.shH m], by simp [enc, he.zC2]⟩
  obtain ⟨τ1, hi1, r1⟩ := copyLoop_ok C cap m l L0 hW (by nlinarith) l.length 0 σ (by simp) hinv0
  -- close the shadow
  have hcl := closeOut_spec cap (O := sS m) (CO := rC2) τ1 (enc C.Wd (l.take l.length)) L0 hi1.out
    (by rw [List.take_of_length_le le_rfl, enc_length]; nlinarith)
  rw [List.take_of_length_le le_rfl] at hcl
  set τ2 := ((τ1.sets (sS m) (overlay (enc C.Wd l ++ [false]) L0)).seth (sS m) 0).setv rC2 0 with hτ2
  have hsh2 : overlay (enc C.Wd l ++ [false]) L0 = encR C.Wd l := by
    rw [overlay_short _ _ (by have := he.shL m; rw [he.ramS m] at this; simpa [encR] using this)]; rfl
  -- rewind the store
  have hrw := wrewind_spec cap (sM m) (rM m) (B * l.length) τ2
    (by simp only [hτ2, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (by lay_ne)]; exact hi1.rv)
    (by simp only [hτ2, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (by lay_ne), hi1.rv]; nlinarith)
  set τ3 := (τ2.setv (rM m) 0).seth (sM m) (τ2.sh (sM m) - B * l.length) with hτ3
  have hτ3st : ∀ i, τ3.st i = τ2.st i := fun i => rfl
  have hsM3 : τ3.sh (sM m) = 0 := by
    simp only [hτ3, hτ2, WState.seth_sh, WState.setv_sh, Function.update_self, WState.sets_sh]
    rw [Function.update_of_ne (by have := m.isLt; lay_ne), hi1.sh, hB]; simp
  -- sort
  have hS3 : τ3.st (sM m) = recStream (l.map (binary C.Wd)) := by
    rw [hτ3st]; simp only [hτ2, WState.setv_st, WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne (by have := m.isLt; lay_ne), hi1.st, encR_eq]
  have hS'3 : (τ3.st (sS m)).length = (recStream (l.map (binary C.Wd))).length := by
    rw [hτ3st]; simp only [hτ2, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [hsh2, encR_eq]
  have hS'h3 : τ3.sh (sS m) = 0 := by
    simp only [hτ3, hτ2, WState.seth_sh, WState.setv_sh, WState.sets_sh]
    rw [Function.update_of_ne (by have := m.isLt; lay_ne), Function.update_self]
  have hv3 : ∀ r, r ≠ rM m → r ≠ rC2 → τ3.val r = σ.val r := by
    intro r h1 h2
    simp only [hτ3, hτ2, WState.seth_val, WState.setv_val, WState.sets_val]
    rw [Function.update_of_ne h1, Function.update_of_ne h2]; exact hi1.oval r h1 h2
  have hC1 : τ3.val rC1 = 0 := by rw [hv3 _ (by lay_ne) (by lay_ne)]; exact he.zC1
  have hC2 : τ3.val rC2 = 0 := by
    simp only [hτ3, hτ2, WState.seth_val, WState.setv_val, WState.sets_val]
    rw [Function.update_of_ne (by lay_ne), Function.update_self]
  have hG : τ3.val rG = 0 := by rw [hv3 _ (by lay_ne) (by lay_ne)]; exact he.zG
  have hlen : (recStream (l.map (binary C.Wd))).length = B * l.length + 1 := by
    rw [← encR_eq, encR_length]
  obtain ⟨junk, hj, r4⟩ := sortRecs_spec cap C.Wd (S := sM m) (S' := sS m) (CA := rC1) (CB := rC2) (K := rG)
    (by have := m.isLt; lay_ne) (by lay_ne) (by lay_ne) (by lay_ne) τ3 l hW (fun x hx => ha.ram_lt m x hx) hS3 hsM3
    hS'3 hS'h3 hC1 hC2 hG (by rw [hlen]; nlinarith)
  set τ4 := (τ3.sets (sM m) (recStream ((NearCubicWires.WireExponent3_5.SelectionMachine.Sort.sorted l).map
    (binary C.Wd)))).sets (sS m) junk with hτ4
  have hsorted : NearCubicWires.WireExponent3_5.SelectionMachine.Sort.sorted l = l.insertionSort (· ≤ ·) := rfl
  refine ⟨τ4, ?_, ?_⟩
  · -- the encoding of the sorted store
    have keepS : ∀ i, i ≠ sM m → i ≠ sTP → i ≠ sS m → τ4.st i = σ.st i ∧ τ4.sh i = σ.sh i := by
      intro i h1 h2 h3
      simp only [hτ4, WState.sets_st, WState.sets_sh]
      rw [Function.update_of_ne h3, Function.update_of_ne h1]
      simp only [hτ3, hτ2, WState.seth_sh, WState.setv_sh, WState.sets_sh, WState.setv_st, WState.seth_st,
        WState.sets_st]
      rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h3]
      exact hi1.other i h1 h2 h3
    have keepV : ∀ r, r ≠ rM m → r ≠ rC2 → τ4.val r = σ.val r := fun r h1 h2 => by
      simp only [hτ4, WState.sets_val]; exact hv3 r h1 h2
    refine
      { inS := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.inS
        inH := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.inH
        inR := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.inR
        outS := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.outS
        outH := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.outH
        outR := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.outR
        zero := ⟨by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.zero.1,
          by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.zero.2⟩
        var := fun x => ⟨by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact (he.var x).1,
          by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact (he.var x).2⟩
        ramS := ?_, ramH := ?_, ramR := ?_, shL := ?_, shH := ?_
        tpS := ?_, tpH := ?_
        kiS := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.kiS
        kiH := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.kiH
        kiR := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.kiR
        koS := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.koS
        koH := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.koH
        koR := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.koR
        scS := fun j => by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.scS j
        scH := fun j => by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.scH j
        lgS := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.lgS
        lgH := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.lgH
        ruS := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).1]; exact he.ruS
        ruH := by rw [(keepS _ (by lay_ne) (by lay_ne) (by lay_ne)).2]; exact he.ruH
        zF := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.zF
        zR := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.zR
        zG := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.zG
        zK := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.zK
        zT := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.zT
        zC1 := by rw [keepV _ (by lay_ne) (by lay_ne)]; exact he.zC1
        zC2 := by simp only [hτ4, WState.sets_val]; exact hC2
        cell := by
          simp only [hτ4, hτ3, hτ2, WState.sets_cell, WState.seth_cell, WState.setv_cell]; rw [hi1.cell]; exact he.cell }
    · intro m'
      by_cases hm : m' = m
      · subst hm
        simp only [hτ4, WState.sets_st, Function.update_of_ne (show (sM m' : Fin (NS M (TS C) V + 1)) ≠ sS m' by
          have := m'.isLt; lay_ne), Function.update_self, DS.srt, encR_eq]
        rfl
      · rw [(keepS _ (sM_inj hm) (by lay_ne) (by have := m.isLt; have := m'.isLt; lay_ne)).1, he.ramS m']
        simp [DS.srt, Function.update_of_ne hm]
    · intro m'
      by_cases hm : m' = m
      · subst hm
        simp only [hτ4, WState.sets_sh, DS.srt, h0, mul_zero]; exact hsM3
      · rw [(keepS _ (sM_inj hm) (by lay_ne) (by have := m.isLt; have := m'.isLt; lay_ne)).2, he.ramH m']
        simp [DS.srt]
    · intro m'
      by_cases hm : m' = m
      · subst hm
        simp only [hτ4, WState.sets_val, DS.srt, h0, mul_zero, hτ3, WState.seth_val, WState.setv_val,
          Function.update_self]
      · rw [keepV _ (rM_inj hm) (by lay_ne), he.ramR m']
        simp [DS.srt]
    · intro m'
      by_cases hm : m' = m
      · subst hm
        simp only [hτ4, WState.sets_st, Function.update_self, Function.update_of_ne (show (sM m' : Fin (NS M (TS C) V + 1)) ≠ sS m' by
          have := m'.isLt; lay_ne)]
        rw [hj, ← encR_eq, ← encR_eq, encR_length, encR_length, hsorted, (List.perm_insertionSort _ _).length_eq]
      · rw [(keepS _ (by have := m.isLt; have := m'.isLt; lay_ne) (by lay_ne) (sS_inj hm)).1,
          (keepS _ (sM_inj hm) (by lay_ne) (by have := m.isLt; have := m'.isLt; lay_ne)).1]
        exact he.shL m'
    · intro m'
      by_cases hm : m' = m
      · subst hm; simp only [hτ4, WState.sets_sh]; exact hS'h3
      · rw [(keepS _ (by have := m.isLt; have := m'.isLt; lay_ne) (by lay_ne) (sS_inj hm)).2]; exact he.shH m'
    · obtain ⟨v, hv⟩ := hi1.tp
      refine ⟨v, ?_⟩
      simp only [hτ4, hτ3, hτ2, WState.sets_st, WState.setv_st, WState.seth_st]
      rw [Function.update_of_ne (by lay_ne), Function.update_of_ne (by lay_ne), Function.update_of_ne (by lay_ne)]
      exact hv
    · simp only [hτ4, hτ3, hτ2, WState.sets_sh, WState.setv_sh, WState.seth_sh]
      rw [Function.update_of_ne (by lay_ne), Function.update_of_ne (by lay_ne)]; exact hi1.tph
  · have hK4 := KC_ge4 C
    have hc := sortCost_le C.Wd l.length
    have hlenE : (enc C.Wd l).length = B * l.length := enc_length _ _
    refine WXExec.mono (WXExec.seq' cap r1 (WXExec.seq' cap (WXExec.wm hcl) (WXExec.seq' cap (WXExec.wm hrw) r4
      le_rfl) le_rfl) le_rfl) ?_
    rw [hlenE]
    have h3 := Nat.mul_le_mul_left (l.length + 1) hK4
    have h4 : l.length * (80 * C.Wd + 40) + 1 + 1 + (5 * (B * l.length) + 3 + 1 + (5 * (B * l.length) + 1 + 1 +
        400 * (l.length + 1) * (C.Wd + 1) ^ 2)) ≤ (l.length + 1) * (500 * (C.Wd + 1) ^ 2) := by
      rw [hB]; nlinarith [Nat.zero_le l.length, Nat.zero_le C.Wd]
    omega

end Srt

end NearCubicGates.Close.Cells
