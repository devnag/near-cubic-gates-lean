import Proof.Gates.CheckedPCPP.CompRunA

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.Comp

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq NearCubicGates.Close.WordPrograms
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary.Streaming (marks)

section RunB
variable {t2 : ℕ} (E : LinearCodeFamily) {bud : MessageRequest → ℕ}
  (wf : WordFunction MessageRequest messageWord (fun m => FramedSim.pairs (List.ofFn (E.enc m.1 m.2.val))) bud)
  {t4 s4 : ℕ} (M4 : Machine t4 s4) (in4 out4 : Fin t4) {t5 s5 : ℕ} (M5 : Machine t5 s5) (in5 out5 : Fin t5)

/-- The cost bound of `phaseB`. -/
def costB (q L V f4 cwl f5 pbl rbl : ℕ) : ℕ :=
  DescW.descCost q L V + 1 + (5 * (V * (12 * V + 18) + 14 * V + 20) + 1) + 1 + f4 + 1 +
    (22 * cwl + 1 + 1 + 7 + 1 + (5 * (2 * cwl + 1) + 1)) + 1 + f5 + 1 + (22 * pbl + 22 * rbl + 30)

theorem runB (hin4 : in4.val = 0) (hio4 : in4 ≠ out4) (hin5 : in5.val = 0) (hio5 : in5 ≠ out5) (D : Circuit) (V : ℕ)
    (hV : (PCPPNative.descriptor D.D).length + E.length D.n * (5 * D.n + 8) + D.n + E.length D.n + 8 ≤ V)
    (cap : ℕ) (hcap : 200 * (V + 1) * (V + 1) ≤ cap) (f4 : ℕ) (o4 : Fin t4 → List Bool)
    (h4 : ClockJoin.ReadyRun M4 f4 (fun i => if i.val = 0 then
      RepairOrdinary.frame (PCPPNative.descriptor (checkedCircuit E D).D) else []) o4)
    (cw : List Bool) (hcw : o4 out4 = RepairOrdinary.frame cw) (hcwc : 2 * cw.length + 2 ≤ cap) (f5 : ℕ)
    (o5 : Fin t5 → List Bool) (h5 : ClockJoin.ReadyRun M5 f5 (fun i => if i.val = 0 then
      RepairOrdinary.frame cw else []) o5)
    (pb rb rest : List Bool) (hwo : o5 out5 = RepairOrdinary.frame pb ++ RepairOrdinary.frame rb ++ rest)
    (hpbc : 2 * pb.length + 2 * rb.length + 2 ≤ cap) (σ : WState (NS t2 wf.program.tapeCount t4 t5) 64)
    (hDD : σ.st (DD2 t2 wf.program.tapeCount t4 t5) = RepairOrdinary.frame (PCPPNative.descriptor D.D))
    (hDDh : σ.sh (DD2 t2 wf.program.tapeCount t4 t5) = 0)
    (hmat : ∀ p, readTapeBit (σ.st (MAT t2 wf.program.tapeCount t4 t5)) p = matBit E D.n p)
    (hMATh : σ.sh (MAT t2 wf.program.tapeCount t4 t5) = 0) (hL : σ.val (descH 16) = E.length D.n)
    (hF : Fresh t2 wf.program.tapeCount t4 t5 σ) :
    ∃ τ, WXExec cap (phaseB (t2 := t2) E wf M4 in4 out4 M5 in5 out5) σ τ
        (costB D.n (E.length D.n) V f4 cw.length f5 pb.length rb.length) ∧
      τ.st (b4 t2 wf.program.tapeCount t4 t5 out4) = RepairOrdinary.frame cw ∧
      τ.st (b5 t2 wf.program.tapeCount t4 t5 out5) = o5 out5 ∧
      τ.st (PO t2 wf.program.tapeCount t4 t5) = RepairOrdinary.frame pb ∧
      τ.st (RO t2 wf.program.tapeCount t4 t5) = RepairOrdinary.frame rb ∧
      τ.st (MAT t2 wf.program.tapeCount t4 t5) = σ.st (MAT t2 wf.program.tapeCount t4 t5) ∧
      τ.sh (MAT t2 wf.program.tapeCount t4 t5) = E.length D.n * D.n ∧
      τ.val (descH 9) = D.n ∧ τ.val (descH 16) = E.length D.n ∧
      τ.st (SUP t2 wf.program.tapeCount t4 t5) = [] ∧ τ.sh (SUP t2 wf.program.tapeCount t4 t5) = 0 ∧
      (∀ i, τ.val (supG i) = 0) ∧ τ.val rP2 = 0 ∧ τ.val rA2 = 0 ∧ τ.val rT = 0 := by
  -- 8. the checked descriptor
  obtain ⟨τ8, e8, h8O, h8Oh, h8H7, h8M, h8q, h8L, h8cl, h8fr, h8len, h8math⟩ := DescW.descW_runs cap descH
    (DD2 t2 wf.program.tapeCount t4 t5) (SN t2 wf.program.tapeCount t4 t5) (SC t2 wf.program.tapeCount t4 t5)
    (b4 t2 wf.program.tapeCount t4 t5 in4) (MAT t2 wf.program.tapeCount t4 t5)
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
          not_false_eq_true]
        split_ands <;> dst)
    E D V hV hcap σ hDD hDDh hF.sn.1 hF.sn.2 hF.sc.1 hF.sc.2 (hF.b4 in4).1 (hF.b4 in4).2 hmat hMATh hF.dh hL
  have hlenV : (τ8.st (b4 t2 wf.program.tapeCount t4 t5 in4)).length ≤ cap := by nlinarith
  have hst8 : ∀ y, y ∉ [DD2 t2 wf.program.tapeCount t4 t5, SN t2 wf.program.tapeCount t4 t5,
      SC t2 wf.program.tapeCount t4 t5, b4 t2 wf.program.tapeCount t4 t5 in4, MAT t2 wf.program.tapeCount t4 t5] →
      τ8.st y = σ.st y ∧ τ8.sh y = σ.sh y := fun y hy => ⟨h8fr.st hy, h8fr.sh hy⟩
  have hv8 : ∀ r, (∀ i, descH i ≠ r) → τ8.val r = σ.val r := fun r hr =>
    h8fr.val (by simp only [List.mem_ofFn, not_exists]; exact hr)
  -- 9. rewind the descriptor
  have e9 := wrewind_spec (cap := cap) (b4 t2 wf.program.tapeCount t4 t5 in4) (descH 7)
    (τ8.st (b4 t2 wf.program.tapeCount t4 t5 in4)).length τ8 h8H7 (by rw [h8H7]; exact hlenV)
  set τ9 := (τ8.setv (descH 7) 0).seth (b4 t2 wf.program.tapeCount t4 t5 in4)
    (τ8.sh (b4 t2 wf.program.tapeCount t4 t5 in4) - (τ8.st (b4 t2 wf.program.tapeCount t4 t5 in4)).length) with hτ9

  have hin4' : ∀ j, j ≠ in4 → b4 t2 wf.program.tapeCount t4 t5 j ∉ [DD2 t2 wf.program.tapeCount t4 t5,
      SN t2 wf.program.tapeCount t4 t5, SC t2 wf.program.tapeCount t4 t5, b4 t2 wf.program.tapeCount t4 t5 in4,
      MAT t2 wf.program.tapeCount t4 t5] := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by dst, by dst, by dst, fun e => hj (b4_inj _ _ _ _ e), by dst⟩
  obtain ⟨τ10, e10, hd10⟩ := Dock.ready_mach cap h4 (b4_inj _ _ _ _) τ9
    (fun j => by
      by_cases hj : j = in4
      · subst hj; simp [hτ9, h8Oh]
      · simp [hτ9, Function.update_of_ne (fun e => hj (b4_inj _ _ _ _ e)), (hst8 _ (hin4' j hj)).2, (hF.b4 j).2])
    (fun j => by
      by_cases hj : j = in4
      · subst hj; simp [hτ9, h8O, hin4]
      · have hj0 : j.val ≠ 0 := fun e => hj (Fin.ext (by rw [e, hin4]))
        simp [hτ9, (hst8 _ (hin4' j hj)).1, (hF.b4 j).1, hj0])
  have hother10 : ∀ y, (∀ j, b4 t2 wf.program.tapeCount t4 t5 j ≠ y) → τ10.st y = τ8.st y ∧ τ10.sh y = τ8.sh y := by
    intro y hy
    rw [(hd10.other y hy).1, (hd10.other y hy).2]
    simp [hτ9, Function.update_of_ne (Ne.symm (hy in4))]
  have hv10 : ∀ r, r ≠ descH 7 → τ10.val r = τ8.val r := by
    intro r hr; rw [hd10.val]; simp [hτ9, Function.update_of_ne hr]
  -- 11. copy the circuit word
  have hCW2 : τ10.st (b5 t2 wf.program.tapeCount t4 t5 in5) = [] ∧ τ10.sh (b5 t2 wf.program.tapeCount t4 t5 in5) = 0 := by
    rw [(hother10 _ (fun j => by dst)).1, (hother10 _ (fun j => by dst)).2]
    have hy : b5 t2 wf.program.tapeCount t4 t5 in5 ∉ [DD2 t2 wf.program.tapeCount t4 t5, SN t2 wf.program.tapeCount t4 t5,
        SC t2 wf.program.tapeCount t4 t5, b4 t2 wf.program.tapeCount t4 t5 in4, MAT t2 wf.program.tapeCount t4 t5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by dst, by dst, by dst, by dst, by dst⟩
    rw [(hst8 _ hy).1, (hst8 _ hy).2]; exact hF.b5 in5
  have hP10 : τ10.val rP = 0 := by
    rw [hv10 rP (by rdst), hv8 rP (fun i => by rdst)]; exact hF.misc.1
  have e11 := Glue.copyFrameW_spec cap (b4 t2 wf.program.tapeCount t4 t5 out4) (b5 t2 wf.program.tapeCount t4 t5 in5)
    (by dst) rP cw [] [] τ10 (by rw [hd10.st, hcw]; simp) (by rw [hd10.sh]; rfl) hCW2.1 hCW2.2 hP10 hcwc
  set τ11 := (τ10.sets (b5 t2 wf.program.tapeCount t4 t5 in5) (RepairOrdinary.frame cw)).seth
    (b4 t2 wf.program.tapeCount t4 t5 out4) ([].length + 2 * cw.length) with hτ11

  have hb5 : ∀ j, j ≠ in5 → τ11.st (b5 t2 wf.program.tapeCount t4 t5 j) = [] ∧
      τ11.sh (b5 t2 wf.program.tapeCount t4 t5 j) = 0 := by
    intro j hj
    have hne : b5 t2 wf.program.tapeCount t4 t5 j ≠ b5 t2 wf.program.tapeCount t4 t5 in5 :=
      fun e => hj (b5_inj _ _ _ _ e)
    simp only [hτ11, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh,
      Function.update_of_ne hne, Function.update_of_ne (show b5 t2 wf.program.tapeCount t4 t5 j ≠
        b4 t2 wf.program.tapeCount t4 t5 out4 by dst)]
    rw [(hother10 _ (fun j' => by dst)).1, (hother10 _ (fun j' => by dst)).2]
    have hy : b5 t2 wf.program.tapeCount t4 t5 j ∉ [DD2 t2 wf.program.tapeCount t4 t5, SN t2 wf.program.tapeCount t4 t5,
        SC t2 wf.program.tapeCount t4 t5, b4 t2 wf.program.tapeCount t4 t5 in4, MAT t2 wf.program.tapeCount t4 t5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by dst, by dst, by dst, by dst, by dst⟩
    rw [(hst8 _ hy).1, (hst8 _ hy).2]; exact hF.b5 j
  obtain ⟨τ12, e12, hd12⟩ := Dock.ready_mach cap h5 (b5_inj _ _ _ _) τ11
    (fun j => by
      by_cases hj : j = in5
      · subst hj
        simp [hτ11, Function.update_of_ne (show b5 t2 wf.program.tapeCount t4 t5 j ≠
          b4 t2 wf.program.tapeCount t4 t5 out4 by dst), hCW2.2]
      · exact (hb5 j hj).2)
    (fun j => by
      by_cases hj : j = in5
      · subst hj; simp [hτ11, hin5]
      · have hj0 : j.val ≠ 0 := fun e => hj (Fin.ext (by rw [e, hin5]))
        simp [(hb5 j hj).1, hj0])
  -- 13. the header
  have hPO12 : ∀ y, y.val < 12 → y.val ≥ 9 → τ12.st y = [] ∧ τ12.sh y = 0 := by
    intro y h1 h2
    rw [(hd12.other y (fun j e => by have := congrArg Fin.val e; simp only [b5_val] at this; omega)).1,
      (hd12.other y (fun j e => by have := congrArg Fin.val e; simp only [b5_val] at this; omega)).2]
    simp only [hτ11, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh,
      Function.update_of_ne (show y ≠ b5 t2 wf.program.tapeCount t4 t5 in5 from fin_ne (by simp only [b5_val]; omega)),
      Function.update_of_ne (show y ≠ b4 t2 wf.program.tapeCount t4 t5 out4 from fin_ne (by simp only [b4_val]; omega))]
    rw [(hother10 _ (fun j e => by have := congrArg Fin.val e; simp only [b4_val] at this; omega)).1,
      (hother10 _ (fun j e => by have := congrArg Fin.val e; simp only [b4_val] at this; omega)).2]
    have hy : y ∉ [DD2 t2 wf.program.tapeCount t4 t5, SN t2 wf.program.tapeCount t4 t5,
        SC t2 wf.program.tapeCount t4 t5, b4 t2 wf.program.tapeCount t4 t5 in4, MAT t2 wf.program.tapeCount t4 t5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fin_ne (by simp only [DD2_val]; omega), fin_ne (by simp only [SN_val]; omega),
        fin_ne (by simp only [SC_val]; omega), fin_ne (by simp only [b4_val]; omega), fin_ne (by simp only [MAT_val]; omega)⟩
    rw [(hst8 _ hy).1, (hst8 _ hy).2]
    by_cases h9 : y.val = 9
    · have : y = PO t2 wf.program.tapeCount t4 t5 := Fin.ext (by simp [h9])
      subst this; exact hF.po
    · by_cases h10 : y.val = 10
      · have : y = RO t2 wf.program.tapeCount t4 t5 := Fin.ext (by simp [h10])
        subst this; exact hF.ro
      · have : y = SUP t2 wf.program.tapeCount t4 t5 := Fin.ext (by simp; omega)
        subst this; exact hF.sup
  have hPO := hPO12 (PO t2 wf.program.tapeCount t4 t5) (by simp) (by simp)
  have hRO := hPO12 (RO t2 wf.program.tapeCount t4 t5) (by simp) (by simp)
  have hP12 : τ12.val rP = 0 := by rw [hd12.val]; simp [hτ11, hP10]
  obtain ⟨τ13, e13, h13PO, h13RO, h13WO, h13fr⟩ := Glue.headerW_spec cap (b5 t2 wf.program.tapeCount t4 t5 out5)
    (PO t2 wf.program.tapeCount t4 t5) (RO t2 wf.program.tapeCount t4 t5)
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
          not_false_eq_true]
        split_ands <;> dst) rP pb rb rest τ12 (by rw [hd12.st, hwo]) (by rw [hd12.sh])
    hPO.1 hPO.2 hRO.1 hRO.2 (by rw [hP12]; omega)
  -- facts at the end
  have hv13 : ∀ r, r ≠ rP → r ≠ descH 7 → τ13.val r = τ8.val r := by
    intro r h1 h2
    rw [h13fr.val (by simp [h1]), hd12.val]; simp [hτ11, hv10 r h2]
  have hst13 : ∀ y, y ∉ [b5 t2 wf.program.tapeCount t4 t5 out5, PO t2 wf.program.tapeCount t4 t5,
      RO t2 wf.program.tapeCount t4 t5] → (∀ j, b5 t2 wf.program.tapeCount t4 t5 j ≠ y) →
      τ13.st y = τ11.st y ∧ τ13.sh y = τ11.sh y := by
    intro y h1 h2
    rw [h13fr.st h1, h13fr.sh h1, (hd12.other y h2).1, (hd12.other y h2).2]
    exact ⟨rfl, rfl⟩
  have hMAT13 := hst13 (MAT t2 wf.program.tapeCount t4 t5)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by dst, by dst, by dst⟩) (fun j => by dst)
  have hMAT11 : τ11.st (MAT t2 wf.program.tapeCount t4 t5) = τ8.st (MAT t2 wf.program.tapeCount t4 t5) ∧
      τ11.sh (MAT t2 wf.program.tapeCount t4 t5) = τ8.sh (MAT t2 wf.program.tapeCount t4 t5) := by
    simp only [hτ11, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh,
      Function.update_of_ne (show MAT t2 wf.program.tapeCount t4 t5 ≠ b5 t2 wf.program.tapeCount t4 t5 in5 by dst),
      Function.update_of_ne (show MAT t2 wf.program.tapeCount t4 t5 ≠ b4 t2 wf.program.tapeCount t4 t5 out4 by dst)]
    exact hother10 _ (fun j => by dst)
  have hSUP := hPO12 (SUP t2 wf.program.tapeCount t4 t5) (by simp) (by simp)
  have hSUP13 := hst13 (SUP t2 wf.program.tapeCount t4 t5)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by dst, by dst, by dst⟩) (fun j => by dst)
  have hSUP12 : τ11.st (SUP t2 wf.program.tapeCount t4 t5) = [] ∧ τ11.sh (SUP t2 wf.program.tapeCount t4 t5) = 0 := by
    rw [← (hd12.other _ (fun j => by dst)).1, ← (hd12.other _ (fun j => by dst)).2]; exact hSUP
  refine ⟨τ13, WXExec.mono (WXExec.seq e8 (WXExec.seq (WXExec.wm e9) (WXExec.seq e10 (WXExec.seq (WXExec.wm e11)
    (WXExec.seq e12 (WXExec.wm e13)))))) ?_, ?_, ?_, h13PO, h13RO, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold costB; omega
  · have h := hst13 (b4 t2 wf.program.tapeCount t4 t5 out4)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by dst, by dst, by dst⟩)
      (fun j => by dst)
    rw [h.1]
    simp [hτ11, Function.update_of_ne (show b4 t2 wf.program.tapeCount t4 t5 out4 ≠ b5 t2 wf.program.tapeCount t4 t5 in5
      by dst), hd10.st, hcw]
  · rw [h13WO, hd12.st]
  · rw [hMAT13.1, hMAT11.1, h8M]
  · rw [hMAT13.2, hMAT11.2, h8math]
  · rw [hv13 (descH 9) (by rdst) (by rdst), h8q]
  · rw [hv13 (descH 16) (by rdst) (by rdst), h8L]
  · rw [hSUP13.1, hSUP12.1]
  · rw [hSUP13.2, hSUP12.2]
  · intro i; rw [hv13 (supG i) (by rdst) (by rdst), hv8 (supG i) (fun i' => by rdst)]; exact hF.sg i
  · rw [hv13 rP2 (by rdst) (by rdst), hv8 rP2 (fun i' => by rdst)]; exact hF.misc.2.1
  · rw [hv13 rA2 (by rdst) (by rdst), hv8 rA2 (fun i' => by rdst)]; exact hF.misc.2.2.1
  · rw [hv13 rT (by rdst) (by rdst), hv8 rT (fun i' => by rdst)]; exact hF.misc.2.2.2

end RunB

end NearCubicGates.Close.CheckedPCPP.Comp
