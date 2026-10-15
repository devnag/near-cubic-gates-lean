import Proof.Gates.CheckedPCPP.CompLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.Comp

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq NearCubicGates.Close.WordPrograms
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The entry state: `h` on `HS`, `d` on `DS`, every other stream empty, every head and register `0`. -/
def init (t2 te t4 t5 : ℕ) (h d : List Bool) : WState (NS t2 te t4 t5) 64 :=
  ⟨fun _ => 0, fun i => if i = HS t2 te t4 t5 then h else if i = DS t2 te t4 t5 then d else [], fun _ => 0, false⟩

/-- Streams and registers that phases 2 and 3 still need empty / zero. -/
structure Fresh (t2 te t4 t5 : ℕ) (τ : WState (NS t2 te t4 t5) 64) : Prop where
  sn : τ.st (SN t2 te t4 t5) = [] ∧ τ.sh (SN t2 te t4 t5) = 0
  sc : τ.st (SC t2 te t4 t5) = [] ∧ τ.sh (SC t2 te t4 t5) = 0
  po : τ.st (PO t2 te t4 t5) = [] ∧ τ.sh (PO t2 te t4 t5) = 0
  ro : τ.st (RO t2 te t4 t5) = [] ∧ τ.sh (RO t2 te t4 t5) = 0
  sup : τ.st (SUP t2 te t4 t5) = [] ∧ τ.sh (SUP t2 te t4 t5) = 0
  b4 : ∀ j, τ.st (b4 t2 te t4 t5 j) = [] ∧ τ.sh (b4 t2 te t4 t5 j) = 0
  b5 : ∀ j, τ.st (b5 t2 te t4 t5 j) = [] ∧ τ.sh (b5 t2 te t4 t5 j) = 0
  dh : ∀ i : Fin 19, i ≠ 16 → τ.val (descH i) = 0
  sg : ∀ i, τ.val (supG i) = 0
  misc : τ.val rP = 0 ∧ τ.val rP2 = 0 ∧ τ.val rA2 = 0 ∧ τ.val rT = 0

section RunA
variable {t2 s2 : ℕ} (M2 : Machine t2 s2) (in2 out2 : Fin t2) (E : LinearCodeFamily) {bud : MessageRequest → ℕ}
  (wf : WordFunction MessageRequest messageWord (fun m => FramedSim.pairs (List.ofFn (E.enc m.1 m.2.val))) bud)
  (t4 t5 : ℕ) (Cb eb : ℕ)

/-- The cost bound of `phaseA`. -/
def costA (hl dl f2 wl q L B te : ℕ) : ℕ :=
  FrameIn.frameInCost hl dl + 1 + f2 + 1 + (22 * wl + 1 + 1 + 7 + 1 + (5 * (2 * wl + 1) + 1)) + 1 +
    Glue.readQCost wl + 1 + (18 * q + 3 + 1 + 3 + 1 + 4 * Cb + 1 + EncSetup.powCost B eb + 1 + (7 * B + 1) + 1 +
    (3 * (q + 1) + 1)) + 1 + (B * (7 + 8) + 7 * B + 3 + 1 + (18 * B + 3 + 1 + (5 * B + 1 + 1 + (18 * B + 3 + 1 +
    (5 * B + 1))))) + 1 + encColsCost q L B te

theorem runA (hin2 : in2.val = 0) (hio : in2 ≠ out2) (x t : List Bool) {n : ℕ} (c : BooleanCircuit n) (f2 : ℕ)
    (o2 : Fin t2 → List Bool)
    (h2 : ClockJoin.ReadyRun M2 f2 (fun i => if i.val = 0 then RepairOrdinary.frame (RepairOrdinary.frame x ++
      RepairOrdinary.frame t) ++ RepairOrdinary.frame (PCPPNative.descriptor c) else []) o2)
    (q : ℕ) (w' : List Bool) (hw : o2 out2 = RepairOrdinary.frame (natWord q ++ w')) (hq : 2 ≤ q)
    (hqw : q ≤ (natWord q ++ w').length)
    (hBnd : ∀ i, i < q → (RepairOrdinary.frame (messageWord (unitReq q i hq))).length + bud (unitReq q i hq) + 1 ≤
      Cb * (q + 1) ^ eb)
    (hBL : 2 * E.length q ≤ Cb * (q + 1) ^ eb) (cap : ℕ)
    (hcap : 16 * (RepairOrdinary.frame x ++ RepairOrdinary.frame t).length + 16 * (PCPPNative.descriptor c).length +
      40 + 2 * (natWord q ++ w').length + 8 * (natWord q ++ w').length + 20 + 2 * (Cb * (q + 1) ^ eb) +
      (Cb * (q + 1) ^ eb) * (Cb * (q + 1) ^ eb) + (E.length q + 1) * q + 3 * (Cb * (q + 1) ^ eb) + 4 * q + 30 ≤ cap) :
    ∃ τ, WXExec cap (phaseA M2 in2 out2 E wf (t4 := t4) (t5 := t5) Cb eb)
        (init t2 wf.program.tapeCount t4 t5 (RepairOrdinary.frame x ++ RepairOrdinary.frame t)
          (PCPPNative.descriptor c)) τ
        (costA Cb eb (RepairOrdinary.frame x ++ RepairOrdinary.frame t).length (PCPPNative.descriptor c).length f2
          (natWord q ++ w').length q (E.length q) (Cb * (q + 1) ^ eb) wf.program.tapeCount) ∧
      τ.st (DD2 t2 wf.program.tapeCount t4 t5) = RepairOrdinary.frame (natWord q ++ w') ∧
      τ.sh (DD2 t2 wf.program.tapeCount t4 t5) = 0 ∧
      (∀ p, readTapeBit (τ.st (MAT t2 wf.program.tapeCount t4 t5)) p = matBit E q p) ∧
      τ.sh (MAT t2 wf.program.tapeCount t4 t5) = 0 ∧ τ.val (encR 9) = E.length q ∧
      Fresh t2 wf.program.tapeCount t4 t5 τ := by
  -- notation-free abbreviations (only for states and streams)
  set σ0 := init t2 wf.program.tapeCount t4 t5 (RepairOrdinary.frame x ++ RepairOrdinary.frame t)
    (PCPPNative.descriptor c) with hσ0
  have i0st : ∀ y, y ≠ HS t2 wf.program.tapeCount t4 t5 → y ≠ DS t2 wf.program.tapeCount t4 t5 → σ0.st y = [] := by
    intro y h1 h2; simp [hσ0, init, h1, h2]
  have hHSDS : HS t2 wf.program.tapeCount t4 t5 ≠ DS t2 wf.program.tapeCount t4 t5 := (by dst)
  have hHSA : HS t2 wf.program.tapeCount t4 t5 ≠ b2 t2 wf.program.tapeCount t4 t5 in2 := (by dst)
  have hDSA : DS t2 wf.program.tapeCount t4 t5 ≠ b2 t2 wf.program.tapeCount t4 t5 in2 := (by dst)
  -- 1. entry framing
  obtain ⟨τ1, e1, h1A, h1Ah, h1R, h1fr⟩ := FrameIn.frameInW_spec cap (HS t2 wf.program.tapeCount t4 t5)
    (DS t2 wf.program.tapeCount t4 t5) (b2 t2 wf.program.tapeCount t4 t5 in2)
    (by simp [hHSDS, hHSA, hDSA]) (ChecksW.Rw (DescW.Gof descH)) x t c σ0 (by simp [hσ0, init])
    rfl (by simp [hσ0, init, Ne.symm hHSDS]) rfl (i0st _ (Ne.symm hHSA) (Ne.symm hDSA)) rfl (fun i => rfl)
    (by omega)

  have hin : ∀ j, τ1.st (b2 t2 wf.program.tapeCount t4 t5 j) = (fun i : Fin t2 => if i.val = 0 then
      RepairOrdinary.frame (RepairOrdinary.frame x ++ RepairOrdinary.frame t) ++
      RepairOrdinary.frame (PCPPNative.descriptor c) else []) j := by
    intro j
    by_cases hj : j = in2
    · subst hj; simp [h1A, hin2]
    · have hj0 : j.val ≠ 0 := fun e => hj (Fin.ext (by rw [e, hin2]))
      have hne : b2 t2 wf.program.tapeCount t4 t5 j ∉ [HS t2 wf.program.tapeCount t4 t5,
          DS t2 wf.program.tapeCount t4 t5, b2 t2 wf.program.tapeCount t4 t5 in2] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨(by dst), (by dst), fun e => hj (b2_inj _ _ _ _ e)⟩
      rw [h1fr.st hne, i0st _ ((by dst)) ((by dst))]
      simp [hj0]
  have h0 : ∀ j, τ1.sh (b2 t2 wf.program.tapeCount t4 t5 j) = 0 := by
    intro j
    by_cases hj : j = in2
    · subst hj; exact h1Ah
    · have hne : b2 t2 wf.program.tapeCount t4 t5 j ∉ [HS t2 wf.program.tapeCount t4 t5,
          DS t2 wf.program.tapeCount t4 t5, b2 t2 wf.program.tapeCount t4 t5 in2] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨(by dst), (by dst), fun e => hj (b2_inj _ _ _ _ e)⟩
      rw [h1fr.sh hne]; rfl
  obtain ⟨τ2, e2, hd2⟩ := Dock.ready_mach cap h2 (b2_inj _ _ _ _) τ1 h0 hin

  have hv2 : ∀ r, τ2.val r = 0 := by intro r; rw [hd2.val, h1fr.val (by simp)]; rfl
  have hs2 : ∀ y, (∀ j, b2 t2 wf.program.tapeCount t4 t5 j ≠ y) → y ≠ HS t2 wf.program.tapeCount t4 t5 →
      y ≠ DS t2 wf.program.tapeCount t4 t5 → τ2.st y = [] ∧ τ2.sh y = 0 := by
    intro y hb h1 h2
    have hy : y ∉ [HS t2 wf.program.tapeCount t4 t5, DS t2 wf.program.tapeCount t4 t5,
        b2 t2 wf.program.tapeCount t4 t5 in2] := by simp [h1, h2, Ne.symm (hb in2)]
    rw [(hd2.other y hb).1, (hd2.other y hb).2, h1fr.st hy, h1fr.sh hy]
    exact ⟨i0st y h1 h2, rfl⟩
  have hfresh2 : ∀ y, y.val < 12 → y.val ≠ 0 → y.val ≠ 1 → τ2.st y = [] ∧ τ2.sh y = 0 := by
    intro y hy h0 h1
    exact hs2 y (fun j e => by have := congrArg Fin.val e; simp only [b2_val] at this; omega)
      (fin_ne (by simp only [HS_val]; omega)) (fin_ne (by simp only [DS_val]; omega))
  -- 3. duplicate the descriptor
  have hDD2 := hfresh2 (DD2 t2 wf.program.tapeCount t4 t5) (by simp) (by simp) (by simp)
  have e3 := Glue.copyFrameW_spec cap (b2 t2 wf.program.tapeCount t4 t5 out2) (DD2 t2 wf.program.tapeCount t4 t5)
    (by dst) rP (natWord q ++ w') [] [] τ2 (by rw [hd2.st, hw]; simp) (by rw [hd2.sh]; rfl) hDD2.1 hDD2.2
    (hv2 rP) (by omega)
  set τ3 := (τ2.sets (DD2 t2 wf.program.tapeCount t4 t5) (RepairOrdinary.frame (natWord q ++ w'))).seth
    (b2 t2 wf.program.tapeCount t4 t5 out2) ([].length + 2 * (natWord q ++ w').length) with hτ3
  have hv3 : ∀ r, τ3.val r = 0 := fun r => by simp [hτ3, hv2 r]
  have hs3 : ∀ y, y.val < 12 → y.val ≠ 0 → y.val ≠ 1 → y.val ≠ 3 → τ3.st y = [] ∧ τ3.sh y = 0 := by
    intro y hy h0 h1 h3
    have hne : y ≠ DD2 t2 wf.program.tapeCount t4 t5 := fin_ne (by simp only [DD2_val]; omega)
    have hne2 : y ≠ b2 t2 wf.program.tapeCount t4 t5 out2 := fin_ne (by simp only [b2_val]; omega)
    simp [hτ3, Function.update_of_ne hne, Function.update_of_ne hne2, hfresh2 y hy h0 h1]
  -- 4. read q
  have hQS := hs3 (QS t2 wf.program.tapeCount t4 t5) (by simp) (by simp) (by simp) (by simp)
  have hregs : [ChecksW.Rw (DescW.Gof descH) 1, ChecksW.Rw (DescW.Gof descH) 2, ChecksW.Rw (DescW.Gof descH) 7, rP2,
      rT, encR 0, rf, rc, rp, rt].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide
  obtain ⟨τ4, e4, h4DD, h4DDh, h4q, h4fr⟩ := Glue.readQW_spec cap (DD2 t2 wf.program.tapeCount t4 t5)
    (QS t2 wf.program.tapeCount t4 t5) (by dst) (ChecksW.Rw (DescW.Gof descH)) hregs q w' τ3
    (by simp [hτ3]) (by simp [hτ3, Function.update_of_ne (show DD2 t2 wf.program.tapeCount t4 t5 ≠
      b2 t2 wf.program.tapeCount t4 t5 out2 by dst), hDD2.2]) hQS.1 hQS.2 (fun r _ => hv3 r)
    (natWord q ++ w').length hqw (by omega)
  -- streams untouched since the entry, after phase 4
  have hs4 : ∀ y, (∀ j, b2 t2 wf.program.tapeCount t4 t5 j ≠ y) → y ≠ HS t2 wf.program.tapeCount t4 t5 →
      y ≠ DS t2 wf.program.tapeCount t4 t5 → y ≠ DD2 t2 wf.program.tapeCount t4 t5 →
      y ≠ QS t2 wf.program.tapeCount t4 t5 → τ4.st y = [] ∧ τ4.sh y = 0 := by
    intro y hb h1 h2 h3 h4
    rw [h4fr.st (by simp [h4]), h4fr.sh (by simp [h4])]
    simp [hτ3, Function.update_of_ne h3, Function.update_of_ne (Ne.symm (hb out2)), hs2 y hb h1 h2]
  have hv4 : ∀ r, r ≠ encR 0 → τ4.val r = 0 := fun r hr => by rw [h4fr.val (by simp [hr])]; exact hv3 r
  have hB0 : Cb * (q + 1) ^ eb = Cb * (τ4.val (encR 0) + 1) ^ eb := by rw [h4q]
  -- 5. B
  have e5 := EncSetup.boundW_spec cap (Q := encR 0) (X := rX) (Y := rY) (Z := rZ) (A2 := rA2) (T := rT)
    (BR := encR 11) (by decide) Cb eb (Cb * (q + 1) ^ eb) τ4 (hv4 _ (by rdst)) (hv4 _ (by rdst)) (hv4 _ (by rdst))
    (hv4 _ (by rdst)) (hv4 _ (by rdst)) (hv4 _ (by rdst)) (by rw [h4q]) (by rw [h4q]; nlinarith)
  rw [h4q] at e5
  set τ5 := τ4.setv (encR 11) (Cb * (q + 1) ^ eb) with hτ5
  -- 6. driver and log
  have hTT4 := hs4 (TT t2 wf.program.tapeCount t4 t5) (fun j => by dst) (by dst) (by dst) (by dst) (by dst)
  have hLG4 := hs4 (LG t2 wf.program.tapeCount t4 t5) (fun j => by dst) (by dst) (by dst) (by dst) (by dst)
  have e6 := EncSetup.fillW_spec cap (TT := TT t2 wf.program.tapeCount t4 t5) (LG := LG t2 wf.program.tapeCount t4 t5)
    (by dst) (BR := encR 11) (C2 := rC2) (CNT := rCNT) (T := rT) (by decide) (Cb * (q + 1) ^ eb) τ5
    (by simp [hτ5, hTT4.1]) (by simp [hτ5, hTT4.2]) (by simp [hτ5, hLG4.1]) (by simp [hτ5, hLG4.2])
    (by simp [hτ5]) (by simp [hτ5, Function.update_of_ne (show rC2 ≠ encR 11 by rdst), hv4 _ (show rC2 ≠ encR 0 by rdst)])
    (by simp [hτ5, Function.update_of_ne (show rCNT ≠ encR 11 by rdst), hv4 _ (show rCNT ≠ encR 0 by rdst)])
    (by simp [hτ5, Function.update_of_ne (show rT ≠ encR 11 by rdst), hv4 _ (show rT ≠ encR 0 by rdst)])
    (by nlinarith)
  set τ6 := (τ5.sets (TT t2 wf.program.tapeCount t4 t5) (List.replicate (Cb * (q + 1) ^ eb) true)).sets
    (LG t2 wf.program.tapeCount t4 t5) (List.replicate (Cb * (q + 1) ^ eb) false) with hτ6
  have hs6 : ∀ y, (∀ j, b2 t2 wf.program.tapeCount t4 t5 j ≠ y) → y ≠ HS t2 wf.program.tapeCount t4 t5 →
      y ≠ DS t2 wf.program.tapeCount t4 t5 → y ≠ DD2 t2 wf.program.tapeCount t4 t5 →
      y ≠ QS t2 wf.program.tapeCount t4 t5 → y ≠ TT t2 wf.program.tapeCount t4 t5 → y ≠ LG t2 wf.program.tapeCount t4 t5 →
      τ6.st y = [] ∧ τ6.sh y = 0 := by
    intro y hb h1 h2 h3 h4 h5 h6
    simp [hτ6, hτ5, Function.update_of_ne h5, Function.update_of_ne h6, hs4 y hb h1 h2 h3 h4]
  have hv6 : ∀ r, r ≠ encR 0 → r ≠ encR 11 → τ6.val r = 0 := by
    intro r h0 h11; simp [hτ6, hτ5, Function.update_of_ne h11, hv4 r h0]
  -- 7. the support matrix
  obtain ⟨τ7, e7, h7mat, h7math, h7L, h7q, h7B, h7enc, h7fr⟩ := encCols_runs (cap := cap) E wf
    (bE t2 wf.program.tapeCount t4 t5) (bE_inj _ _ _ _) (MAT := MAT t2 wf.program.tapeCount t4 t5)
    (TT := TT t2 wf.program.tapeCount t4 t5) (LG := LG t2 wf.program.tapeCount t4 t5)
    (fun j => by dst) (fun j => by dst) (fun j => by dst) (by dst) (by dst) encR (Cb * (q + 1) ^ eb) q hq hBnd hBL
    (by nlinarith) τ6 (by simp [hτ6, Function.update_of_ne (show TT t2 wf.program.tapeCount t4 t5 ≠
      LG t2 wf.program.tapeCount t4 t5 by dst)]) (by simp [hτ6, hτ5, Function.update_of_ne (show
      TT t2 wf.program.tapeCount t4 t5 ≠ LG t2 wf.program.tapeCount t4 t5 by dst), hTT4.2])
    (by simp [hτ6]) (by simp [hτ6, hτ5, hLG4.2])
    (fun j => by
      have := hs6 (bE t2 wf.program.tapeCount t4 t5 j) (fun j' => by dst) (by dst) (by dst) (by dst) (by dst) (by dst)
        (by dst)
      rw [this.1, this.2]; exact ⟨RdEq.refl _, rfl⟩)
    (fun p => by
      rw [(hs6 (MAT t2 wf.program.tapeCount t4 t5) (fun j' => by dst) (by dst) (by dst) (by dst) (by dst) (by dst)
        (by dst)).1]; rfl)
    (hs6 (MAT t2 wf.program.tapeCount t4 t5) (fun j' => by dst) (by dst) (by dst) (by dst) (by dst) (by dst)
        (by dst)).2
    (by simp [hτ6, hτ5, Function.update_of_ne (show encR 0 ≠ encR 11 by rdst), h4q]) (by simp [hτ6, hτ5])
    (fun k h0 h11 => hv6 _ (fun e => h0 (encR.injective e)) (fun e => h11 (encR.injective e)))
  -- streams and registers after phase 7
  have hs7 : ∀ y, (∀ j, b2 t2 wf.program.tapeCount t4 t5 j ≠ y) → (∀ j, bE t2 wf.program.tapeCount t4 t5 j ≠ y) →
      y ≠ HS t2 wf.program.tapeCount t4 t5 → y ≠ DS t2 wf.program.tapeCount t4 t5 → y ≠ DD2 t2 wf.program.tapeCount t4 t5 →
      y ≠ QS t2 wf.program.tapeCount t4 t5 → y ≠ TT t2 wf.program.tapeCount t4 t5 → y ≠ LG t2 wf.program.tapeCount t4 t5 →
      y ≠ MAT t2 wf.program.tapeCount t4 t5 → τ7.st y = [] ∧ τ7.sh y = 0 := by
    intro y hb he h1 h2 h3 h4 h5 h6 h7
    have hy : y ∉ List.ofFn (bE t2 wf.program.tapeCount t4 t5) ++ [MAT t2 wf.program.tapeCount t4 t5] := by
      simp only [List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists]
      exact ⟨fun j => he j, h7⟩
    rw [h7fr.st hy, h7fr.sh hy]
    exact hs6 y hb h1 h2 h3 h4 h5 h6
  have hv7 : ∀ r, (∀ k, encR k ≠ r) → r ≠ encR 0 → r ≠ encR 11 → τ7.val r = 0 := by
    intro r hr h0 h11
    rw [h7fr.val (by simp only [List.mem_ofFn, not_exists]; exact hr)]
    exact hv6 r h0 h11
  have hfr7 : ∀ y, (∀ j, b2 t2 wf.program.tapeCount t4 t5 j ≠ y) → (∀ j, bE t2 wf.program.tapeCount t4 t5 j ≠ y) →
      y.val ≥ 7 → τ7.st y = [] ∧ τ7.sh y = 0 := by
    intro y hb he hy
    exact hs7 y hb he (fin_ne (by simp only [HS_val]; omega)) (fin_ne (by simp only [DS_val]; omega))
      (fin_ne (by simp only [DD2_val]; omega)) (fin_ne (by simp only [QS_val]; omega))
      (fin_ne (by simp only [TT_val]; omega)) (fin_ne (by simp only [LG_val]; omega))
      (fin_ne (by simp only [MAT_val]; omega))
  have hvR : ∀ r : Fin 64, r.val ≥ 14 → τ7.val r = 0 := by
    intro r hr
    exact hv7 r (fun k e => by have := congrArg Fin.val e; simp only [encR_val] at this; omega)
      (fin_ne (by simp only [encR_val]; omega)) (fin_ne (by simp only [encR_val]; omega))
  have hDD2_7 : τ7.st (DD2 t2 wf.program.tapeCount t4 t5) = RepairOrdinary.frame (natWord q ++ w') ∧
      τ7.sh (DD2 t2 wf.program.tapeCount t4 t5) = 0 := by
    have hy : DD2 t2 wf.program.tapeCount t4 t5 ∉ List.ofFn (bE t2 wf.program.tapeCount t4 t5) ++
        [MAT t2 wf.program.tapeCount t4 t5] := by
      simp only [List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists]
      exact ⟨fun j => by dst, by dst⟩
    rw [h7fr.st hy, h7fr.sh hy]
    simp only [hτ6, hτ5, WState.sets_st, WState.setv_st, WState.sets_sh, WState.setv_sh,
      Function.update_of_ne (show DD2 t2 wf.program.tapeCount t4 t5 ≠ LG t2 wf.program.tapeCount t4 t5 by dst),
      Function.update_of_ne (show DD2 t2 wf.program.tapeCount t4 t5 ≠ TT t2 wf.program.tapeCount t4 t5 by dst), h4DD,
      h4DDh]
    simp [hτ3]
  refine ⟨τ7, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.seq e5 (WXExec.seq e6 e7)))))) ?_, hDD2_7.1, hDD2_7.2, h7mat, h7math, h7L,
    ⟨hfr7 _ (fun j => by dst) (fun j => by dst) (by simp), hfr7 _ (fun j => by dst) (fun j => by dst) (by simp),
      hfr7 _ (fun j => by dst) (fun j => by dst) (by simp), hfr7 _ (fun j => by dst) (fun j => by dst) (by simp),
      hfr7 _ (fun j => by dst) (fun j => by dst) (by simp),
      fun j => hfr7 _ (fun j' => by dst) (fun j' => by dst) (by simp only [b4_val]; omega),
      fun j => hfr7 _ (fun j' => by dst) (fun j' => by dst) (by simp only [b5_val]; omega),
      fun i hi => hvR _ (by simp only [descH_val]; have : i.val ≠ 16 := fun e => hi (Fin.ext e); simp [this]),
      fun i => hvR _ (by simp only [supG_val]; omega),
      ⟨hvR _ (by simp), hvR _ (by simp), hvR _ (by simp), hvR _ (by simp)⟩⟩⟩
  unfold costA
  omega

end RunA

end NearCubicGates.Close.CheckedPCPP.Comp
