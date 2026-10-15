import Proof.Gates.Expand.PolyTabStage9c

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.RepairRepresentation (natWord)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

theorem se_out (σ : WState (NSx te qa) NRk) (O : Fin (NSx te qa + 1)) (CO : Fin NRk) (l : List Bool) (n m : ℕ) :
    SameExcept σ (((σ.sets O l).seth O n).setv CO m) [O] [CO] :=
  ((sameExcept_sets σ (List.mem_singleton_self O) l).trans (sameExcept_seth _ (List.mem_singleton_self O) n)).trans
    (sameExcept_setv _ (List.mem_singleton_self CO) m)

theorem nm1 {α : Type} {x y : α} (h : x ≠ y) : x ∉ [y] := by simpa using h

theorem rb_nm (j : Fin 12) (k : Fin 64) (hk : k.val < 52) : RB j ∉ [rX k] := nm1 (RB_ne j k hk)

theorem xr_nm (k : Fin 64) (j : Fin 64) (hj : XR j) (hk : j ≠ k) : rX j ∉ [rX k] := nm1 (rX_ne hk)

section MSSteps
variable {Wb Wc : ℕ} {inp VT : List Bool} {σA : WState (NSx te qa) NRk} {o46 o56 oV L5 : List Bool}
  {f : Fin 64 → ℕ}

theorem ms_read2 (cap : ℕ) (hW : 1 ≤ Wb) (hd : ℕ) (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true (natWord x) ++ rest)
    (hhd : hd = pre.length) (hcap : natBitLength x + 1 ≤ cap) (hcapW : 2 * Wb + 1 ≤ cap) :
    Runs cap (readBin U2 RB 1 2) τ (readBinCost Wb (natBitLength x))
      (MS Wb Wc inp VT σA (pre.length + 2 * (natWord x).length) o46 o56 oV L5 f (fun v => v 1 = x % 2 ^ Wb) q3) := by
  obtain ⟨⟨v, hv, hv8, hv9, -⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  refine (readBinV cap 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (Post.refl hv) hv8 hW x pre rest
    hinp hhd hcap hcapW).post fun ρ ⟨hρ, hS⟩ => ?_
  refine ⟨⟨_, hρ, by simp [hv8], by simp [hv9], by simp⟩, ⟨w, evv_move hw (fun i hi => ⟨hS.st (nevS2_U3 i hi),
    hS.sh (nevS2_U3 i hi)⟩) ?_ ?_ ?_, hw8, hw9, hq3⟩, out_tr h46 hS (nevS2 _ (by simp)) (nevR 37 (by decide)),
    out_tr h56 hS (nevS2 _ (by simp)) (nevR 38 (by decide)), out_tr h5 hS (nevS2 _ (by simp)) (nevR 34 (by decide)),
    by rw [hS.st (nevS2 _ (by simp))]; exact hvt, by rw [hS.sh (nevS2 _ (by simp))]; exact hvth,
    by rw [hS.sh (nevS2 _ (by simp))]; exact h6h, by rw [hS.st (nevS2 _ (by simp))]; exact h6l,
    x_tr hx hS xr_evR, se_ext hfr hS evS2_MSS evR_RXL⟩
  · have := hρ.inp; rw [UB_zero] at this; rw [UB2_zero]; exact this
  · have := hρ.hd; rw [UB_zero] at this; rw [UB2_zero]; exact this
  · intro j h11
    by_cases h1 : j = 1
    · subst h1; exact hρ.r1
    · exact hρ.zero j h1 h11

theorem ms_read3 (cap : ℕ) (hW : 1 ≤ Wc) (hd : ℕ) (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true (natWord x) ++ rest)
    (hhd : hd = pre.length) (hcap : natBitLength x + 1 ≤ cap) (hcapW : 2 * Wc + 1 ≤ cap) :
    Runs cap (readBin U3 RB 1 2) τ (readBinCost Wc (natBitLength x))
      (MS Wb Wc inp VT σA (pre.length + 2 * (natWord x).length) o46 o56 oV L5 f q2 (fun v => v 1 = x % 2 ^ Wc)) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, -⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  refine (readBinV cap 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (Post.refl hw) hw8 hW x pre rest
    hinp hhd hcap hcapW).post fun ρ ⟨hρ, hS⟩ => ?_
  refine ⟨⟨v, evv_move hv (fun i hi => ⟨hS.st (nevS3_U2 i hi), hS.sh (nevS3_U2 i hi)⟩) ?_ ?_ ?_, hv8, hv9, hq2⟩,
    ⟨_, hρ, by simp [hw8], by simp [hw9], by simp⟩, out_tr h46 hS (nevS3 _ (by simp)) (nevR 37 (by decide)),
    out_tr h56 hS (nevS3 _ (by simp)) (nevR 38 (by decide)), out_tr h5 hS (nevS3 _ (by simp)) (nevR 34 (by decide)),
    by rw [hS.st (nevS3 _ (by simp))]; exact hvt, by rw [hS.sh (nevS3 _ (by simp))]; exact hvth,
    by rw [hS.sh (nevS3 _ (by simp))]; exact h6h, by rw [hS.st (nevS3 _ (by simp))]; exact h6l,
    x_tr hx hS xr_evR, se_ext hfr hS evS3_MSS evR_RXL⟩
  · have := hρ.inp; rw [UB2_zero] at this; rw [UB_zero]; exact this
  · have := hρ.hd; rw [UB2_zero] at this; rw [UB_zero]; exact this
  · intro j h11
    by_cases h1 : j = 1
    · subst h1; exact hρ.r1
    · exact hρ.zero j h1 h11

theorem ms_app46 (cap : ℕ) (hd : ℕ) (q3 : (Fin 10 → ℕ) → Prop) (y : ℕ) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f (fun v => v 1 = y) q3 τ) (h29 : f 29 = 0)
    (hcap : o46.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (appendRecX (U2 1) (sZ 46) (rX 29) (rX 37)) τ (40 * Wb + 11)
      (MS Wb Wc inp VT σA hd (o46 ++ frame (binary Wb y)) o56 oV L5 f (fun v => v 1 = y) q3) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hN := hv.num 1 (by decide)
  rw [hq2] at hN
  have e := appendRec_spec cap (Src := U2 1) (O := sZ 46) (CS := rX 29) (CO := rX 37) (U2_ne 1 _ (by simp))
    (by polyTabNe) τ (binary Wb y) [] o46 [] (by rw [hN.1, frame_eq_frameP]) hN.2 (by rw [hx 29 (by decide), h29]) h46
    (by rw [binary_length]; omega)
  rw [binary_length] at e
  have hS := se_out τ (sZ 46) (rX 37) (overlay (o46 ++ frame (binary Wb y)) []) (o46 ++ frame (binary Wb y)).length
    (o46 ++ frame (binary Wb y)).length
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 47 → X ∉ [sZ 46] := fun X hX => nm1 (fun e => hX (by rw [e]; simp))
  refine ⟨_, WXExec.wm e, ⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega)) (fun j => rb_nm j 37
    (by decide)), hv8, hv9, hq2⟩, ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega))
    (fun j => rb_nm j 37 (by decide)), hw8, hw9, hq3⟩, appendRec_out τ _ _ _ _ _,
    out_tr h56 hS (nO _ (by simp)) (nm1 (by polyTabNe)), out_tr h5 hS (nO _ (by simp)) (nm1 (by polyTabNe)),
    by rw [hS.st (nO _ (by simp))]; exact hvt, by rw [hS.sh (nO _ (by simp))]; exact hvth,
    by rw [hS.sh (nO _ (by simp))]; exact h6h, by rw [hS.st (nO _ (by simp))]; exact h6l,
    x_tr hx hS (fun j hj => xr_nm 37 j hj (fun e => by subst e; revert hj; decide)),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_z46) (by simp [rX_mem])⟩

theorem ms_appV (cap : ℕ) (hd : ℕ) (q3 : (Fin 10 → ℕ) → Prop) (y : ℕ) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f (fun v => v 1 = y) q3 τ) (h29 : f 29 = 0)
    (hcap : oV.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (appendRecX (U2 1) (sS 5) (rX 29) (rX 34)) τ (40 * Wb + 11)
      (MS Wb Wc inp VT σA hd o46 o56 (oV ++ frame (binary Wb y)) L5 f (fun v => v 1 = y) q3) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hN := hv.num 1 (by decide)
  rw [hq2] at hN
  have e := appendRec_spec cap (Src := U2 1) (O := sS 5) (CS := rX 29) (CO := rX 34) (U2_ne 1 _ (by simp))
    (by polyTabNe) τ (binary Wb y) [] oV L5 (by rw [hN.1, frame_eq_frameP]) hN.2 (by rw [hx 29 (by decide), h29]) h5
    (by rw [binary_length]; omega)
  rw [binary_length] at e
  have hS := se_out τ (sS 5) (rX 34) (overlay (oV ++ frame (binary Wb y)) L5) (oV ++ frame (binary Wb y)).length
    (oV ++ frame (binary Wb y)).length
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 70 → X ∉ [sS 5] := fun X hX => nm1 (fun e => hX (by rw [e]; simp))
  refine ⟨_, WXExec.wm e, ⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega)) (fun j => rb_nm j 34
    (by decide)), hv8, hv9, hq2⟩, ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega))
    (fun j => rb_nm j 34 (by decide)), hw8, hw9, hq3⟩, out_tr h46 hS (nO _ (by simp)) (nm1 (by polyTabNe)),
    out_tr h56 hS (nO _ (by simp)) (nm1 (by polyTabNe)), appendRec_out τ _ _ _ _ _,
    by rw [hS.st (nO _ (by simp))]; exact hvt, by rw [hS.sh (nO _ (by simp))]; exact hvth,
    by rw [hS.sh (nO _ (by simp))]; exact h6h, by rw [hS.st (nO _ (by simp))]; exact h6l,
    x_tr hx hS (fun j hj => xr_nm 34 j hj (fun e => by subst e; revert hj; decide)),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_s5) (by simp [rX_mem])⟩

theorem ms_app56 (cap : ℕ) (hd : ℕ) (q2 : (Fin 10 → ℕ) → Prop) (y : ℕ) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 (fun v => v 1 = y) τ) (h29 : f 29 = 0)
    (hcap : o56.length + 2 * Wc + 2 ≤ cap) :
    Runs cap (appendRecX (U3 1) (sZ 56) (rX 29) (rX 38)) τ (40 * Wc + 11)
      (MS Wb Wc inp VT σA hd o46 (o56 ++ frame (binary Wc y)) oV L5 f q2 (fun v => v 1 = y)) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hN := hw.num 1 (by decide)
  rw [hq3] at hN
  have e := appendRec_spec cap (Src := U3 1) (O := sZ 56) (CS := rX 29) (CO := rX 38) (U3_ne 1 _ (by simp))
    (by polyTabNe) τ (binary Wc y) [] o56 [] (by rw [hN.1, frame_eq_frameP]) hN.2 (by rw [hx 29 (by decide), h29]) h56
    (by rw [binary_length]; omega)
  rw [binary_length] at e
  have hS := se_out τ (sZ 56) (rX 38) (overlay (o56 ++ frame (binary Wc y)) []) (o56 ++ frame (binary Wc y)).length
    (o56 ++ frame (binary Wc y)).length
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 57 → X ∉ [sZ 56] := fun X hX => nm1 (fun e => hX (by rw [e]; simp))
  refine ⟨_, WXExec.wm e, ⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega)) (fun j => rb_nm j 38
    (by decide)), hv8, hv9, hq2⟩, ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega))
    (fun j => rb_nm j 38 (by decide)), hw8, hw9, hq3⟩, out_tr h46 hS (nO _ (by simp)) (nm1 (by polyTabNe)),
    appendRec_out τ _ _ _ _ _, out_tr h5 hS (nO _ (by simp)) (nm1 (by polyTabNe)),
    by rw [hS.st (nO _ (by simp))]; exact hvt, by rw [hS.sh (nO _ (by simp))]; exact hvth,
    by rw [hS.sh (nO _ (by simp))]; exact h6h, by rw [hS.st (nO _ (by simp))]; exact h6l,
    x_tr hx hS (fun j hj => xr_nm 38 j hj (fun e => by subst e; revert hj; decide)),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_z56) (by simp [rX_mem])⟩

theorem ms_closeV (cap : ℕ) (hd : ℕ) (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (hcap : oV.length ≤ cap) :
    Runs cap (closeOutX (sS 5) (rX 34)) τ (5 * oV.length + 3)
      (MS Wb Wc inp VT σA hd o46 o56 [] (overlay (oV ++ [false]) L5) f q2 q3) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have e := closeOut_spec cap τ oV L5 h5 hcap
  have hS := se_out τ (sS 5) (rX 34) (overlay (oV ++ [false]) L5) 0 0
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 70 → X ∉ [sS 5] := fun X hX => nm1 (fun e => hX (by rw [e]; simp))
  refine ⟨_, WXExec.wm e, ⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega)) (fun j => rb_nm j 34
    (by decide)), hv8, hv9, hq2⟩, ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega))
    (fun j => rb_nm j 34 (by decide)), hw8, hw9, hq3⟩, out_tr h46 hS (nO _ (by simp)) (nm1 (by polyTabNe)),
    out_tr h56 hS (nO _ (by simp)) (nm1 (by polyTabNe)), ⟨by simp [overlay], by simp, by simp⟩,
    by rw [hS.st (nO _ (by simp))]; exact hvt, by rw [hS.sh (nO _ (by simp))]; exact hvth,
    by rw [hS.sh (nO _ (by simp))]; exact h6h, by rw [hS.st (nO _ (by simp))]; exact h6l,
    x_tr hx hS (fun j hj => xr_nm 34 j hj (fun e => by subst e; revert hj; decide)),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_s5) (by simp [rX_mem])⟩

theorem ms_toReg2 (cap : ℕ) (hd : ℕ) (q3 : (Fin 10 → ℕ) → Prop) (y : ℕ) (j : Fin 64) (hj : XR j)
    (hj3 : j.val ∉ [3, 4, 6]) (τ : WSt) (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f (fun v => v 1 = y) q3 τ)
    (h3 : f 3 = 0) (h4 : f 4 = 0) (h6 : f 6 = 0) (hy : y < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) (hcapR : f j + y < cap) :
    Runs cap (toReg (U2 1) (U2 8) (U2 9) (rX j) (rX 3) (rX 4) (rX 6)) τ (y * (83 * Wb + 30) + 41 * Wb + 14)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j (f j + y)) (fun v => v 1 = 0) q3) := by
  have hj' := hj3; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hN1 := hv.num 1 (by decide); have hN8 := hv.num 8 (by decide); have hN9 := hv.num 9 (by decide)
  rw [hq2] at hN1; rw [hv8] at hN8; rw [hv9] at hN9
  have hR : [rX j, rX 3, rX 4, rX 6].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨rX_ne (fun e => hj'.1 (by rw [e]; rfl)), rX_ne (fun e => hj'.2.1 (by rw [e]; rfl)),
      rX_ne (fun e => hj'.2.2 (by rw [e]; rfl))⟩, ⟨by polyTabNe, by polyTabNe⟩, by polyTabNe, not_false⟩
  have e := toReg_spec cap Wb (X := U2 1) (ONE := U2 8) (Z := U2 9) (R := rX j) (NZ := rX 3) (F := rX 4) (Rr := rX 6)
    (by simp) hR τ y 0 (f j) hN1 hN8 hN9 (hx j hj) (by rw [hx 3 (by decide), h3]) (by rw [hx 4 (by decide), h4])
    (by rw [hx 6 (by decide), h6]) hy hcap hcapR
  have hS : SameExcept τ ((τ.sets (U2 1) (frame (binary Wb 0))).setv (rX j) (f j + y)) [U2 1] [rX j] :=
    (sameExcept_sets τ (List.mem_singleton_self _) _).trans (sameExcept_setv _ (List.mem_singleton_self _) _)
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 86 → X ∉ [U2 (te := te) (qa := qa) 1] := fun X hX =>
    nm1 (fun e => hX (by rw [e, U2_val]; simp))
  refine ⟨_, e, ⟨Function.update v 1 0, evv_tr (hv.sets 1 (by decide) 0) (sameExcept_setv (S := []) _
    (List.mem_singleton_self (rX j)) _) (fun _ => by simp) (fun k => rb_nm k j hj.1), by simp [hv8], by simp [hv9],
    by simp⟩, ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega)) (fun k => rb_nm k j hj.1), hw8,
    hw9, hq3⟩, out_tr h46 hS (nO _ (by simp)) (nm1 (rX_ne (fun e => by rw [← e] at hj; revert hj; decide)) : rX 37 ∉ [rX j]),
    out_tr h56 hS (nO _ (by simp)) (nm1 (rX_ne (fun e => by rw [← e] at hj; revert hj; decide)) : rX 38 ∉ [rX j]),
    out_tr h5 hS (nO _ (by simp)) (nm1 (rX_ne (fun e => by rw [← e] at hj; revert hj; decide)) : rX 34 ∉ [rX j]),
    by rw [hS.st (nO _ (by simp))]; exact hvt, by rw [hS.sh (nO _ (by simp))]; exact hvth,
    by rw [hS.sh (nO _ (by simp))]; exact h6h, by rw [hS.st (nO _ (by simp))]; exact h6l, fun k hk => ?_,
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact U2_MSS 1) (by simp [rX_mem])⟩
  by_cases e : k = j
  · subst e; simp
  · rw [hS.val (xr_nm j k hk e), Function.update_of_ne e]; exact hx k hk

end MSSteps

end NearCubicGates.Close.Expand.PolyTab
