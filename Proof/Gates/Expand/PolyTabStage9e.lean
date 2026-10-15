import Proof.Gates.Expand.PolyTabStage9d

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

section MSSteps
variable {Wb Wc : ℕ} {inp VT : List Bool} {σA : WState (NSx te qa) NRk} {hd : ℕ} {o46 o56 oV L5 : List Bool}
  {f : Fin 64 → ℕ} {q2 q3 : (Fin 10 → ℕ) → Prop}

theorem MS.sets6 {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (l : List Bool)
    (hl : l.length ≤ 2 * Wb + 1) : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 (τ.sets (sS 6) l) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hS : SameExcept τ (τ.sets (sS 6) l) [sS 6] [] := sameExcept_sets τ (List.mem_singleton_self _) l
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 71 → X ∉ [sS 6] := fun X hX => nm1 (fun e => hX (by rw [e]; simp))
  exact ⟨⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega)) (fun j => by simp), hv8, hv9, hq2⟩,
    ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega)) (fun j => by simp), hw8, hw9, hq3⟩,
    out_tr h46 hS (nO _ (by simp)) (by simp), out_tr h56 hS (nO _ (by simp)) (by simp),
    out_tr h5 hS (nO _ (by simp)) (by simp), by rw [hS.st (nO _ (by simp))]; exact hvt,
    by rw [hS.sh (nO _ (by simp))]; exact hvth, by simp [h6h], by simpa using hl, x_tr hx hS (fun _ _ => by simp),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_s6) (by simp)⟩

theorem MS.sets3 {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (z : ℕ) :
    MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 (fun v => v 1 = z) (τ.sets (U3 1) (frame (binary Wc z))) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hS : SameExcept τ (τ.sets (U3 1) (frame (binary Wc z))) [U3 1] [] :=
    sameExcept_sets τ (List.mem_singleton_self _) _
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 95 → X ∉ [U3 (te := te) (qa := qa) 1] := fun X hX =>
    nm1 (fun e => hX (by rw [e, U3_val]; simp))
  exact ⟨⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega)) (fun j => by simp), hv8, hv9, hq2⟩,
    ⟨Function.update w 1 z, hw.sets 1 (by decide) z, by simp [hw8], by simp [hw9], by simp⟩,
    out_tr h46 hS (nO _ (by simp)) (by simp), out_tr h56 hS (nO _ (by simp)) (by simp),
    out_tr h5 hS (nO _ (by simp)) (by simp), by rw [hS.st (nO _ (by simp))]; exact hvt,
    by rw [hS.sh (nO _ (by simp))]; exact hvth, by rw [hS.sh (nO _ (by simp))]; exact h6h,
    by rw [hS.st (nO _ (by simp))]; exact h6l, x_tr hx hS (fun _ _ => by simp),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact U3_MSS 1) (by simp)⟩

theorem MS.sets2 {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (z : ℕ) :
    MS Wb Wc inp VT σA hd o46 o56 oV L5 f (fun v => v 1 = z) q3 (τ.sets (U2 1) (frame (binary Wb z))) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have hS : SameExcept τ (τ.sets (U2 1) (frame (binary Wb z))) [U2 1] [] :=
    sameExcept_sets τ (List.mem_singleton_self _) _
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 86 → X ∉ [U2 (te := te) (qa := qa) 1] := fun X hX =>
    nm1 (fun e => hX (by rw [e, U2_val]; simp))
  exact ⟨⟨Function.update v 1 z, hv.sets 1 (by decide) z, by simp [hv8], by simp [hv9], by simp⟩,
    ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega)) (fun j => by simp), hw8, hw9, hq3⟩,
    out_tr h46 hS (nO _ (by simp)) (by simp), out_tr h56 hS (nO _ (by simp)) (by simp),
    out_tr h5 hS (nO _ (by simp)) (by simp), by rw [hS.st (nO _ (by simp))]; exact hvt,
    by rw [hS.sh (nO _ (by simp))]; exact hvth, by rw [hS.sh (nO _ (by simp))]; exact h6h,
    by rw [hS.st (nO _ (by simp))]; exact h6l, x_tr hx hS (fun _ _ => by simp),
    se_ext hfr hS (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact U2_MSS 1) (by simp)⟩

/-- Fetch record `n = rX 31` of the closed variable list into `sS 6`. -/
theorem ms_getAt (cap : ℕ) (hW : 1 ≤ Wb) (xs : List ℕ) (junk : List Bool) (n : ℕ) (hn : n < xs.length) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 [] (recStream (xs.map (binary Wb)) ++ junk) f q2 q3 τ)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h9 : f 9 = 0) (h31 : f 31 = n)
    (hcap : (xs.length + 1) * (2 * Wb + 1) + 2 * n ≤ cap) :
    Runs cap (getAt (sS 5) (sS 6) (rX 0) (rX 1) (rX 31) (rX 9)) τ
      ((n + 1) * (40 * Wb + 40) + 10 * (n + 1) * (2 * Wb + 1) + 10)
      (fun ρ => MS Wb Wc inp VT σA hd o46 o56 [] (recStream (xs.map (binary Wb)) ++ junk) f q2 q3 ρ ∧
        NumOn ρ (sS 6) Wb xs[n]) := by
  have e := getAt_spec cap (A := sS 5) (Wk := sS 6) (CA := rX 0) (CW := rX 1) (N := rX 31) (K2 := rX 9) (by polyTabNe)
    (by polyTabNe) Wb hW xs n hn τ junk (by rw [h.vs.1]; simp [overlay]) (by rw [h.vs.2.1]; rfl)
    (by rw [h.x 0 (by decide), h0]) h.w6h h.w6l (by rw [h.x 1 (by decide), h1]) (by rw [h.x 31 (by decide), h31])
    (by rw [h.x 9 (by decide), h9]) hcap
  exact ⟨_, e, h.sets6 _ (by rw [frame_length, binary_length]), by simp, by simp [h.w6h]⟩

/-- `rX j += sS 6`, `sS 6 := 0`. -/
theorem ms_toReg6 (cap : ℕ) (x : ℕ) (j : Fin 64) (hj : XR j) (hj3 : j.val ∉ [3, 4, 6]) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (h6 : NumOn τ (sS 6) Wb x)
    (h3 : f 3 = 0) (h4 : f 4 = 0) (h6' : f 6 = 0) (hx : x < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) (hcapR : f j + x < cap) :
    Runs cap (toReg (sS 6) (U2 8) (U2 9) (rX j) (rX 3) (rX 4) (rX 6)) τ (x * (83 * Wb + 30) + 41 * Wb + 14)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j (f j + x)) q2 q3) := by
  have hj' := hj3; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
  obtain ⟨v, hv, hv8, hv9, -⟩ := h.e2
  have hN8 := hv.num 8 (by decide); have hN9 := hv.num 9 (by decide)
  rw [hv8] at hN8; rw [hv9] at hN9
  have hR : [rX j, rX 3, rX 4, rX 6].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨rX_ne (fun e => hj'.1 (by rw [e]; rfl)), rX_ne (fun e => hj'.2.1 (by rw [e]; rfl)),
      rX_ne (fun e => hj'.2.2 (by rw [e]; rfl))⟩, ⟨by polyTabNe, by polyTabNe⟩, by polyTabNe, not_false⟩
  have hS3 : [sS (te := te) (qa := qa) 6, U2 8, U2 9].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨(U2_ne 8 _ (by simp)).symm, (U2_ne 9 _ (by simp)).symm⟩, U2_ne_U2 8 9 (by decide), not_false⟩
  have e := toReg_spec cap Wb (X := sS 6) (ONE := U2 8) (Z := U2 9) (R := rX j) (NZ := rX 3) (F := rX 4) (Rr := rX 6)
    hS3 hR τ x 0 (f j) h6 hN8 hN9 (h.x j hj) (by rw [h.x 3 (by decide), h3]) (by rw [h.x 4 (by decide), h4])
    (by rw [h.x 6 (by decide), h6']) hx hcap hcapR
  exact ⟨_, e, (h.sets6 _ (by rw [frame_length, binary_length])).setv j hj _⟩

/-- Copy `K` records of the occurrence table, from `c0 = rX 30`, to `sZ 46` (`rX 30 := c0 + K`). -/
theorem ms_copyN (cap : ℕ) (hW : 1 ≤ Wb) (ys : List ℕ) (c0 K : ℕ) (hK : c0 + K ≤ ys.length) (τ : WSt)
    (h : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd o46 o56 oV L5 f q2 q3 τ)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h9 : f 9 = 0) (h29 : f 29 = 0) (h28 : f 28 = 0) (h30 : f 30 = c0) (h27 : f 27 = K)
    (hcap : (ys.length + 1) * (2 * Wb + 1) + 2 * ys.length ≤ cap) (hcapO : o46.length + K * (2 * Wb + 1) + 1 ≤ cap) :
    Runs cap (copyN (sS 4) (sS 6) (sZ 46) (rX 0) (rX 1) (rX 30) (rX 9) (rX 29) (rX 37) (rX 27) (rX 28)) τ
      (K * (copyStep Wb ys.length + 8) + 7 * K + 3)
      (MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd (o46 ++ segRecs Wb ys c0 K) o56 oV L5
        (Function.update f 30 (c0 + K)) q2 q3) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  refine (copyN_spec cap (A := sS 4) (Wk := sS 6) (O := sZ 46) (CA := rX 0) (CW := rX 1) (CUR := rX 30) (K2 := rX 9)
    (CS := rX 29) (CO := rX 37) (KC := rX 27) (KC2 := rX 28) (by polyTabNe) (by polyTabNe) Wb hW ys c0 K hK τ []
    o46 [] (by rw [hvt, List.append_nil]) hvth (by rw [hx 0 (by decide), h0]) (by rw [hx 1 (by decide), h1])
    (by rw [hx 9 (by decide), h9]) (by rw [hx 29 (by decide), h29]) h6h h6l (by rw [hx 30 (by decide), h30])
    (by rw [hx 27 (by decide), h27]) (by rw [hx 28 (by decide), h28]) (by simpa using h46) hcap
    (by simpa using hcapO)).post fun ρ ⟨ho, hcur, hwh, hwl, _, _, hS⟩ => ?_
  have nO : ∀ X : Fin (NSx te qa + 1), X.val ≠ 71 → X.val ≠ 47 → X ∉ [sS 6, sZ 46] := fun X h1 h2 hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e <;> (rw [e] at h1 h2; simp at h1 h2)
  have nR : ∀ k : Fin 64, k.val ≠ 30 → k.val ≠ 37 → rX k ∉ [rX 30, rX 37] := fun k h1 h2 hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e <;> (have := rX.injective e; subst this; simp at h1 h2)
  have nRB : ∀ j : Fin 12, RB j ∉ [rX 30, rX 37] := fun j hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e <;> exact RB_ne j _ (by decide) e
  refine ⟨⟨v, evv_tr hv hS (fun i => nO _ (by rw [U2_val]; split_ifs <;> omega) (by rw [U2_val]; split_ifs <;> omega))
    nRB, hv8, hv9, hq2⟩, ⟨w, evv_tr hw hS (fun i => nO _ (by rw [U3_val]; split_ifs <;> omega)
    (by rw [U3_val]; split_ifs <;> omega)) nRB, hw8, hw9, hq3⟩, by simpa using ho,
    out_tr h56 hS (nO _ (by simp) (by simp)) (nR 38 (by decide) (by decide)),
    out_tr h5 hS (nO _ (by simp) (by simp)) (nR 34 (by decide) (by decide)),
    by rw [hS.st (nO _ (by simp) (by simp))]; exact hvt, by rw [hS.sh (nO _ (by simp) (by simp))]; exact hvth,
    hwh, hwl, fun k hk => ?_, se_ext hfr hS (fun X hX => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact mss_s6
      · exact mss_z46) (by simp [rX_mem])⟩
  by_cases e : k = 30
  · subst e; simp [hcur]
  · have hk' := hk; unfold XR at hk'; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk'
    rw [hS.val (nR k (fun h => e (Fin.ext h)) hk'.2.2.1), Function.update_of_ne e]; exact hx k hk

def enc3 : WX :=
  .seq (BinW.shl (U3 1) (U3 9) (RB 2) (RB 3)) <|
  .seq (.ifr (rX 5) (BinW.inc (U3 1) (U3 9) (RB 2) (RB 3)) WMX.skip) (.wm (WM.clear (rX 5)))

theorem ms_enc3 (cap : ℕ) (y sg : ℕ) (hsg : sg ≤ 1) (hyW : 2 * y + 1 < 2 ^ Wc) (τ : WSt)
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 (fun v => v 1 = y) τ) (h5 : f 5 = sg) (hcap : 2 * Wc + 1 ≤ cap) :
    Runs cap enc3 τ (41 * Wc + 8 + 1 + (41 * Wc + 7 + 1 + 1 + (3 * 1 + 1)))
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f 5 0) q2 (fun v => v 1 = 2 * y + sg)) := by
  obtain ⟨w, hw, hw8, hw9, hq3⟩ := h.e3
  have hN1 := hw.num 1 (by decide); have hN9 := hw.num 9 (by decide)
  rw [hq3] at hN1; rw [hw9] at hN9
  have hRB2 := hw.zero 2 (by decide) (by decide)
  have hRB3 := hw.zero 3 (by decide) (by decide)
  have nRB : (RB 2 : Fin NRk) ≠ RB 3 := fun e => absurd (RB.injective e) (by decide)
  have e1 := BinW.shl_spec cap Wc (A := U3 1) (B := U3 9) (F := RB 2) (R := RB 3) (U3_ne_U3 1 9 (by decide)) nRB τ y 0
    hN1 hN9 hRB2 hRB3 hcap
  have h1 := h.sets3 (2 * y)
  have e2 : Runs cap (.ifr (rX 5) (BinW.inc (U3 1) (U3 9) (RB 2) (RB 3)) WMX.skip)
      (τ.sets (U3 1) (frame (binary Wc (2 * y)))) (41 * Wc + 7 + 1)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 (fun v => v 1 = 2 * y + sg)) := by
    have h5' : (τ.sets (U3 1) (frame (binary Wc (2 * y)))).val (rX 5) = sg := by rw [h1.x 5 (by decide), h5]
    refine Runs.ifr (fun hT => ?_) (fun hF => ?_)
    · have hs1 : sg = 1 := by omega
      obtain ⟨w', hw', hw8', hw9', hq3'⟩ := h1.e3
      have hN1' := hw'.num 1 (by decide); have hN9' := hw'.num 9 (by decide)
      rw [hq3'] at hN1'; rw [hw9'] at hN9'
      have e := BinW.inc_spec cap Wc (A := U3 1) (B := U3 9) (F := RB 2) (R := RB 3) (U3_ne_U3 1 9 (by decide)) nRB _
        (2 * y) 0 hN1' hN9' (hw'.zero 2 (by decide) (by decide)) (hw'.zero 3 (by decide) (by decide)) (by omega) hcap
      refine ⟨_, WXExec.mono e le_rfl, ?_⟩
      have := h1.sets3 (2 * y + 1)
      rw [hs1]; exact this
    · have hs0 : sg = 0 := by omega
      refine ⟨_, WXExec.mono (WXExec.skip (cap := cap) _) (Nat.zero_le _), ?_⟩
      rw [hs0, Nat.add_zero]; exact h1
  refine Runs.seqE e1 (Runs.seq e2 fun τ2 h2 => ?_)
  exact (ms_clr cap h2 5 (by decide) (by omega)).cost (by rw [h5]; omega)

end MSSteps

end NearCubicGates.Close.Expand.PolyTab
