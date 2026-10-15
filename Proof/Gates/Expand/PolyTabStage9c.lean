import Proof.Gates.Expand.PolyTabStage9b

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

theorem sS2_ne (i : Fin 9) : sS (te := te) (qa := qa) 2 ≠ ubv i := by
  intro e; have := congrArg Fin.val e; simp at this; omega
theorem sS2_ne' (i : Fin 9) : sS (te := te) (qa := qa) 2 ≠ ubw i := by
  intro e; have := congrArg Fin.val e; simp at this; omega

abbrev U2 : Fin 10 ↪ Fin (NSx te qa + 1) := UB (sS 2) sS2_ne
abbrev U3 : Fin 10 ↪ Fin (NSx te qa + 1) := UB2 (sS 2) sS2_ne'

theorem U2_val (i : Fin 10) : (U2 (te := te) (qa := qa) i).val = if i.val = 0 then 67 else 85 + i.val := by
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this; rw [UB_zero]; simp
  · rw [UB_succ _ _ i hi]; simp [hi]; omega

theorem U3_val (i : Fin 10) : (U3 (te := te) (qa := qa) i).val = if i.val = 0 then 67 else 94 + i.val := by
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this; rw [UB2_zero]; simp
  · rw [UB2_succ _ _ i hi]; simp [hi]; omega

theorem U2_ne (i : Fin 10) (X : Fin (NSx te qa + 1)) (hX : X.val ≠ 67 ∧ (X.val < 86 ∨ 95 ≤ X.val)) :
    U2 (te := te) (qa := qa) i ≠ X := by
  intro e; have := congrArg Fin.val e; rw [U2_val] at this; split_ifs at this <;> omega

theorem U3_ne (i : Fin 10) (X : Fin (NSx te qa + 1)) (hX : X.val ≠ 67 ∧ (X.val < 95 ∨ 104 ≤ X.val)) :
    U3 (te := te) (qa := qa) i ≠ X := by
  intro e; have := congrArg Fin.val e; rw [U3_val] at this; split_ifs at this <;> omega

theorem U2_U3 (i j : Fin 10) (hi : i.val ≠ 0) : U2 (te := te) (qa := qa) i ≠ U3 j := by
  intro e; have := congrArg Fin.val e; rw [U2_val, U3_val] at this; split_ifs at this <;> omega

theorem U2_ne_U2 (i j : Fin 10) (h : i ≠ j) : U2 (te := te) (qa := qa) i ≠ U2 j := fun e => h (U2.injective e)
theorem U3_ne_U3 (i j : Fin 10) (h : i ≠ j) : U3 (te := te) (qa := qa) i ≠ U3 j := fun e => h (U3.injective e)

theorem nevS2 (X : Fin (NSx te qa + 1)) (hX : X.val ≠ 67 ∧ (X.val < 86 ∨ 95 ≤ X.val)) :
    X ∉ evS (U2 (te := te) (qa := qa)) := fun hm => by
  simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e <;> exact U2_ne _ X hX e.symm

theorem nevS3 (X : Fin (NSx te qa + 1)) (hX : X.val ≠ 67 ∧ (X.val < 95 ∨ 104 ≤ X.val)) :
    X ∉ evS (U3 (te := te) (qa := qa)) := fun hm => by
  simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e <;> exact U3_ne _ X hX e.symm

theorem nevS2_U3 (i : Fin 10) (hi : i.val ≠ 0) : U3 (te := te) (qa := qa) i ∉ evS (U2 (te := te) (qa := qa)) :=
  nevS2 _ (by rw [U3_val]; simp [hi]; omega)

theorem nevS3_U2 (i : Fin 10) (hi : i.val ≠ 0) : U2 (te := te) (qa := qa) i ∉ evS (U3 (te := te) (qa := qa)) :=
  nevS3 _ (by rw [U2_val]; simp [hi]; omega)

theorem nevR (j : Fin 64) (hj : j.val < 52) : rX j ∉ evR RB := fun hm => by
  simp only [evR, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e | e | e | e <;> exact RB_ne _ j hj e.symm

theorem RB_ne_rB (j : Fin 12) (i : Fin 10) : RB j ≠ rB i := by
  intro e; have := congrArg Fin.val e; simp at this; omega

/-- The registers the phase tracks by value. -/
def XR (j : Fin 64) : Prop := j.val < 52 ∧ j.val ∉ [34, 37, 38]

instance (j : Fin 64) : Decidable (XR j) := by unfold XR; infer_instance

def MSS : List (Fin (NSx te qa + 1)) := [sZ 46, sZ 56, sS 5, sS 6, sS 2] ++ List.ofFn ubv ++ List.ofFn ubw

/-- **The monomial phase's state.** -/
structure MS (Wb Wc : ℕ) (inp VT : List Bool) (σA : WSt) (hd : ℕ) (o46 o56 oV L5 : List Bool) (f : Fin 64 → ℕ)
    (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt) : Prop where
  e2 : ∃ v : Fin 10 → ℕ, EvV U2 RB Wb inp hd 0 v τ ∧ v 8 = 1 ∧ v 9 = 0 ∧ q2 v
  e3 : ∃ w : Fin 10 → ℕ, EvV U3 RB Wc inp hd 0 w τ ∧ w 8 = 1 ∧ w 9 = 0 ∧ q3 w
  out46 : OutOn τ (sZ 46) (rX 37) o46 []
  out56 : OutOn τ (sZ 56) (rX 38) o56 []
  vs : OutOn τ (sS 5) (rX 34) oV L5
  vt : τ.st (sS 4) = VT
  vth : τ.sh (sS 4) = 0
  w6h : τ.sh (sS 6) = 0
  w6l : (τ.st (sS 6)).length ≤ 2 * Wb + 1
  x : ∀ j : Fin 64, XR j → τ.val (rX j) = f j
  fr : SameExcept σA τ MSS RXL

theorem ubv_MSS (i : Fin 9) : ubv (te := te) (qa := qa) i ∈ MSS := by
  unfold MSS; simp only [List.mem_append, List.mem_ofFn]; left; right; exact ⟨i, rfl⟩
theorem ubw_MSS (i : Fin 9) : ubw (te := te) (qa := qa) i ∈ MSS := by
  unfold MSS; simp only [List.mem_append, List.mem_ofFn]; right; exact ⟨i, rfl⟩
theorem U2_MSS (i : Fin 10) : U2 (te := te) (qa := qa) i ∈ MSS := by
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this; rw [UB_zero]; unfold MSS; simp
  · rw [UB_succ _ _ i hi]; exact ubv_MSS _
theorem U3_MSS (i : Fin 10) : U3 (te := te) (qa := qa) i ∈ MSS := by
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this; rw [UB2_zero]; unfold MSS; simp
  · rw [UB2_succ _ _ i hi]; exact ubw_MSS _
theorem evS2_MSS : ∀ X ∈ evS (U2 (te := te) (qa := qa)), X ∈ (MSS : List (Fin (NSx te qa + 1))) := by
  intro X hX; simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> exact U2_MSS _
theorem evS3_MSS : ∀ X ∈ evS (U3 (te := te) (qa := qa)), X ∈ (MSS : List (Fin (NSx te qa + 1))) := by
  intro X hX; simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> exact U3_MSS _
theorem evR_RXL : ∀ q ∈ evR (RB : Fin 12 ↪ Fin NRk), q ∈ (RXL : List (Fin NRk)) := by
  intro q hq; simp only [evR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact rX_mem _
theorem mss_z46 : sZ 46 ∈ (MSS : List (Fin (NSx te qa + 1))) := by unfold MSS; simp
theorem mss_z56 : sZ 56 ∈ (MSS : List (Fin (NSx te qa + 1))) := by unfold MSS; simp
theorem mss_s5 : sS 5 ∈ (MSS : List (Fin (NSx te qa + 1))) := by unfold MSS; simp
theorem mss_s6 : sS 6 ∈ (MSS : List (Fin (NSx te qa + 1))) := by unfold MSS; simp

/-! ## Field transfer -/

section Tr
variable {S : List (Fin (NSx te qa + 1))} {R : List (Fin NRk)} {τ τ' : WState (NSx te qa) NRk}

theorem out_tr {O : Fin (NSx te qa + 1)} {CO : Fin NRk} {o L : List Bool} (h : OutOn τ O CO o L)
    (hS : SameExcept τ τ' S R) (hO : O ∉ S) (hC : CO ∉ R) : OutOn τ' O CO o L :=
  ⟨by rw [hS.st hO]; exact h.1, by rw [hS.sh hO]; exact h.2.1, by rw [hS.val hC]; exact h.2.2⟩

theorem x_tr {f : Fin 64 → ℕ} (h : ∀ j : Fin 64, XR j → τ.val (rX j) = f j) (hS : SameExcept τ τ' S R)
    (hR : ∀ j : Fin 64, XR j → rX j ∉ R) : ∀ j : Fin 64, XR j → τ'.val (rX j) = f j :=
  fun j hj => by rw [hS.val (hR j hj)]; exact h j hj

theorem evv_tr {U : Fin 10 ↪ Fin (NSx te qa + 1)} {Wb hd : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (h : EvV U RB Wb inp hd 0 v τ) (hS : SameExcept τ τ' S R) (hU : ∀ i, U i ∉ S) (hR : ∀ j, RB j ∉ R) :
    EvV U RB Wb inp hd 0 v τ' :=
  evv_transfer h (fun i => ⟨hS.st (hU i), hS.sh (hU i)⟩) (fun j => hS.val (hR j))

theorem xr_evR (j : Fin 64) (hj : XR j) : rX j ∉ evR RB := nevR j hj.1

/-- `EvV` of a block whose numbers did not move, with the shared input's head moved. -/
theorem evv_move {U : Fin 10 ↪ Fin (NSx te qa + 1)} {Wb hd hd' : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (h : EvV U RB Wb inp hd 0 v τ) (hs : ∀ i : Fin 10, i.val ≠ 0 → τ'.st (U i) = τ.st (U i) ∧ τ'.sh (U i) = τ.sh (U i))
    (h0 : τ'.st (U 0) = inp) (h0h : τ'.sh (U 0) = hd') (hr : ∀ j : Fin 12, j ≠ 11 → τ'.val (RB j) = 0) :
    EvV U RB Wb inp hd' 0 v τ' :=
  ⟨fun i hi => ⟨by rw [(hs i (fun e => hi (Fin.ext e))).1]; exact (h.num i hi).1,
    by rw [(hs i (fun e => hi (Fin.ext e))).2]; exact (h.num i hi).2⟩, h0, h0h, hr 1 (by decide),
    fun j _ h11 => hr j h11⟩

end Tr

/-! ## Register steps -/

section MSSteps
variable {Wb Wc : ℕ} {inp VT : List Bool} {σA : WState (NSx te qa) NRk} {hd : ℕ} {o46 o56 oV L5 : List Bool}
  {q2 q3 : (Fin 10 → ℕ) → Prop}

theorem MS.setv {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (j : Fin 64) (hj : XR j)
    (y : ℕ) : MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j y) q2 q3 (τ.setv (rX j) y) := by
  have hS : SameExcept τ (τ.setv (rX j) y) [] [rX j] := sameExcept_setv (S := []) τ (List.mem_singleton_self _) y
  have nj : ∀ k : Fin 64, k.val ≠ j.val → rX k ∉ [rX j] := fun k hk hm => by
    simp only [List.mem_singleton] at hm; exact hk (by rw [rX.injective hm])
  have hj' := hj; unfold XR at hj'; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
  obtain ⟨⟨v, hv, hv8, hv9, hq2⟩, ⟨w, hw, hw8, hw9, hq3⟩, h46, h56, h5, hvt, hvth, h6h, h6l, hx, hfr⟩ := h
  have nRB : ∀ k : Fin 12, RB k ∉ [rX j] := fun k hm => by
    simp only [List.mem_singleton] at hm; exact RB_ne k j hj.1 hm
  refine ⟨⟨v, evv_tr hv hS (fun _ => by simp) nRB, hv8, hv9, hq2⟩, ⟨w, evv_tr hw hS (fun _ => by simp) nRB, hw8, hw9, hq3⟩,
    out_tr h46 hS (by simp) (nj 37 (by simp; omega)), out_tr h56 hS (by simp) (nj 38 (by simp; omega)),
    out_tr h5 hS (by simp) (nj 34 (by simp; omega)), by simp [hvt], by simp [hvth], by simp [h6h], by simp [h6l],
    fun k hk => ?_, se_ext hfr hS (by simp) (by simp [rX_mem])⟩
  by_cases e : k = j
  · subst e; simp
  · rw [hS.val (nj k (fun h => e (Fin.ext h))), Function.update_of_ne e]; exact hx k hk

theorem MS.congr {f g : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ)
    (hfg : ∀ j, XR j → f j = g j) : MS Wb Wc inp VT σA hd o46 o56 oV L5 g q2 q3 τ :=
  { h with x := fun j hj => (h.x j hj).trans (hfg j hj) }

theorem MS.withQ2 {f : Fin 64 → ℕ} {τ : WSt} {q2' : (Fin 10 → ℕ) → Prop} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ)
    (hq : ∀ v, q2 v → q2' v) : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2' q3 τ := by
  obtain ⟨v, a, b, c, d⟩ := h.e2
  exact { h with e2 := ⟨v, a, b, c, hq v d⟩ }

theorem MS.withQ3 {f : Fin 64 → ℕ} {τ : WSt} {q3' : (Fin 10 → ℕ) → Prop} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ)
    (hq : ∀ v, q3 v → q3' v) : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3' τ := by
  obtain ⟨v, a, b, c, d⟩ := h.e3
  exact { h with e3 := ⟨v, a, b, c, hq v d⟩ }

theorem ms_inc (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (j : Fin 64)
    (hj : XR j) (hcap : f j < cap) :
    Runs cap (WMX.inc (rX j)) τ 3 (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j (f j + 1)) q2 q3) := by
  have e := WXExec.inc cap (rX j) τ (by rw [h.x j hj]; exact hcap)
  rw [h.x j hj] at e
  exact ⟨_, e, h.setv j hj _⟩

theorem ms_dec (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (j : Fin 64)
    (hj : XR j) (hcap : f j ≤ cap) :
    Runs cap (WMX.dec (rX j)) τ 1 (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j (f j - 1)) q2 q3) := by
  have e := WXExec.dec cap (rX j) τ (by rw [h.x j hj]; exact hcap)
  rw [h.x j hj] at e
  exact ⟨_, e, h.setv j hj _⟩

theorem ms_clr (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (j : Fin 64)
    (hj : XR j) (hcap : f j ≤ cap) :
    Runs cap (.wm (WM.clear (rX j))) τ (3 * f j + 1) (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j 0) q2 q3) := by
  have e := wclear_spec (cap := cap) (rX j) (f j) τ (h.x j hj) (by rw [h.x j hj]; exact hcap)
  exact ⟨_, WXExec.wm e, h.setv j hj _⟩

theorem ms_add (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (a b : Fin 64)
    (ha : XR a) (hb : XR b) (hab : a ≠ b) (ha7 : a ≠ 7) (hb7 : b ≠ 7) (h7 : f 7 = 0) (hcap : f b + f a ≤ cap) :
    Runs cap (addR (rX a) (rX b) (rX 7)) τ (18 * f a + 3)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f b (f b + f a)) q2 q3) := by
  have e := addR_spec cap (A := rX a) (B := rX b) (T := rX 7) (rX_ne hab) (rX_ne ha7) (rX_ne hb7) τ
    (by rw [h.x 7 (by decide), h7]) (by rw [h.x a ha, h.x b hb]; exact hcap)
  rw [h.x a ha, h.x b hb] at e
  exact ⟨_, e, h.setv b hb _⟩

theorem ms_mul (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ)
    (a a2 b c : Fin 64) (hd5 : [a, a2, b, c, 7].Nodup) (ha : XR a) (ha2 : XR a2) (hb : XR b) (hc : XR c)
    (h2 : f a2 = 0) (h7 : f 7 = 0) (hcap : f c + f a * f b ≤ cap) (hcapA : 2 * f a ≤ cap) :
    Runs cap (mulR (rX a) (rX a2) (rX b) (rX c) (rX 7)) τ (f a * (18 * f b + 3 + 8) + 7 * f a + 3)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f c (f c + f a * f b)) q2 q3) := by
  have hR : [rX a, rX a2, rX b, rX c, rX 7].Nodup := by
    have := hd5.map rX.injective; simpa using this
  have e := mulR_spec cap hR τ (by rw [h.x a2 ha2, h2]) (by rw [h.x 7 (by decide), h7])
    (by rw [h.x a ha, h.x b hb, h.x c hc]; exact hcap) (by rw [h.x a ha]; exact hcapA)
  rw [h.x a ha, h.x b hb, h.x c hc] at e
  exact ⟨_, e, h.setv c hc _⟩

end MSSteps

end NearCubicGates.Close.Expand.PolyTab
