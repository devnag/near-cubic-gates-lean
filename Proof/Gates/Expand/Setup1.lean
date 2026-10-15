import Proof.Gates.Expand.Core

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

/-! ## The number block -/

def nbv (j : ℕ) : ℕ := if j < 9 then j + 1 else if j < 18 then j + 4 else if j < 39 then j + 5 else j + 6

theorem nbv_lt (j : ℕ) (h : j < 53) : nbv j < NS + 1 := by show nbv j < 64; unfold nbv; split_ifs <;> omega

def NB : Fin 53 ↪ Fin (NS + 1) :=
  ⟨fun j => ⟨nbv j.val, nbv_lt j.val j.isLt⟩, fun a b e => by
    have := congrArg Fin.val e; simp only at this
    apply Fin.ext; unfold nbv at this; split_ifs at this <;> omega⟩

@[simp] theorem NB_val (j : Fin 53) : (NB j).val = nbv j.val := rfl

theorem NB_U (i : Fin 10) (hi : i ≠ 0) : NB ⟨i.val - 1, by omega⟩ = U i := by
  have := Fin.val_ne_of_ne hi; simp at this
  apply Fin.ext; simp only [NB_val, U_val, nbv]; split_ifs <;> omega

theorem NB_UF (i : Fin 12) (hi : 3 ≤ i.val) : NB ⟨i.val + 6, by omega⟩ = UF i := by
  apply Fin.ext; simp only [NB_val, UF_val, MB_val, PB_val, nbv]; split_ifs <;> omega

theorem NB_MB (i : Fin 18) : NB ⟨i.val + 21, by omega⟩ = MB i := by
  apply Fin.ext; simp only [NB_val, UF_val, MB_val, PB_val, nbv]; split_ifs <;> omega

theorem NB_PB (i : Fin 14) : NB ⟨i.val + 39, by omega⟩ = PB i := by
  apply Fin.ext; simp only [NB_val, UF_val, MB_val, PB_val, nbv]; split_ifs <;> omega

theorem NB_ne_O (j : Fin 53) : NB j ≠ O := sne (by
  have := j.isLt; simp only [NB_val, O_val, nbv]; split_ifs <;> omega)
theorem NB_ne_ORC (j : Fin 53) : NB j ≠ ORC := sne (by
  have := j.isLt; simp only [NB_val, ORC_val, nbv]; split_ifs <;> omega)
theorem NB_ne_0 (j : Fin 53) : NB j ≠ U 0 := sne (by
  have := j.isLt; simp only [NB_val, U_val, nbv, Fin.val_zero]; split_ifs <;> omega)
theorem NB_ne_rec (j : Fin 53) (k : Fin 12) (hk : k.val < 3) : NB j ≠ UF k := sne (by
  have := j.isLt; simp only [NB_val, UF_val, nbv]; split_ifs <;> omega)
theorem NB_ne_X0 (j : Fin 53) : NB j ≠ X 0 := sne (by
  have := j.isLt; simp only [NB_val, X_val, nbv, Fin.val_zero]; split_ifs <;> omega)

/-! ## Initialization of a list of streams -/

def initL (K K2 : Fin NR) : List (Fin (NS + 1)) → WMX NS NR
  | [] => WMX.skip
  | X :: l => .seq (initNum X K K2) (initL K K2 l)

theorem initL_spec (cap : ℕ) {K K2 : Fin NR} (hK : K ≠ K2) (k : ℕ) (hcap : 2 * k ≤ cap) :
    ∀ (l : List (Fin (NS + 1))) (σ : WState NS NR), (∀ X ∈ l, (σ.st X).length ≤ 2 * k + 1 ∧ σ.sh X = 0) →
      σ.val K = k → σ.val K2 = 0 →
      Runs cap (initL K K2 l) σ (l.length * (initCost k + 1))
        (fun τ => (∀ X ∈ l, τ.st X = frame (binary k 0)) ∧ SameExcept σ τ l [] ∧ ∀ X, τ.sh X = σ.sh X) := by
  intro l
  induction l with
  | nil =>
    intro σ _ _ _
    simp only [initL, List.length_nil, zero_mul]
    exact Runs.of (WXExec.skip cap σ) ⟨by simp, SameExcept.refl _ _ _, fun _ => rfl⟩
  | cons X l ih =>
    intro σ hl hKv hK2
    have hX := hl X List.mem_cons_self
    have e := initNum_spec (X := X) cap hK σ k hX.1 hX.2 hKv hK2 hcap
    refine (Runs.seqE e ((ih _ (fun Y hY => ?_) (by simpa using hKv) (by simpa using hK2)).post
      (fun τ ⟨h1, h2, h3⟩ => ⟨?_, ?_, ?_⟩))).cost (by simp; ring_nf; omega)
    · have := hl Y (List.mem_cons_of_mem X hY)
      by_cases e : Y = X
      · subst e; simp [frame_length, hX.2]
      · simp [Function.update_of_ne e, this.1, this.2]
    · intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      · by_cases hm : Y ∈ l
        · exact h1 Y hm
        · rw [h2.st hm]; simp
      · exact h1 Y hY
    · exact (sameExcept_sets (S := X :: l) (Rg := []) σ (by simp) _).trans
        (se_sub h2 (fun y hy => List.mem_cons_of_mem X hy) (fun _ h => h))
    · intro Y; rw [h3 Y]; simp

/-- All number streams. -/
def nbList : List (Fin (NS + 1)) := List.ofFn fun j : Fin 53 => NB j

theorem mem_nbList (j : Fin 53) : NB j ∈ nbList := by unfold nbList; rw [List.mem_ofFn]; exact ⟨j, rfl⟩

theorem nbList_length : nbList.length = 53 := by simp [nbList]

/-! ## The input length -/

theorem frame_mark_lt : ∀ (bs : List Bool) (i : ℕ), i < bs.length → readTapeBit (frame bs) (2 * i) = true
  | [], i, h => absurd h (by simp)
  | b :: bs, 0, _ => rfl
  | b :: bs, i + 1, h => by
      have := frame_mark_lt bs i (by simp at h; omega)
      unfold readTapeBit at *
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
      simpa [frame] using this

def measLoop : WMX NS NR :=
  .whs (U 0) (.seq (WMX.fwd (U 0)) (.seq (WMX.inc (GR 1)) (.seq (WMX.fwd (U 0)) (.seq (WMX.inc (GR 1))
    (WMX.inc (GR 0))))))

def measRew : WMX NS NR := .whr (GR 1) (.seq (WMX.dec (GR 1)) (.seq (WMX.inc (Y 0)) (WMX.bwd (U 0))))

/-- `GR 0 := |w|`, `Y 0 := 2|w| + 1`. -/
def meas : WMX NS NR := .seq measLoop (.seq measRew (WMX.inc (Y 0)))

def measCost (n : ℕ) : ℕ := (n * (15 + 2) + 1) + 1 + ((2 * n * (7 + 2) + 1) + 1 + 3)

theorem meas_spec (cap : ℕ) (w : List Bool) (σ : WState NS NR) (hst : σ.st (U 0) = frame w) (hsh : σ.sh (U 0) = 0)
    (h0 : σ.val (GR 0) = 0) (h1 : σ.val (GR 1) = 0) (hY : σ.val (Y 0) = 0) (hcap : 2 * w.length + 2 ≤ cap) :
    Runs cap meas σ (measCost w.length) (fun τ => SameExcept σ τ [] [GR 0, Y 0] ∧ τ.val (GR 0) = w.length ∧
      τ.val (Y 0) = 2 * w.length + 1) := by
  set n := w.length with hn
  have g01 : GR 0 ≠ GR 1 := GR.injective.ne (by decide)
  have gy0 : GR 0 ≠ Y 0 := rne (by simp)
  have gy1 : GR 1 ≠ Y 0 := rne (by simp)
  -- the counting loop
  let Inv : ℕ → WState NS NR → Prop := fun k τ => k ≤ n ∧ SameExcept σ τ [U 0] [GR 0, GR 1] ∧
    τ.st (U 0) = frame w ∧ τ.sh (U 0) = 2 * (n - k) ∧ τ.val (GR 1) = 2 * (n - k) ∧ τ.val (GR 0) = n - k
  have hl : Runs cap measLoop σ (n * (15 + 2) + 1) (Inv 0) := by
    refine Runs.whs Inv 15 (Inv 0) (fun τ h => ⟨?_, h⟩) (fun k τ h => ⟨?_, ?_⟩) n σ ⟨le_rfl, SameExcept.refl _ _ _,
      hst, by simp [hsh], by simp [h1], by simp [h0]⟩
    · obtain ⟨_, _, hs0, hs, _, _⟩ := h
      unfold wbit; rw [hs0, hs, Nat.sub_zero]; exact frame_end_gen w
    · obtain ⟨hk, _, hs0, hs, _, _⟩ := h
      unfold wbit; rw [hs0, hs]; exact frame_mark_lt w _ (by omega)
    · obtain ⟨hk, f, hs0, hs, ha, hc⟩ := h
      have e := WXExec.seq (WXExec.fwd cap (U 0) τ) (WXExec.seq (WXExec.inc cap (GR 1) _ (by simp; omega))
        (WXExec.seq (WXExec.fwd cap (U 0) _) (WXExec.seq (WXExec.inc cap (GR 1) _ (by simp; omega))
          (WXExec.inc cap (GR 0) _ (by simp [Function.update_of_ne g01]; omega)))))
      refine Runs.of (WXExec.mono e (by omega)) ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · refine f.trans ?_
        exact ((((sameExcept_seth _ (by simp) _).trans (sameExcept_setv _ (by simp) _)).trans
          (sameExcept_seth _ (by simp) _)).trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_setv _ (by simp) _)
      · simpa using hs0
      · simp [hs]; omega
      · simp [Function.update_of_ne g01.symm, ha]; omega
      · simp [Function.update_of_ne g01, hc]; omega
  refine Runs.seq hl (fun τ1 h1' => ?_)
  obtain ⟨_, f1, hs01, hs1, ha1, hc1⟩ := h1'
  simp only [Nat.sub_zero] at hs1 ha1 hc1
  -- the rewind
  let Inv2 : ℕ → WState NS NR → Prop := fun k τ => k ≤ 2 * n ∧ SameExcept σ τ [U 0] [GR 0, GR 1, Y 0] ∧
    τ.st (U 0) = frame w ∧ τ.sh (U 0) = k ∧ τ.val (GR 1) = k ∧ τ.val (Y 0) = 2 * n - k ∧ τ.val (GR 0) = n
  have hr : Runs cap measRew τ1 (2 * n * (7 + 2) + 1) (Inv2 0) := by
    refine Runs.whr Inv2 7 (Inv2 0) (fun τ h => ⟨by rw [h.2.2.2.2.1], h⟩) (fun k τ h => ⟨?_, ?_⟩) (2 * n) τ1
      ⟨le_rfl, se_sub f1 (by simp) (by simp [List.cons_subset]), hs01, hs1, ha1,
        by rw [f1.val (by simp [gy0.symm, gy1.symm]), hY]; simp, hc1⟩
    · rw [h.2.2.2.2.1]; simp
    · obtain ⟨hk, f, hs0, hs, ha, hy, hc⟩ := h
      have e := WXExec.seq (WXExec.dec cap (GR 1) τ (by omega)) (WXExec.seq (WXExec.inc cap (Y 0) _
        (by simp [Function.update_of_ne gy1.symm]; omega)) (WXExec.bwd cap (U 0) _))
      refine Runs.of (WXExec.mono e (by omega)) ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact f.trans (((sameExcept_setv _ (by simp) _).trans (sameExcept_setv _ (by simp) _)).trans
          (sameExcept_seth _ (by simp) _))
      · simpa using hs0
      · simp [hs]
      · simp [Function.update_of_ne gy1, ha]
      · simp [hy, Function.update_of_ne gy1.symm]; omega
      · simp [Function.update_of_ne gy0, Function.update_of_ne g01, hc]
  refine Runs.seq hr (fun τ2 h2' => ?_)
  obtain ⟨_, f2, hs02, hs2, ha2, hy2, hc2⟩ := h2'
  refine Runs.of (WXExec.inc cap (Y 0) τ2 (by rw [hy2]; omega)) ⟨?_, ?_, ?_⟩
  · refine ⟨fun x _ => ?_, fun q hq => ?_, by simpa using f2.2.2⟩
    · by_cases e : x = U 0
      · subst e; simp [hs2, hsh, hs02, hst]
      · simpa using f2.1 x (by simp [e])
    · by_cases e : q = GR 1
      · subst e; simp [Function.update_of_ne gy1, ha2, h1]
      · simp at hq; rw [WState.setv_val, Function.update_of_ne hq.2]; exact f2.2.1 q (by simp [hq.1, e, hq.2])
  · simp [Function.update_of_ne gy0, hc2]
  · simp [hy2] <;> omega

end NearCubicGates.Close.Expand.Layout
