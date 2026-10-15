import Proof.Wire_3_5.FinalPassWordLib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- A tape padded with blank cells up to length `k`. -/
def pad (l : List Bool) (k : ℕ) : List Bool := l ++ List.replicate (k - l.length) false

theorem pad_length (l : List Bool) (k : ℕ) : (pad l k).length = max l.length k := by
  simp [pad]; omega

theorem pad_zero (l : List Bool) : pad l 0 = l := by simp [pad]

theorem pad_nil (k : ℕ) : pad [] k = List.replicate k false := by simp [pad]

theorem readTapeBit_pad (l : List Bool) (k p : ℕ) : readTapeBit (pad l k) p = readTapeBit l p := by
  unfold readTapeBit pad
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : p < l.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := l) (by omega : l.length ≤ p),
      List.getElem?_replicate]
    split <;> rfl

theorem writeTapeBit_length : ∀ (l : List Bool) (h : ℕ) (b : Bool),
    (writeTapeBit l h b).length = max l.length (h + 1)
  | [], 0, _ => rfl
  | [], h + 1, b => by
    simp only [writeTapeBit, List.length_cons, writeTapeBit_length [] h b, List.length_nil]
    omega
  | _ :: _, 0, _ => by simp only [writeTapeBit, List.length_cons]; omega
  | a :: t, h + 1, b => by
    simp only [writeTapeBit, List.length_cons, writeTapeBit_length t h b]
    omega

theorem readTapeBit_writeTapeBit : ∀ (l : List Bool) (h : ℕ) (b : Bool) (p : ℕ),
    readTapeBit (writeTapeBit l h b) p = if p = h then b else readTapeBit l p
  | [], 0, b, 0 => rfl
  | [], 0, b, p + 1 => by simp [writeTapeBit, readTapeBit]
  | [], h + 1, b, 0 => by simp [writeTapeBit, readTapeBit]
  | [], h + 1, b, p + 1 => by
    have := readTapeBit_writeTapeBit [] h b p
    simp only [writeTapeBit, readTapeBit, List.getD_cons_succ] at this ⊢
    rw [this]
    simp
  | a :: t, 0, b, 0 => rfl
  | a :: t, 0, b, p + 1 => by simp [writeTapeBit, readTapeBit]
  | a :: t, h + 1, b, 0 => by simp [writeTapeBit, readTapeBit]
  | a :: t, h + 1, b, p + 1 => by
    have := readTapeBit_writeTapeBit t h b p
    simp only [writeTapeBit, readTapeBit, List.getD_cons_succ] at this ⊢
    rw [this]
    simp

theorem list_eq_of_read {l m : List Bool} (hl : l.length = m.length) (hr : ∀ p, readTapeBit l p = readTapeBit m p) :
    l = m := by
  apply List.ext_getElem hl
  intro p h1 h2
  have := hr p
  unfold readTapeBit at this
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact this

/-- **Writing commutes with padding.** -/
theorem writeTapeBit_pad (l : List Bool) (k h : ℕ) (b : Bool) :
    writeTapeBit (pad l k) h b = pad (writeTapeBit l h b) k := by
  apply list_eq_of_read
  · rw [writeTapeBit_length, pad_length, pad_length, writeTapeBit_length]; omega
  · intro p
    rw [readTapeBit_writeTapeBit, readTapeBit_pad, readTapeBit_pad, readTapeBit_writeTapeBit]

variable {ns nr : ℕ}

/-- Every stream `i` padded to `K i`. -/
def padAll (σ : WState ns nr) (K : Fin (ns + 1) → ℕ) : WState ns nr :=
  ⟨σ.sh, fun i => pad (σ.st i) (K i), σ.val, σ.cell⟩

@[simp] theorem padAll_sh (σ : WState ns nr) (K : Fin (ns + 1) → ℕ) : (padAll σ K).sh = σ.sh := rfl
@[simp] theorem padAll_val (σ : WState ns nr) (K : Fin (ns + 1) → ℕ) : (padAll σ K).val = σ.val := rfl
@[simp] theorem padAll_cell (σ : WState ns nr) (K : Fin (ns + 1) → ℕ) : (padAll σ K).cell = σ.cell := rfl
@[simp] theorem padAll_st (σ : WState ns nr) (K : Fin (ns + 1) → ℕ) (i : Fin (ns + 1)) :
    (padAll σ K).st i = pad (σ.st i) (K i) := rfl

theorem wbit_padAll (σ : WState ns nr) (K : Fin (ns + 1) → ℕ) (i : Fin (ns + 1)) :
    wbit (padAll σ K) i = wbit σ i := by
  unfold wbit; rw [padAll_st, readTapeBit_pad]; rfl

/-- **Padding transports runs exactly.** -/
theorem wexec_pad {cap : ℕ} {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n)
    (K : Fin (ns + 1) → ℕ) : WExec cap P (padAll σ K) (padAll τ K) n := by
  induction h with
  | skip σ => exact WExec.skip _
  | inc r σ hv => exact WExec.inc r (padAll σ K) hv
  | dec r σ hv => exact WExec.dec r (padAll σ K) hv
  | fwd i σ => exact WExec.fwd i (padAll σ K)
  | bwd i σ => exact WExec.bwd i (padAll σ K)
  | wr i b σ =>
    have e := WExec.wr (cap := cap) i b (padAll σ K)
    refine WExec.cast cap e ?_ le_rfl
    apply WState.eq
    · rfl
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [WState.sets, padAll, writeTapeBit_pad]
      · simp [WState.sets, padAll, Function.update_of_ne hj]
    · rfl
    · rfl
  | setc v σ => exact WExec.setc v (padAll σ K)
  | seq _ _ ih1 ih2 => exact WExec.seq ih1 ih2
  | ifrT hv _ ih => exact WExec.ifrT hv ih
  | ifrF hv _ ih => exact WExec.ifrF hv ih
  | ifsT hb _ ih => exact WExec.ifsT (by rw [wbit_padAll]; exact hb) ih
  | ifsF hb _ ih => exact WExec.ifsF (by rw [wbit_padAll]; exact hb) ih
  | whrF hv => exact WExec.whrF hv
  | whrT hv _ _ ih1 ih2 => exact WExec.whrT hv ih1 ih2
  | whsF hb => exact WExec.whsF (by rw [wbit_padAll]; exact hb)
  | whsT hb _ _ ih1 ih2 => exact WExec.whsT (by rw [wbit_padAll]; exact hb) ih1 ih2
  | mono _ hn ih => exact WExec.mono ih hn

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
