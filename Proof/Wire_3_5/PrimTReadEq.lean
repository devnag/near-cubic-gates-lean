import Proof.Wire_3_5.FinalPassWords

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Two tapes read the same at every position. -/
def RdEq (l l' : List Bool) : Prop := ∀ p, readTapeBit l p = readTapeBit l' p

theorem RdEq.refl (l : List Bool) : RdEq l l := fun _ => rfl
theorem RdEq.symm {l l' : List Bool} (h : RdEq l l') : RdEq l' l := fun p => (h p).symm
theorem RdEq.trans {l l' l'' : List Bool} (h1 : RdEq l l') (h2 : RdEq l' l'') : RdEq l l'' := fun p => (h1 p).trans (h2 p)

/-- **Reading a written cell.** -/
theorem readTapeBit_write : ∀ (l : List Bool) (p : ℕ) (b : Bool) (q : ℕ),
    readTapeBit (writeTapeBit l p b) q = if q = p then b else readTapeBit l q
  | [], 0, b, 0 => rfl
  | [], 0, b, q + 1 => by simp [writeTapeBit, readTapeBit]
  | [], p + 1, b, 0 => by simp [writeTapeBit, readTapeBit]
  | [], p + 1, b, q + 1 => by
    have := readTapeBit_write [] p b q
    simp only [writeTapeBit, readTapeBit, List.getD_cons_succ] at this ⊢
    rw [this]
    simp
  | x :: l, 0, b, 0 => rfl
  | x :: l, 0, b, q + 1 => by simp [writeTapeBit, readTapeBit]
  | x :: l, p + 1, b, 0 => by simp [writeTapeBit, readTapeBit]
  | x :: l, p + 1, b, q + 1 => by
    have := readTapeBit_write l p b q
    simp only [writeTapeBit, readTapeBit, List.getD_cons_succ] at this ⊢
    rw [this]
    simp

theorem rdEq_write {l l' : List Bool} (h : RdEq l l') (p : ℕ) (b : Bool) :
    RdEq (writeTapeBit l p b) (writeTapeBit l' p b) := fun q => by
  rw [readTapeBit_write, readTapeBit_write, h q]

/-- **A stream of blank cells reads like the empty one.** -/
theorem rdEq_blank (l : List Bool) (hl : ∀ b ∈ l, b = false) : RdEq l [] := fun p => by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  cases h : l[p]? with
  | none => rfl
  | some b => exact hl b (List.mem_of_getElem? h)

theorem blank_of_rdEq_nil (l : List Bool) (h : RdEq l []) : ∀ b ∈ l, b = false := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hb
  have := h p
  unfold readTapeBit at this
  rw [List.getD_eq_getElem _ _ hp] at this
  simpa using this

theorem rdEq_append_blank (l r : List Bool) (hr : ∀ b ∈ r, b = false) : RdEq (l ++ r) l := fun p => by
  unfold readTapeBit
  by_cases hp : p < l.length
  · rw [List.getD_append _ _ _ _ hp]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default l false (by omega)]
    exact rdEq_blank r hr (p - l.length)

/-- **Two states read alike**: the same heads, registers and cell, streams reading the same everywhere. -/
structure SimW {ns nr : ℕ} (σ σ' : WState ns nr) : Prop where
  sh : σ'.sh = σ.sh
  val : σ'.val = σ.val
  cell : σ'.cell = σ.cell
  st : ∀ i, RdEq (σ.st i) (σ'.st i)

theorem SimW.refl {ns nr : ℕ} (σ : WState ns nr) : SimW σ σ := ⟨rfl, rfl, rfl, fun _ => RdEq.refl _⟩

theorem SimW.bit {ns nr : ℕ} {σ σ' : WState ns nr} (h : SimW σ σ') (i : Fin (ns + 1)) :
    FinalPass.Tm.wbit σ' i = FinalPass.Tm.wbit σ i := by
  unfold FinalPass.Tm.wbit
  rw [h.sh]
  exact (h.st i (σ.sh i)).symm

/-- **Read-alike states run alike.** -/
theorem wexec_sim {ns nr cap : ℕ} {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    ∀ σ' : WState ns nr, SimW σ σ' → ∃ τ', WExec cap P σ' τ' n ∧ SimW τ τ' := by
  induction h with
  | skip σ => exact fun σ' hs => ⟨σ', WExec.skip σ', hs⟩
  | inc r σ hv =>
    intro σ' hs
    refine ⟨σ'.setv r (σ'.val r + 1), WExec.inc r σ' (by rw [hs.val]; exact hv), ?_, ?_, ?_, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro i; simpa using hs.st i
  | dec r σ hv =>
    intro σ' hs
    refine ⟨σ'.setv r (σ'.val r - 1), WExec.dec r σ' (by rw [hs.val]; exact hv), ?_, ?_, ?_, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro i; simpa using hs.st i
  | fwd i σ =>
    intro σ' hs
    refine ⟨σ'.seth i (σ'.sh i + 1), WExec.fwd i σ', ?_, ?_, ?_, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j; simpa using hs.st j
  | bwd i σ =>
    intro σ' hs
    refine ⟨σ'.seth i (σ'.sh i - 1), WExec.bwd i σ', ?_, ?_, ?_, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j; simpa using hs.st j
  | wr i b σ =>
    intro σ' hs
    refine ⟨σ'.sets i (writeTapeBit (σ'.st i) (σ'.sh i) b), WExec.wr i b σ', ?_, ?_, ?_, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j
      by_cases hj : j = i
      · subst hj
        simp only [WState.sets_st, Function.update_self]
        rw [hs.sh]
        exact rdEq_write (hs.st j) _ b
      · simp only [WState.sets_st, Function.update_of_ne hj]
        exact hs.st j
  | setc v σ =>
    intro σ' hs
    refine ⟨σ'.setc v, WExec.setc v σ', ?_, ?_, ?_, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp
    · intro j; simpa using hs.st j
  | seq _ _ ih1 ih2 =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih1 σ' hs
    obtain ⟨τ2, e2, s2⟩ := ih2 τ1 s1
    exact ⟨τ2, WExec.seq e1 e2, s2⟩
  | ifrT hv _ ih =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih σ' hs
    exact ⟨τ1, WExec.ifrT (by rw [hs.val]; exact hv) e1, s1⟩
  | ifrF hv _ ih =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih σ' hs
    exact ⟨τ1, WExec.ifrF (by rw [hs.val]; exact hv) e1, s1⟩
  | ifsT hb _ ih =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih σ' hs
    exact ⟨τ1, WExec.ifsT (by rw [hs.bit]; exact hb) e1, s1⟩
  | ifsF hb _ ih =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih σ' hs
    exact ⟨τ1, WExec.ifsF (by rw [hs.bit]; exact hb) e1, s1⟩
  | whrF hv =>
    intro σ' hs
    exact ⟨σ', WExec.whrF (by rw [hs.val]; exact hv), hs⟩
  | whrT hv _ _ ih1 ih2 =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih1 σ' hs
    obtain ⟨τ2, e2, s2⟩ := ih2 τ1 s1
    exact ⟨τ2, WExec.whrT (by rw [hs.val]; exact hv) e1 e2, s2⟩
  | whsF hb =>
    intro σ' hs
    exact ⟨σ', WExec.whsF (by rw [hs.bit]; exact hb), hs⟩
  | whsT hb _ _ ih1 ih2 =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih1 σ' hs
    obtain ⟨τ2, e2, s2⟩ := ih2 τ1 s1
    exact ⟨τ2, WExec.whsT (by rw [hs.bit]; exact hb) e1 e2, s2⟩
  | mono _ hn ih =>
    intro σ' hs
    obtain ⟨τ1, e1, s1⟩ := ih σ' hs
    exact ⟨τ1, WExec.mono e1 hn, s1⟩

/-- **A spec stated at `[]` runs on a blank stream of any length**: from a run on `σ.sets i []` and a stream `i` of
blank cells on `σ`, a run on `σ` of the same cost to a state reading like the end state. -/
theorem wexec_blank {ns nr cap : ℕ} {P : WM ns nr} (σ : WState ns nr) (i : Fin (ns + 1))
    (hi : ∀ b ∈ σ.st i, b = false) {τ : WState ns nr} {n : ℕ} (h : WExec cap P (σ.sets i []) τ n) :
    ∃ τ', WExec cap P σ τ' n ∧ SimW τ τ' := by
  refine wexec_sim h σ ⟨rfl, rfl, rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    simp only [WState.sets_st, Function.update_self]
    exact (rdEq_blank _ hi).symm
  · simp only [WState.sets_st, Function.update_of_ne hj]
    exact RdEq.refl _

end NearCubicWires.WireExponent3_5.PrimT.ReadEq
