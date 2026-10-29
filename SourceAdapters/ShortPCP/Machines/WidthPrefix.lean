import SourceAdapters.ShortPCP.TimeStages
import Proof.Gates.WordPrograms.OutX
import Proof.Gates.Codec.Unframe
import Proof.Gates.Interfaces.WordFn

/-!
# Single-run time, stage 1: the width prefix (`Time.PrefixStage`, proved)

The verdict is computed by programs of the released cell language (`Joins/FieldCells.lean`), whose word width is
`Sz.W s = 2^(c1·s)·a1` for an input starting with `s` ones (`Cells.ctxOf`, `L/Proof/Gates/Cells/Run.lean`). The
X5(a) input `frame data ++ frame R` gives no such prefix, and `Request.Valid` bounds the field degree `f` only by
`|data|` (proof of `thm:short-pcp-ours`: field elements are `f`-bit words, `f = O(log T)`), so this ordinary stage writes
`prefixWord w = 1^(size |w|) 0 ++ w` (`2^(size |w|) > |w|`): count the pairs of `frame w` (`countL`), rewind, emit
`size |w|` framed ones by halving the count (`emitLoop`), the framed zero, the pairs of `w` (L's `fieldO`), and close
(L's `closeOut`). Within `200·(|w|+1)²` steps (`prefixStage`).
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.WidthPrefix

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open StablePartition.Workspace (overlay)

abbrev St := WState 1 5

/-- The machine's state: the input stream holds `frame w`, the output stream `o`. -/
def pst (w o : List Bool) (h0 h1 : ℕ) (r : Fin 5 → ℕ) : St := ⟨![h0, h1], ![frame w, o], r, false⟩

variable (cap : ℕ)

/-! ## Counting the input -/

/-- `N := |w|`, `M := 2|w|` (the input head's position). -/
def countL : WM 1 5 := .whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (.seq (.inc 0) (.seq (.inc 1) (.inc 1)))))

theorem count_spec (w : List Bool) (hcap : 2 * w.length < cap) :
    ∀ m j, j + m = w.length → WExec cap countL (pst w [] (2 * j) 0 ![j, 2 * j, 0, 0, 0])
      (pst w [] (2 * w.length) 0 ![w.length, 2 * w.length, 0, 0, 0]) (17 * m + 1) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj; subst hj
    refine WExec.mono (WExec.whsF ?_) (by omega)
    change readTapeBit (frame w) (2 * w.length) = false
    rw [readTapeBit, NearCubicGates.Close.Codec.frame_getD_even]
    simp
  | succ m ih =>
    intro j hj
    let τ := pst w [] (2 * j) 0 ![j, 2 * j, 0, 0, 0]
    have hb : wbit τ 0 = true := by
      change readTapeBit (frame w) (2 * j) = true
      rw [readTapeBit, NearCubicGates.Close.Codec.frame_getD_even]
      simp; omega
    have e1 := WExec.fwd (cap := cap) (0 : Fin 2) τ
    have e2 := WExec.fwd (cap := cap) (0 : Fin 2) (τ.seth 0 (τ.sh 0 + 1))
    have e3 := WExec.inc (cap := cap) (0 : Fin 5)
      ((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)) (by simp [τ, pst]; omega)
    have e4 := WExec.inc (cap := cap) (1 : Fin 5)
      (((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)).setv 0
        (((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)).val 0 + 1)) (by simp [τ, pst]; omega)
    have e5 := WExec.inc (cap := cap) (1 : Fin 5)
      ((((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)).setv 0
        (((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)).val 0 + 1)).setv 1
        ((((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)).setv 0
        (((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)).val 0 + 1)).val 1 + 1))
        (by simp [τ, pst]; omega)
    have hi := ih (j + 1) (by omega)
    refine WExec.mono (WExec.whsT hb (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))))
      ?_ le_rfl) hi)
      (by omega)
    apply WState.eq
    · funext i; fin_cases i <;> simp [τ, pst]; omega
    · rfl
    · funext i; fin_cases i <;> simp [τ, pst] <;> omega
    · rfl

/-! ## Halving a register -/

/-- `H := H + ⌊N/2⌋`, `N := 0`. -/
def halfL : WM 1 5 := .whr 0 (.seq (.dec 0) (.ifr 0 (.seq (.dec 0) (.inc 2)) .skip))

theorem half_spec : ∀ m (σ : St), σ.val 0 = m → σ.val 0 ≤ cap → σ.val 2 + m < cap →
    WExec cap halfL σ ((σ.setv 0 0).setv 2 (σ.val 2 + m / 2)) (9 * m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro σ h0 hc h2
    rcases m with _ | _ | m
    · refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
      apply WState.eq
      · rfl
      · rfl
      · funext r; by_cases hr0 : r = 0
        · subst hr0; simp [h0]
        · by_cases hr2 : r = 2
          · subst hr2; simp
          · simp [WState.setv, Function.update_of_ne hr0, Function.update_of_ne hr2]
      · rfl
    · have e1 := WExec.dec (cap := cap) (0 : Fin 5) σ (by omega)
      have e2 : WExec cap (.ifr 0 (.seq (.dec 0) (.inc 2)) .skip) (σ.setv 0 (σ.val 0 - 1))
          (σ.setv 0 (σ.val 0 - 1)) 1 := WExec.ifrF (by simp [h0]) (WExec.skip _)
      have e3 := WExec.whrF (cap := cap) (r := (0 : Fin 5))
        (P := .seq (.dec 0) (.ifr 0 (.seq (.dec 0) (.inc 2)) .skip)) (σ := σ.setv 0 (σ.val 0 - 1)) (by simp [h0])
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) e3) ?_ (by omega)
      apply WState.eq
      · rfl
      · rfl
      · funext r; by_cases hr0 : r = 0
        · subst hr0; simp [h0]
        · by_cases hr2 : r = 2
          · subst hr2; simp
          · simp [WState.setv, Function.update_of_ne hr0, Function.update_of_ne hr2]
      · rfl
    · have e1 := WExec.dec (cap := cap) (0 : Fin 5) σ (by omega)
      set σ1 := σ.setv 0 (σ.val 0 - 1)
      have e2 := WExec.dec (cap := cap) (0 : Fin 5) σ1 (by simp [σ1]; omega)
      set σ2 := σ1.setv 0 (σ1.val 0 - 1)
      have e3 := WExec.inc (cap := cap) (2 : Fin 5) σ2 (by simp [σ2, σ1]; omega)
      set σ3 := σ2.setv 2 (σ2.val 2 + 1)
      have e4 := WExec.ifrT (r := (0 : Fin 5)) (Q := .skip) (by simp [σ1]; omega) (WExec.seq e2 e3)
      have hi := ih m (by omega) σ3 (by simp [σ3, σ2, σ1]; omega) (by simp [σ3, σ2, σ1]; omega)
        (by simp [σ3, σ2, σ1]; omega)
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e4) hi) ?_ (by omega)
      apply WState.eq
      · rfl
      · rfl
      · funext r; by_cases hr0 : r = 0
        · subst hr0; simp [σ3, σ2, σ1]
        · by_cases hr2 : r = 2
          · subst hr2; simp [σ3, σ2, σ1]; omega
          · simp [σ3, σ2, σ1, WState.setv, Function.update_of_ne hr0, Function.update_of_ne hr2]
      · rfl

/-- `N := N + H`, `H := 0`. -/
def moveL : WM 1 5 := .whr 2 (.seq (.dec 2) (.inc 0))

theorem move_spec : ∀ k (σ : St), σ.val 2 = k → σ.val 2 ≤ cap → σ.val 0 + k < cap →
    WExec cap moveL σ ((σ.setv 2 0).setv 0 (σ.val 0 + k)) (7 * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro σ h2 _ _
    refine WExec.cast cap (WExec.whrF h2) ?_ le_rfl
    apply WState.eq
    · rfl
    · rfl
    · funext r; by_cases hr0 : r = 0
      · subst hr0; simp
      · by_cases hr2 : r = 2
        · subst hr2; simp [h2]
        · simp [WState.setv, Function.update_of_ne hr0, Function.update_of_ne hr2]
    · rfl
  | succ k ih =>
    intro σ h2 hc h0
    have e1 := WExec.dec (cap := cap) (2 : Fin 5) σ (by omega)
    set σ1 := σ.setv 2 (σ.val 2 - 1)
    have e2 := WExec.inc (cap := cap) (0 : Fin 5) σ1 (by simp [σ1]; omega)
    set σ2 := σ1.setv 0 (σ1.val 0 + 1)
    have hi := ih σ2 (by simp [σ2, σ1]; omega) (by simp [σ2, σ1]; omega) (by simp [σ2, σ1]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) hi) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext r; by_cases hr0 : r = 0
      · subst hr0; simp [σ2, σ1]; omega
      · by_cases hr2 : r = 2
        · subst hr2; simp [σ2, σ1]
        · simp [σ2, σ1, WState.setv, Function.update_of_ne hr0, Function.update_of_ne hr2]
    · rfl

/-- `N := ⌊N/2⌋` (through `H`, which starts and ends at `0`). -/
def halveL : WM 1 5 := .seq halfL moveL

theorem halve_spec (σ : St) (h2 : σ.val 2 = 0) (hc : σ.val 0 < cap) :
    WExec cap halveL σ (σ.setv 0 (σ.val 0 / 2)) (17 * σ.val 0 + 3) := by
  have e1 := half_spec cap (σ.val 0) σ rfl (by omega) (by omega)
  set σ1 := (σ.setv 0 0).setv 2 (σ.val 2 + σ.val 0 / 2)
  have e2 := move_spec cap (σ.val 0 / 2) σ1 (by simp [σ1, h2]) (by simp [σ1, h2]; omega) (by simp [σ1]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext r; by_cases hr0 : r = 0
    · subst hr0; simp [σ1]
    · by_cases hr2 : r = 2
      · subst hr2; simp [σ1, h2]
      · simp [σ1, WState.setv, Function.update_of_ne hr0, Function.update_of_ne hr2]
  · rfl

/-! ## Emitting the prefix -/

/-- One pass: append the framed bit `1` (`true, true`) to the output, halve `N`. -/
def emitBody : WMX 1 5 := .seq (emitO 1 3 true) (.seq (emitO 1 3 true) (.wm halveL))

/-- `size N` passes. -/
def emitLoop : WMX 1 5 := .whr 0 emitBody

/-- The state after `k` passes. -/
def qst (w : List Bool) (n k : ℕ) : St := pst w (List.replicate (2 * k) true) 0 (2 * k) ![n / 2 ^ k, 0, 0, 2 * k, 0]

theorem outOn_qst (w : List Bool) (n k : ℕ) : OutOn (qst w n k) 1 3 (List.replicate (2 * k) true) [] :=
  ⟨by simp [qst, pst, overlay], by simp [qst, pst], by simp [qst, pst]⟩

theorem emitLoop_spec (w : List Bool) (n : ℕ) (hc : 2 * n + 2 < cap) :
    ∀ r k, k + r = Nat.size n → WXExec cap emitLoop (qst w n k) (qst w n (Nat.size n)) (r * (17 * n + 30) + 1) := by
  have hsz : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  intro r
  induction r with
  | zero =>
    intro k hk
    rw [Nat.add_zero] at hk; subst hk
    refine WXExec.mono (WXExec.whrF ?_) (by omega)
    simp only [qst, pst]
    show n / 2 ^ Nat.size n = 0
    exact Nat.div_eq_of_lt (Nat.lt_size_self n)
  | succ r ih =>
    intro k hk
    have hk1 : 2 ^ k ≤ n := by
      by_contra h
      have : Nat.size n ≤ k := Nat.size_le.mpr (by omega)
      omega
    have hpos : n / 2 ^ k ≠ 0 := by
      have := Nat.div_pos hk1 (Nat.two_pow_pos k); omega
    have hle : n / 2 ^ k ≤ n := Nat.div_le_self _ _
    have e1 := emitO_spec cap (qst w n k) _ _ true (outOn_qst w n k) (by simp; omega)
    have e2 := emitO_spec cap _ _ _ true (outOn_outSt (qst w n k) 1 3 (List.replicate (2 * k) true ++ [true]) [])
      (by simp; omega)
    rw [outSt_outSt] at e2
    set σ2 := outSt (qst w n k) 1 3 (List.replicate (2 * k) true ++ [true] ++ [true]) []
    have e3 := halve_spec cap σ2 (by simp [σ2, outSt, qst, pst]) (by simp [σ2, outSt, qst, pst]; omega)
    have hi := ih (k + 1) (by omega)
    have hst : σ2.setv 0 (σ2.val 0 / 2) = qst w n (k + 1) := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [σ2, outSt, qst, pst] <;> ring
      · funext i; fin_cases i <;> simp [σ2, outSt, qst, pst, overlay] <;> omega
      · funext i; fin_cases i <;> simp [σ2, outSt, qst, pst, Nat.div_div_eq_div_mul, pow_succ] <;> ring
      · rfl
    have body : WXExec cap emitBody (qst w n k) (qst w n (k + 1)) (17 * n + 28) := by
      refine WXExec.seq' cap e1 (WXExec.seq' cap e2 (WXExec.cast cap (WXExec.wm e3) hst le_rfl) le_rfl) ?_
      simp only [σ2, outSt, qst, pst]
      simp
      omega
    exact WXExec.mono (WXExec.whrT (by simpa [qst, pst] using hpos) body hi) (by nlinarith)

/-! ## The stage -/

/-- **The width-prefix program**: count, rewind, `size |w|` framed ones, the framed zero, the pairs of `w`, close. -/
def prefixP : WMX 1 5 :=
  .seq (.wm countL) (.seq (.wm (WM.rewind 0 1)) (.seq emitLoop (.seq (emitO 1 3 true) (.seq (emitO 1 3 false)
    (.seq (fieldO 0 1 4 3) (closeOutX 1 3))))))

theorem frame_prefix (s : ℕ) (w : List Bool) :
    frame (List.replicate s true ++ false :: w) =
      List.replicate (2 * s) true ++ [true] ++ [false] ++ frameP w ++ [false] := by
  induction s with
  | zero => simp [frame_eq_frameP]
  | succ s ih =>
    rw [List.replicate_succ, List.cons_append, frame, ih, show 2 * (s + 1) = 2 * s + 1 + 1 by ring,
      List.replicate_succ, List.replicate_succ]
    simp

/-- The budget and the space bound. -/
def prefixBudget (n : ℕ) : ℕ := 200 * (n + 1) ^ 2
def prefixCap (n : ℕ) : ℕ := 8 * n + 40

theorem prefixP_spec (w : List Bool) :
    WXExec (prefixCap w.length) prefixP (NearCubicGates.Close.Interfaces.startState 1 5 w)
      (pst w (frame (Time.prefixWord w)) 0 0 ![0, 0, 0, 0, 0]) (prefixBudget w.length) := by
  set n := w.length with hn
  set cap := prefixCap n
  have hcap : cap = 8 * n + 40 := rfl
  have hsz : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h0 : NearCubicGates.Close.Interfaces.startState 1 5 w = pst w [] (2 * 0) 0 ![0, 2 * 0, 0, 0, 0] := by
    apply WState.eq
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  -- count
  have e1 := count_spec cap w (by omega) n 0 (by omega)
  rw [← h0] at e1
  rw [← hn] at e1
  -- rewind the input
  have e2 := wrewind_spec cap (0 : Fin 2) (1 : Fin 5) (2 * n) (pst w [] (2 * w.length) 0 ![w.length, 2 * w.length, 0, 0, 0])
    (by simp [pst, hn]) (by simp [pst]; omega)
  have hq0 : ((pst w [] (2 * w.length) 0 ![w.length, 2 * w.length, 0, 0, 0]).setv 1 0).seth 0
      ((pst w [] (2 * w.length) 0 ![w.length, 2 * w.length, 0, 0, 0]).sh 0 - 2 * n) = qst w n 0 := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [pst, qst, hn]
    · funext i; fin_cases i <;> simp [pst, qst, hn]
    · funext i; fin_cases i <;> simp [pst, qst, hn]
    · rfl
  rw [hq0] at e2
  -- the ones
  have e3 := emitLoop_spec cap w n (by omega) (Nat.size n) 0 (by omega)
  -- the zero
  set s := Nat.size n
  have e4 := emitO_spec cap (qst w n s) _ _ true (outOn_qst w n s) (by simp; omega)
  have e5 := emitO_spec cap _ _ _ false (outOn_outSt (qst w n s) 1 3 (List.replicate (2 * s) true ++ [true]) [])
    (by simp; omega)
  rw [outSt_outSt] at e5
  set σ5 := outSt (qst w n s) 1 3 (List.replicate (2 * s) true ++ [true] ++ [false]) []
  -- the pairs of `w`
  have e6 := fieldO_spec cap (Src := (0 : Fin 2)) (O := (1 : Fin 2)) (CS := (4 : Fin 5)) (CO := (3 : Fin 5))
    (by decide) (by decide) σ5 w [] _ [] (by simp [σ5, outSt, qst, pst, frame_eq_frameP])
    (by simp [σ5, outSt, qst, pst]) (by simp [σ5, outSt, qst, pst])
    (outOn_outSt (qst w n s) 1 3 _ []) (by simp; omega)
  rw [outSt_outSt] at e6
  set σ6 := outSt (qst w n s) 1 3 (List.replicate (2 * s) true ++ [true] ++ [false] ++ frameP w) []
  -- close
  have e7 := closeOut_spec cap (O := (1 : Fin 2)) (CO := (3 : Fin 5)) σ6 _ [] (outOn_outSt (qst w n s) 1 3 _ [])
    (by simp; omega)
  have hfin : ((σ6.sets 1 (overlay (List.replicate (2 * s) true ++ [true] ++ [false] ++ frameP w ++ [false]) [])).seth 1
      0).setv 3 0 = pst w (frame (Time.prefixWord w)) 0 0 ![0, 0, 0, 0, 0] := by
    have hz : n / 2 ^ s = 0 := Nat.div_eq_of_lt (Nat.lt_size_self n)
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ6, outSt, qst, pst]
    · funext i; fin_cases i <;> simp [σ6, outSt, qst, pst, overlay, Time.prefixWord, frame_prefix, s, hn]
    · funext i; fin_cases i <;> simp [σ6, outSt, qst, pst, hz]
    · rfl
  have whole := WXExec.seq' cap (WXExec.wm e1) (WXExec.seq' cap (WXExec.wm e2) (WXExec.seq' cap e3
    (WXExec.seq' cap e4 (WXExec.seq' cap e5 (WXExec.seq' cap e6 (WXExec.cast cap (WXExec.wm e7) hfin le_rfl)
    le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl
  refine WXExec.mono whole ?_
  simp only [prefixBudget]
  simp
  nlinarith

/-- **The width-prefix word function** (`w ↦ frame (1^(size |w|) 0 ++ w)`). -/
noncomputable def prefixWF :
    WordFunction (List Bool) id (fun w => frame (Time.prefixWord w)) (fun w => prefixBudget w.length) :=
  NearCubicGates.Close.Interfaces.wordFunction_of_wmx prefixP (1 : Fin 2) (by decide) (fun w => prefixCap w.length)
    (fun w => ⟨_, prefixP_spec w, by simp [pst], fun i => by fin_cases i <;> rfl, fun q => by fin_cases q <;> rfl⟩)

/-- **Stage 1 of `Time.singleRunTime_of_stages`**, proved. -/
theorem prefixStage : Time.PrefixStage :=
  ⟨oracleOfProgram prefixWF.program, 200, 2, fun o w => oracleOfProgram_runs prefixWF o w (Time.prefixWord w) rfl⟩

end NearCubicGates.Adapters.ShortPCP.Machines.WidthPrefix
