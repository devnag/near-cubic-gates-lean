import SourceAdapters.Refuter.WitnessCodec

/-!
# Exact-state loops, appended pairs and frame reads (input 7, the record codec, part 1)

Generic tools for the uniform setup of proof of `cor:framed-refuter` ("Parsing the outer record, incrementing its
witness field, writing these frames, and returning their heads to zero cost at most `c_0N` steps"):
`whsE`/`whrE` run a stream/register loop through a given list of exact states; `pairW` appends one
framed bit `1 b` to a stream; `fpre` is a frame without its terminator, with cell reads
`rd_fpre_mark`, `rd_fpre_data`, `rd_fpre_after`.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

section Generic
variable {ns nr : ℕ} (cap : ℕ)

/-- A stream loop through exact states: pass `k` takes `st k` to `st (k+1)`. -/
theorem whsE {i : Fin (ns + 1)} {body : WMX ns nr} (st : ℕ → WState ns nr) (n c : ℕ)
    (hbit : ∀ k < n, wbit (st k) i = true) (hend : wbit (st n) i = false)
    (hstep : ∀ k < n, WXExec cap body (st k) (st (k + 1)) c) :
    WXExec cap (.whs i body) (st 0) (st n) (n * (c + 2) + 1) := by
  obtain ⟨τ, e, hτ⟩ := Runs.whs (cap := cap) (i := i) (P := body) (fun k σ => k ≤ n ∧ σ = st (n - k)) c
    (fun σ => σ = st n)
    (fun σ h => by obtain ⟨_, h⟩ := h; subst h; exact ⟨hend, rfl⟩)
    (fun k σ h => by
      obtain ⟨hk, h⟩ := h
      subst h
      refine ⟨hbit _ (by omega), st (n - k), ?_, by omega, rfl⟩
      have := hstep (n - (k + 1)) (by omega)
      rw [show n - (k + 1) + 1 = n - k by omega] at this
      exact this)
    n (st 0) ⟨le_rfl, by simp⟩
  subst hτ
  exact e

/-- A register loop through exact states. -/
theorem whrE {r : Fin nr} {body : WMX ns nr} (st : ℕ → WState ns nr) (n c : ℕ)
    (hv : ∀ k < n, (st k).val r ≠ 0) (hend : (st n).val r = 0)
    (hstep : ∀ k < n, WXExec cap body (st k) (st (k + 1)) c) :
    WXExec cap (.whr r body) (st 0) (st n) (n * (c + 2) + 1) := by
  obtain ⟨τ, e, hτ⟩ := Runs.whr (cap := cap) (r := r) (P := body) (fun k σ => k ≤ n ∧ σ = st (n - k)) c
    (fun σ => σ = st n)
    (fun σ h => by obtain ⟨_, h⟩ := h; subst h; exact ⟨hend, rfl⟩)
    (fun k σ h => by
      obtain ⟨hk, h⟩ := h
      subst h
      refine ⟨hv _ (by omega), st (n - k), ?_, by omega, rfl⟩
      have := hstep (n - (k + 1)) (by omega)
      rw [show n - (k + 1) + 1 = n - k by omega] at this
      exact this)
    n (st 0) ⟨le_rfl, by simp⟩
  subst hτ
  exact e

theorem wtb_append (pre : List Bool) (b : Bool) : writeTapeBit pre pre.length b = pre ++ [b] := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [writeTapeBit, ih]

/-- Append the framed bit `1 b` at the end of a stream. -/
def pairW (S : Fin (ns + 1)) (b : Bool) : WMX ns nr :=
  .seq (WMX.wr S true) (.seq (WMX.fwd S) (.seq (WMX.wr S b) (WMX.fwd S)))

theorem pairW_spec (S : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (hS : σ.sh S = (σ.st S).length) :
    WXExec cap (pairW S b) σ ((σ.sets S (σ.st S ++ [true, b])).seth S (σ.sh S + 2)) 7 := by
  have e1 := WXExec.wr cap S true σ
  have e2 := WXExec.fwd cap S (σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true))
  have e3 := WXExec.wr cap S b ((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).seth S
    ((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).sh S + 1))
  have e4 := WXExec.fwd cap S (((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).seth S
    ((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).sh S + 1)).sets S (writeTapeBit
      ((((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).seth S
        ((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).sh S + 1))).st S)
      (((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).seth S
        ((σ.sets S (writeTapeBit (σ.st S) (σ.sh S) true)).sh S + 1)).sh S) b))
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
  have w1 : writeTapeBit (σ.st S) (σ.sh S) true = σ.st S ++ [true] := by rw [hS, wtb_append]
  have w2 : writeTapeBit (σ.st S ++ [true]) (σ.sh S + 1) b = σ.st S ++ [true, b] := by
    rw [hS, show (σ.st S).length + 1 = (σ.st S ++ [true]).length by simp, wtb_append]; simp
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = S
    · subst hj; simp [w1, w2]
    · simp [Function.update_apply, hj]
  · rfl
  · rfl

end Generic

/-! ## Frames without terminator -/

/-- The framed bits of `l` without the terminator: `1 b_1 1 b_2 ⋯`. -/
def fpre (l : List Bool) : List Bool := l.flatMap fun b => [true, b]

@[simp] theorem fpre_nil : fpre [] = [] := rfl

theorem fpre_append (l₁ l₂ : List Bool) : fpre (l₁ ++ l₂) = fpre l₁ ++ fpre l₂ := by
  simp [fpre, List.flatMap_append]

theorem fpre_cons (b : Bool) (l : List Bool) : fpre (b :: l) = true :: b :: fpre l := rfl

@[simp] theorem fpre_length (l : List Bool) : (fpre l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [fpre_cons, List.length_cons, ih]; ring

theorem frame_eq_fpre (l : List Bool) : RepairOrdinary.frame l = fpre l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, fpre_cons, ih]

theorem frame_append (l₁ l₂ : List Bool) : RepairOrdinary.frame (l₁ ++ l₂) = fpre l₁ ++ RepairOrdinary.frame l₂ := by
  rw [frame_eq_fpre, frame_eq_fpre, fpre_append, List.append_assoc]

theorem fpre_snoc (l : List Bool) (b : Bool) : fpre (l ++ [b]) = fpre l ++ [true, b] := by
  rw [fpre_append]; rfl

theorem rd_fpre_after (l rest : List Bool) (k : ℕ) :
    readTapeBit (fpre l ++ rest) (2 * l.length + k) = readTapeBit rest k := by
  rw [← fpre_length]; exact rd_append_right _ _ _

theorem rd_fpre_mark (l rest : List Bool) {j : ℕ} (h : j < l.length) :
    readTapeBit (fpre l ++ rest) (2 * j) = true := by
  induction l generalizing j with
  | nil => simp at h
  | cons b l ih =>
    cases j with
    | zero => simp [fpre_cons, readTapeBit]
    | succ j =>
      rw [fpre_cons, show 2 * (j + 1) = (2 * j) + 2 by ring]
      have := ih (j := j) (by simp at h; omega)
      simpa [readTapeBit] using this

theorem rd_fpre_data (l rest : List Bool) {j : ℕ} (h : j < l.length) :
    readTapeBit (fpre l ++ rest) (2 * j + 1) = l[j] := by
  induction l generalizing j with
  | nil => simp at h
  | cons b l ih =>
    cases j with
    | zero => simp [fpre_cons, readTapeBit]
    | succ j =>
      rw [fpre_cons, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring]
      have := ih (j := j) (by simp at h; omega)
      simpa [readTapeBit] using this

end NearCubicGates.Adapters.Refuter.Mach
