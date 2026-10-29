import SourceAdapters.Refuter.RProgramWMX
import Proof.Gates.WordPrograms.Hoare
import Proof.Gates.WorkerArith.CtrCallB

/-!
# Word-program tools for the two machines of R (input 7, R: INIT and STEP)

Paper anchor: `lem:multitape-refuter` proof of `lem:multitape-refuter` and `cor:framed-refuter` (R writes every query in full and runs `O(N)` rounds,
each polynomial in `T(N)`), `cor:framed-refuter` proof of `lem:multitape-refuter` and `cor:framed-refuter`.

Generic tools used by both machines of R (`RMachStep`, `RMachInit`):

* `loopS`/`loopR`: stream/register loops through a given family of exact states;
* `forU U R body`: run `body` once per cell of a unary stream `U = 1^a` (register `R` counts, `U` is
  returned to `0`);
* `pairA X b`: append the framed bit `1 b` at the end of an exact stream;
* `dbl U R1 R2 b`: `U := 1^(2u+b)` from `U = 1^u` (unary Horner step);
* `Parked.rechoose`: between pieces a stream outside the exact set may be re-read as any word reading alike
  (cleared scratch streams become `[]` again).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Equalities of word states built by `sets`/`seth`/`setv`. -/
macro "wst" : tactic => `(tactic| (apply WState.eq <;> (try funext x) <;>
  simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setc_sh, WState.setv_st, WState.seth_st,
    WState.sets_st, WState.setc_st, WState.setv_val, WState.seth_val, WState.sets_val, WState.setc_val,
    WState.setv_cell, WState.seth_cell, WState.sets_cell, WState.setc_cell, Function.update_apply] <;>
  (try split_ifs) <;> (try subst_vars) <;> simp_all <;> omega))

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Exact-state loops -/

theorem loopS {i : Fin (ns + 1)} {body : WMX ns nr} (st : ℕ → WState ns nr) (n c : ℕ)
    (hbit : ∀ k < n, wbit (st k) i = true) (hend : wbit (st n) i = false)
    (hstep : ∀ k < n, WXExec cap body (st k) (st (k + 1)) c) :
    WXExec cap (.whs i body) (st 0) (st n) (n * (c + 2) + 1) := by
  obtain ⟨τ, e, hτ⟩ := Runs.whs (cap := cap) (i := i) (P := body) (fun k σ => k ≤ n ∧ σ = st (n - k)) c
    (fun σ => σ = st n)
    (fun σ h => by obtain ⟨_, h⟩ := h; subst h; exact ⟨by simpa using hend, by simp⟩)
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

theorem loopR {r : Fin nr} {body : WMX ns nr} (st : ℕ → WState ns nr) (n c : ℕ)
    (hv : ∀ k < n, (st k).val r ≠ 0) (hend : (st n).val r = 0)
    (hstep : ∀ k < n, WXExec cap body (st k) (st (k + 1)) c) :
    WXExec cap (.whr r body) (st 0) (st n) (n * (c + 2) + 1) := by
  obtain ⟨τ, e, hτ⟩ := Runs.whr (cap := cap) (r := r) (P := body) (fun k σ => k ≤ n ∧ σ = st (n - k)) c
    (fun σ => σ = st n)
    (fun σ h => by obtain ⟨_, h⟩ := h; subst h; exact ⟨by simpa using hend, by simp⟩)
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

/-! ## Rewind by a counter -/

/-- Move stream `U` back by the value of `R`, clearing `R`. -/
def rew (U : Fin (ns + 1)) (R : Fin nr) : WMX ns nr := .wm (WM.rewind U R)

theorem rew_spec (U : Fin (ns + 1)) (R : Fin nr) (σ : WState ns nr) (n : ℕ) (hR : σ.val R = n) (hc : n ≤ cap) :
    WXExec cap (rew U R) σ ((σ.setv R 0).seth U (σ.sh U - n)) (5 * n + 1) :=
  WXExec.wm (wrewind_spec cap U R n σ hR (by omega))

/-! ## Run a body once per cell of a unary stream -/

/-- `σ` with stream `U` at `k` and register `R = k`. -/
def mv (σ : WState ns nr) (U : Fin (ns + 1)) (R : Fin nr) (k : ℕ) : WState ns nr := (σ.seth U k).setv R k

/-- For each cell of `U = 1^a`: run `body` (with `U` at the cell and `R` = its index); rewind `U`. -/
def forU (U : Fin (ns + 1)) (R : Fin nr) (body : WMX ns nr) : WMX ns nr :=
  .seq (.whs U (.seq body (.seq (WMX.fwd U) (WMX.inc R)))) (rew U R)

theorem forU_spec (U : Fin (ns + 1)) (R : Fin nr) (body : WMX ns nr) (a c : ℕ) (st : ℕ → WState ns nr)
    (hU : ∀ k ≤ a, (st k).st U = List.replicate a true) (hUh : ∀ k ≤ a, (st k).sh U = 0)
    (hR : ∀ k ≤ a, (st k).val R = 0)
    (hbody : ∀ k < a, WXExec cap body (mv (st k) U R k) (mv (st (k + 1)) U R k) c) (hcap : a ≤ cap) :
    WXExec cap (forU U R body) (st 0) (st a) (a * (c + 13) + 3) := by
  have e0 : mv (st 0) U R 0 = st 0 := by
    have h1 := hUh 0 (Nat.zero_le _); have h2 := hR 0 (Nat.zero_le _)
    unfold mv; wst
  have hloop := loopS cap (i := U) (body := .seq body (.seq (WMX.fwd U) (WMX.inc R)))
    (fun k => mv (st k) U R k) a (c + 6)
    (fun k hk => by
      simp only [wbit, mv, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hU k hk.le]
      unfold readTapeBit; rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp)
    (by
      simp only [wbit, mv, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hU a le_rfl]
      unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp)])
    (fun k hk => by
      have e1 := hbody k hk
      have e2 := WXExec.fwd cap U (mv (st (k + 1)) U R k)
      have e3 := WXExec.inc cap R ((mv (st (k + 1)) U R k).seth U ((mv (st (k + 1)) U R k).sh U + 1))
        (by simp [mv]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
      unfold mv; wst)
  rw [e0] at hloop
  have e4 := rew_spec cap U R (mv (st a) U R a) a (by simp [mv]) hcap
  refine (WXExec.seq hloop e4).cast cap ?_ (by nlinarith)
  have h1 := hUh a le_rfl; have h2 := hR a le_rfl
  unfold mv; wst

/-! ## Appending framed bits -/

theorem wtb_append (pre : List Bool) (b : Bool) : writeTapeBit pre pre.length b = pre ++ [b] := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [writeTapeBit, ih]

/-- Append the framed bit `1 b` at the end of a stream. -/
def pairA (S : Fin (ns + 1)) (b : Bool) : WMX ns nr :=
  .seq (WMX.wr S true) (.seq (WMX.fwd S) (.seq (WMX.wr S b) (WMX.fwd S)))

theorem pairA_spec (S : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (hS : σ.sh S = (σ.st S).length) :
    WXExec cap (pairA S b) σ ((σ.sets S (σ.st S ++ [true, b])).seth S (σ.sh S + 2)) 7 := by
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

/-! ## The unary Horner step -/

/-- `U := 1^(2u + b)` from `U = 1^u` (registers `R1`, `R2` scratch). -/
def dbl (U : Fin (ns + 1)) (R1 R2 : Fin nr) (b : Bool) : WMX ns nr :=
  .seq (.whs U (.seq (WMX.fwd U) (.seq (WMX.inc R1) (WMX.inc R2))))
    (.seq (.whr R1 (.seq (WMX.wr U true) (.seq (WMX.fwd U) (.seq (WMX.inc R2) (WMX.dec R1)))))
      (.seq (if b then .seq (WMX.wr U true) (.seq (WMX.fwd U) (WMX.inc R2)) else WMX.skip) (rew U R2)))

theorem dbl_spec (U : Fin (ns + 1)) (R1 R2 : Fin nr) (h12 : R1 ≠ R2) (b : Bool) (σ : WState ns nr) (u : ℕ)
    (hU : σ.st U = List.replicate u true) (hUh : σ.sh U = 0) (h1 : σ.val R1 = 0) (h2 : σ.val R2 = 0)
    (hc : 2 * u + 1 ≤ cap) :
    WXExec cap (dbl U R1 R2 b) σ (σ.sets U (List.replicate (2 * u + b.toNat) true)) (40 * u + 20) := by
  -- walk to the end
  have l1 := loopS cap (i := U) (body := .seq (WMX.fwd U) (.seq (WMX.inc R1) (WMX.inc R2)))
    (fun k => ((σ.seth U k).setv R1 k).setv R2 k) u 9
    (fun k hk => by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hU]
      unfold readTapeBit; rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp)
    (by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hU]
      unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp)])
    (fun k hk => by
      have e1 := WXExec.fwd cap U (((σ.seth U k).setv R1 k).setv R2 k)
      have e2 := WXExec.inc cap R1 ((((σ.seth U k).setv R1 k).setv R2 k).seth U
        ((((σ.seth U k).setv R1 k).setv R2 k).sh U + 1)) (by simp [Function.update_apply, h12, h12.symm]; omega)
      have e3 := WXExec.inc cap R2 (((((σ.seth U k).setv R1 k).setv R2 k).seth U
        ((((σ.seth U k).setv R1 k).setv R2 k).sh U + 1)).setv R1 ((((((σ.seth U k).setv R1 k).setv R2 k).seth U
        ((((σ.seth U k).setv R1 k).setv R2 k).sh U + 1))).val R1 + 1)) (by simp [Function.update_apply, h12, h12.symm]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
      wst)
  have s0 : ((σ.seth U 0).setv R1 0).setv R2 0 = σ := by wst
  rw [s0] at l1
  -- append `u` ones
  let st2 : ℕ → WState ns nr := fun k =>
    (((σ.sets U (List.replicate (u + k) true)).seth U (u + k)).setv R1 (u - k)).setv R2 (u + k)
  have l2 := loopR cap (r := R1) (body := .seq (WMX.wr U true) (.seq (WMX.fwd U) (.seq (WMX.inc R2) (WMX.dec R1))))
    st2 u 9
    (fun k hk => by simp [st2, Function.update_apply, h12, h12.symm]; omega)
    (by simp [st2, Function.update_apply, h12, h12.symm])
    (fun k hk => by
      have e1 := WXExec.wr cap U true (st2 k)
      have hw : writeTapeBit ((st2 k).st U) ((st2 k).sh U) true = List.replicate (u + (k + 1)) true := by
        simp only [st2, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self]
        have := wtb_append (List.replicate (u + k) true) true
        rw [List.length_replicate] at this
        rw [this, ← List.replicate_succ']; rfl
      rw [hw] at e1
      have e2 := WXExec.fwd cap U ((st2 k).sets U (List.replicate (u + (k + 1)) true))
      have e3 := WXExec.inc cap R2 (((st2 k).sets U (List.replicate (u + (k + 1)) true)).seth U
        (((st2 k).sets U (List.replicate (u + (k + 1)) true)).sh U + 1)) (by simp [st2, Function.update_apply, h12, h12.symm]; omega)
      have e4 := WXExec.dec cap R1 ((((st2 k).sets U (List.replicate (u + (k + 1)) true)).seth U
        (((st2 k).sets U (List.replicate (u + (k + 1)) true)).sh U + 1)).setv R2
        ((((st2 k).sets U (List.replicate (u + (k + 1)) true)).seth U
        (((st2 k).sets U (List.replicate (u + (k + 1)) true)).sh U + 1)).val R2 + 1))
        (by simp [st2, Function.update_apply, h12, h12.symm]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
      simp only [st2]; wst)
  have s1 : ((σ.seth U u).setv R1 u).setv R2 u = st2 0 := by
    simp only [st2]
    rw [show u + 0 = u by omega, show u - 0 = u by omega, ← hU]
    wst
  rw [s1] at l1
  -- the last bit and the rewind
  have l3 : WXExec cap (if b then .seq (WMX.wr U true) (.seq (WMX.fwd U) (WMX.inc R2)) else WMX.skip) (st2 u)
      (((σ.sets U (List.replicate (2 * u + b.toNat) true)).seth U (2 * u + b.toNat)).setv R2
        (2 * u + b.toNat)) 7 := by
    cases b
    · refine (WXExec.skip cap (st2 u)).cast cap ?_ (by omega)
      simp only [st2, Bool.toNat_false, Nat.add_zero, Nat.sub_self, show u + u = 2 * u by omega]
      wst
    · have e1 := WXExec.wr cap U true (st2 u)
      have hw : writeTapeBit ((st2 u).st U) ((st2 u).sh U) true = List.replicate (2 * u + 1) true := by
        simp only [st2, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self]
        have := wtb_append (List.replicate (u + u) true) true
        rw [List.length_replicate] at this
        rw [this, ← List.replicate_succ', show u + u + 1 = 2 * u + 1 by omega]
      rw [hw] at e1
      have e2 := WXExec.fwd cap U ((st2 u).sets U (List.replicate (2 * u + 1) true))
      have e3 := WXExec.inc cap R2 (((st2 u).sets U (List.replicate (2 * u + 1) true)).seth U
        (((st2 u).sets U (List.replicate (2 * u + 1) true)).sh U + 1)) (by simp [st2, Function.update_apply, h12, h12.symm]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
      simp only [if_true, st2, Bool.toNat_true]
      wst
  have l4 := rew_spec cap U R2 (((σ.sets U (List.replicate (2 * u + b.toNat) true)).seth U (2 * u + b.toNat)).setv R2
    (2 * u + b.toNat)) (2 * u + b.toNat) (by simp) (by cases b <;> simp <;> omega)
  refine (WXExec.seq l1 (WXExec.seq l2 (WXExec.seq l3 l4))).cast cap ?_ ?_
  · have : st2 u = st2 u := rfl
    wst
  · have : b.toNat ≤ 1 := Bool.toNat_le b
    nlinarith

/-! ## Re-reading scratch streams between pieces -/

theorem Parked.rechoose {E : Fin (ns + 1) → Prop} {σ : WState ns nr} {a : Fin (ns + 2 + nr) → List Bool}
    (h : Refuter.Mach.Parked E σ a) (X : Fin (ns + 1)) (hX : ¬ E X) (l : List Bool) (hl : RdEq l (σ.st X)) :
    Refuter.Mach.Parked E (σ.sets X l) a := by
  refine ⟨fun i => ?_, fun i hi => ?_, h.cell, h.reg⟩
  · by_cases hi : i = X
    · subst hi; simp only [WState.sets_st, Function.update_self]; exact hl.trans (h.read i)
    · simp only [WState.sets_st, Function.update_of_ne hi]; exact h.read i
  · have hiX : i ≠ X := fun e => hX (e ▸ hi)
    simp only [WState.sets_st, Function.update_of_ne hiX]; exact h.exact i hi

/-- A word reading blank everywhere reads like `[]`. -/
theorem rdEq_nil_of_blank (l : List Bool) (h : ∀ p, readTapeBit l p = false) : RdEq [] l := fun p => by
  rw [h p]; rfl

theorem blank_replicate (n : ℕ) : ∀ p, readTapeBit (List.replicate n false) p = false := by
  intro p; unfold readTapeBit
  by_cases hp : p < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hp)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

/-- A word reading blank everywhere is all blanks. -/
theorem eq_replicate_of_blank (l : List Bool) (h : ∀ p, readTapeBit l p = false) :
    l = List.replicate l.length false := by
  apply List.ext_getElem (by simp)
  intro p h1 _
  have := h p
  unfold readTapeBit at this
  rw [List.getD_eq_getElem _ _ h1] at this
  simp [this]

end NearCubicGates.Adapters.Refuter.RM
