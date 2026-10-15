import Proof.Gates.WorkerArith.VerdictVal
import Proof.Gates.WordPrograms.ToReg
import Proof.Gates.WordPrograms.BinWDiv
import Proof.Gates.CounterMachine.Interval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)

/-- The register file at rest. -/
def regs (W L lp bad : ℕ) (r : Fin 16) : ℕ :=
  if r = 6 then 2 * W + 1 else if r = 7 then W else if r = 8 then L else if r = 10 then lp
  else if r = 12 then bad else 0

/-- The ruler of `convM`. -/
def ruler (L : ℕ) : List Bool := false :: List.replicate L true

/-- The state at rest. -/
def mk (w : List Bool) (W : ℕ) (wv : Fin 30 → ℕ) (pos lp bad : ℕ) : WState 29 16 :=
  ⟨fun i => if i = 2 then pos else 0,
   fun i => if i = 0 then frame w else if i = 1 then [] else if i = 2 then w else if i = 3 then ruler w.length
     else frame (binary W (wv i)),
   regs W w.length lp bad, false⟩

/-- A number stream. -/
def NumS (X : Fin 30) : Prop := 4 ≤ X.val

section Mk
variable (w : List Bool) (W : ℕ) (wv : Fin 30 → ℕ) (pos lp bad : ℕ)

theorem NumS.ne {X : Fin 30} (hX : NumS X) : X ≠ 0 ∧ X ≠ 1 ∧ X ≠ 2 ∧ X ≠ 3 := by
  unfold NumS at hX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp at hX

theorem mk_numOn {X : Fin 30} (hX : NumS X) : NumOn (mk w W wv pos lp bad) X W (wv X) := by
  obtain ⟨h0, h1, h2, h3⟩ := hX.ne
  exact ⟨by simp [mk, h0, h1, h2, h3], by simp [mk, h2]⟩

theorem mk_sets {X : Fin 30} (hX : NumS X) (v : ℕ) :
    (mk w W wv pos lp bad).sets X (frame (binary W v)) = mk w W (Function.update wv X v) pos lp bad := by
  obtain ⟨h0, h1, h2, h3⟩ := hX.ne
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = X
    · subst hi; simp [mk, h0, h1, h2, h3]
    · simp only [WState.sets_st, Function.update_of_ne hi, mk]
  · rfl
  · rfl

theorem mk_seth2 (p : ℕ) : (mk w W wv pos lp bad).seth 2 p = mk w W wv p lp bad := by
  apply WState.eq
  · funext i; by_cases hi : i = 2
    · subst hi; simp [mk]
    · simp [mk, hi, Function.update_of_ne hi]
  · rfl
  · rfl
  · rfl

@[simp] theorem mk_val : (mk w W wv pos lp bad).val = regs W w.length lp bad := rfl
@[simp] theorem mk_cell : (mk w W wv pos lp bad).cell = false := rfl
theorem mk_st2 : (mk w W wv pos lp bad).st 2 = w := by simp [mk]
theorem mk_sh2 : (mk w W wv pos lp bad).sh 2 = pos := by simp [mk]
theorem mk_st3 : (mk w W wv pos lp bad).st 3 = ruler w.length := by simp [mk]
theorem mk_sh3 : (mk w W wv pos lp bad).sh 3 = 0 := by simp [mk]

theorem mk_setv_lp (v : ℕ) : (mk w W wv pos lp bad).setv 10 v = mk w W wv pos v bad := by
  apply WState.eq <;> try rfl
  funext r; by_cases hr : r = 10
  · subst hr; simp [mk, regs]
  · simp only [WState.setv_val, Function.update_of_ne hr, mk, regs]; split_ifs <;> simp_all

theorem mk_setv_bad (v : ℕ) : (mk w W wv pos lp bad).setv 12 v = mk w W wv pos lp v := by
  apply WState.eq <;> try rfl
  funext r; by_cases hr : r = 12
  · subst hr; simp [mk, regs]
  · simp only [WState.setv_val, Function.update_of_ne hr, mk, regs]; split_ifs <;> simp_all

/-- A scratch register (`regs = 0`) set back to `0`. -/
theorem mk_setv_zero {r : Fin 16} (hr : regs W w.length lp bad r = 0) :
    (mk w W wv pos lp bad).setv r 0 = mk w W wv pos lp bad := by
  rw [← hr]; exact wsetv_same _ r

end Mk

/-! ## Arithmetic steps -/

section Ops
variable {w : List Bool} {W : ℕ} {wv : Fin 30 → ℕ} {pos lp bad : ℕ} (cap : ℕ)

theorem regs0 {W L lp bad : ℕ} : regs W L lp bad 0 = 0 := rfl
theorem regs1 {W L lp bad : ℕ} : regs W L lp bad 1 = 0 := rfl

theorem one_le_sq (W : ℕ) : W + 1 ≤ (W + 1) ^ 2 := by nlinarith

/-- A step from rest to rest, with its cost bound. -/
def Step (cap : ℕ) (P : WMX 29 16) (σ τ : WState 29 16) (c : ℕ) : Prop := WXExec cap P σ τ c

theorem zeroM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.zero X Y 0 1) (mk w W wv pos lp bad) (mk w W (Function.update wv X 0) pos lp bad)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.zero_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hcap
  rw [mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (by nlinarith [one_le_sq W])

theorem oneM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hW : 1 ≤ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.one X Y 0 1) (mk w W wv pos lp bad) (mk w W (Function.update wv X 1) pos lp bad)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.one_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hW hcap
  rw [mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (by nlinarith [one_le_sq W])

theorem incM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hv : wv X + 1 < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.inc X Y 0 1) (mk w W wv pos lp bad) (mk w W (Function.update wv X (wv X + 1)) pos lp bad)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.inc_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hv hcap
  rw [mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (by nlinarith [one_le_sq W])

theorem addM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hv : wv X + wv Y < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.add X Y 0 1) (mk w W wv pos lp bad) (mk w W (Function.update wv X (wv X + wv Y)) pos lp bad)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.add_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hv hcap
  rw [mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (by nlinarith [one_le_sq W])

theorem copyM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.copy X Y 0 1) (mk w W wv pos lp bad) (mk w W (Function.update wv X (wv Y)) pos lp bad)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.copy_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hcap
  rw [mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (by nlinarith [one_le_sq W])

theorem shlM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.shl X Y 0 1) (mk w W wv pos lp bad) (mk w W (Function.update wv X (2 * wv X)) pos lp bad)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.shl_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hcap
  rw [mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (by nlinarith [one_le_sq W])

theorem ltM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hx : wv X < 2 ^ W) (hy : wv Y < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.lt X Y 0 1) (mk w W wv pos lp bad) ((mk w W wv pos lp bad).setv 0 (decide (wv X < wv Y)).toNat)
      (50 * (W + 1) ^ 2) := by
  have h := BinW.lt_spec cap W (F := 0) (R := 1) hXY (by decide) (mk w W wv pos lp bad) (wv X) (wv Y) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hY) rfl rfl hx hy hcap
  exact h.mono (by nlinarith [one_le_sq W])

theorem mulM {A B C S : Fin 30} (hA : NumS A) (hB : NumS B) (hC : NumS C) (hS : NumS S) (hAB : A ≠ B) (hAC : A ≠ C)
    (hAS : A ≠ S) (hBC : B ≠ C) (hBS : B ≠ S) (hCS : C ≠ S) (hab : wv A * wv B < 2 ^ W) (hb : wv B < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.mul A B C S 0 1 2) (mk w W wv pos lp bad)
      (mk w W (Function.update (Function.update wv C (wv A * wv B)) S 0) pos lp bad) (300 * (W + 1) ^ 2) := by
  have h := BinW.mul_spec cap W (F := 0) (R := 1) (G := 2) hAB hAC hAS hBC hBS hCS (by decide) (by decide) (by decide)
    (mk w W wv pos lp bad) (wv A) (wv B) (wv C) (wv S) (mk_numOn _ _ _ _ _ _ hA) (mk_numOn _ _ _ _ _ _ hB)
    (mk_numOn _ _ _ _ _ _ hC) (mk_numOn _ _ _ _ _ _ hS) rfl rfl rfl hab hb hcap
  rw [mk_sets _ _ _ _ _ _ hC, mk_sets _ _ _ _ _ _ hS] at h
  exact h.mono (BinW.mulCost_le W)

theorem divM {A B Q M X : Fin 30} (hA : NumS A) (hB : NumS B) (hQ : NumS Q) (hM : NumS M) (hX : NumS X)
    (hAQ : A ≠ Q) (hAM : A ≠ M) (hAX : A ≠ X) (hBQ : B ≠ Q) (hBM : B ≠ M) (hBX : B ≠ X) (hQM : Q ≠ M) (hQX : Q ≠ X)
    (hMX : M ≠ X) (ha : wv A < 2 ^ W) (hb : 0 < wv B) (h2b : 2 * wv B ≤ 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (BinW.divmod A B Q M X 0 1 3 4) (mk w W wv pos lp bad)
      (mk w W (Function.update (Function.update (Function.update wv Q (wv A / wv B)) M (wv A % wv B)) X 0) pos lp bad)
      (400 * (W + 1) ^ 2) := by
  have h := BinW.divmod_spec cap W (F := 0) (R := 1) (K := 3) (T := 4) hAQ hAM hAX hBQ hBM hBX hQM hQX hMX
    (by decide) (by decide) (by decide) (by decide) (mk w W wv pos lp bad) (wv A) (wv B) (wv Q) (wv M) (wv X)
    (mk_numOn _ _ _ _ _ _ hA) (mk_numOn _ _ _ _ _ _ hB) (mk_numOn _ _ _ _ _ _ hQ) (mk_numOn _ _ _ _ _ _ hM)
    (mk_numOn _ _ _ _ _ _ hX) rfl rfl rfl rfl ha hb h2b hcap
  rw [mk_sets _ _ _ _ _ _ hQ, mk_sets _ _ _ _ _ _ hM, mk_sets _ _ _ _ _ _ hX] at h
  exact h.mono (BinW.divCost_le W)

theorem nzM {X Z : Fin 30} (hX : NumS X) (hZ : NumS Z) (hXZ : X ≠ Z) (hx : wv X < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (nzP X Z 11 0 1) (mk w W wv pos lp bad) ((mk w W wv pos lp bad).setv 11 (decide (wv X ≠ 0)).toNat)
      (50 * (W + 1) ^ 2) := by
  have h := nzP_spec cap W (NZ := 11) (F := 0) (Rr := 1) hXZ (by decide) (mk w W wv pos lp bad) (wv X) (wv Z) (mk_numOn _ _ _ _ _ _ hX)
    (mk_numOn _ _ _ _ _ _ hZ) rfl rfl rfl hx hcap
  exact h.mono (by nlinarith [one_le_sq W])

/-- **Reading one field.** The raw word holds `pre ++ natWord v ++ post`, read up to `pre`; the number stream `X`
(at `0`) receives `v` and the read position moves past the field. -/
theorem readM {X : Fin 30} (hX : NumS X) (hX0 : wv X = 0) (pre post : List Bool) (v : ℕ)
    (hw : w = pre ++ natWord v ++ post) (hpos : pos = pre.length) (hW : 1 ≤ W) (hv : v < 2 ^ W)
    (hkc : natBitLength v ≤ w.length) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (CounterMachine.natRead 2 3 X 5 6 4) (mk w W wv pos lp bad)
      (mk w W (Function.update wv X v) (pre.length + (natWord v).length) lp bad) (80 * (W + 1) ^ 2) := by
  obtain ⟨h0, h1, h2, h3⟩ := hX.ne
  have h := CounterMachine.natRead_spec cap W w.length (I := 2) (K := 3) (X := X) (by decide) (Ne.symm h2)
    (Ne.symm h3) (C := 5) (R2 := 6) (T := 4) (by decide) (by decide) (by decide) (mk w W wv pos lp bad) pre post v
    hW hv (by rw [mk_st2, hw]) (by rw [mk_sh2, hpos]) (by rw [mk_st3]; rfl) (mk_sh3 _ _ _ _ _ _) hkc
    (by have := (mk_numOn w W wv pos lp bad hX).1; rw [hX0] at this; exact this) (mk_numOn w W wv pos lp bad hX).2
    rfl rfl rfl hcap
  rw [mk_sets _ _ _ _ _ _ hX, mk_seth2] at h
  refine h.mono ?_
  have hn := NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le v W hW hv
  unfold CounterMachine.natReadCost NearCubicWires.WireExponent3_5.CompilerMachine.Pool.convCost
  nlinarith [one_le_sq W]

/-- Zero a number stream, then read one field into it. -/
def zread (X : Fin 30) : WMX 29 16 := .seq (BinW.zero X 9 0 1) (CounterMachine.natRead 2 3 X 5 6 4)

theorem zreadM {X : Fin 30} (hX : NumS X) (hX4 : X ≠ 9) (pre post : List Bool) (v : ℕ)
    (hw : w = pre ++ natWord v ++ post) (hpos : pos = pre.length) (hW : 1 ≤ W) (hv : v < 2 ^ W)
    (hkc : natBitLength v ≤ w.length) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (zread X) (mk w W wv pos lp bad)
      (mk w W (Function.update wv X v) (pre.length + (natWord v).length) lp bad) (140 * (W + 1) ^ 2) := by
  have e1 := zeroM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap hX
    (by unfold NumS; decide) hX4 (by omega)
  have e2 := readM (wv := Function.update wv X 0) (lp := lp) (bad := bad) cap hX (by simp) pre post v hw hpos hW hv
    hkc hcap
  rw [Function.update_idem] at e2
  exact (WXExec.seq e1 e2).mono (by nlinarith [one_le_sq W])

end Ops

/-! ## Fields of the request word -/

open NearCubicGates.Close.Worker

/-- The read position before field `k`. -/
def pfx (r : VerdictReq) (k : ℕ) : ℕ := (((nats r).take k).flatMap natWord).length

theorem pfx_succ (r : VerdictReq) (k : ℕ) (hk : k < (nats r).length) :
    pfx r (k + 1) = pfx r k + (natWord ((nats r).getD k 0)).length := by
  unfold pfx; rw [take_succ_flatMap natWord (nats r) k 0 hk, List.length_append]

theorem pfx_all (r : VerdictReq) : pfx r (nats r).length = (verdictWord r).length := by
  unfold pfx; rw [List.take_length, verdictWord_eq]

/-- **Reading field `k`** of the request word. -/
theorem zreadF (r : VerdictReq) {W : ℕ} {wv : Fin 30 → ℕ} {lp bad : ℕ} (cap : ℕ) {X : Fin 30} (hX : NumS X)
    (hX4 : X ≠ 9) (k : ℕ) (hk : k < (nats r).length) (hW : (verdictWord r).length ≤ W) (hW1 : 1 ≤ W)
    (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (zread X) (mk (verdictWord r) W wv (pfx r k) lp bad)
      (mk (verdictWord r) W (Function.update wv X ((nats r).getD k 0)) (pfx r (k + 1)) lp bad)
      (140 * (W + 1) ^ 2) := by
  have hmem := getD_mem (nats r) k hk
  have h := zreadM (w := verdictWord r) (W := W) (wv := wv) (pos := pfx r k) (lp := lp) (bad := bad) cap hX hX4
    (((nats r).take k).flatMap natWord) (((nats r).drop (k + 1)).flatMap natWord) ((nats r).getD k 0)
    (by rw [verdictWord_eq]; exact flatMap_split natWord (nats r) k 0 hk) rfl hW1
    (lt_of_lt_of_le (field_lt r hmem) (Nat.pow_le_pow_right (by norm_num) hW)) (field_nbl r hmem) hcap
  rw [pfx_succ r k hk]
  exact h

end NearCubicGates.Close.WorkerArith
