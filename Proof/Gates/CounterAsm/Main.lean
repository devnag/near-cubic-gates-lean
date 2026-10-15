import Proof.Gates.CounterAsm.Cell
import Proof.Gates.CounterAsm.Statement
import Proof.Gates.CounterAsm.OutLen
import Proof.Gates.Cells.InputLen
import Proof.Gates.Cells.OutLen
import Proof.Foundations.PolynomialSchedule

set_option autoImplicit false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (ivl)
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab (idealStart)
open NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule

/-- The cell request of a (call, witness word), when the dispatch proceeds to the cells. -/
noncomputable def reqOf (B1 B2 cT : ℕ) (c : Call) (w : List Bool) : Option (CellReq B1 B2 cT) := by
  classical
  exact if h : c.Admitted B1 B2 ∧ c.W ≠ 0 then
    match hp : selectParams cT (header c) with
    | none => none
    | some p => match hw : decodeWitness c p w with
      | none => none
      | some wt => some ⟨c, p, wt, h.1, h.2, hp, ⟨w, hw⟩⟩
  else none

theorem reqOf_none {B1 B2 cT : ℕ} {c : Call} {w : List Bool} (h : reqOf B1 B2 cT c w = none) :
    dispatchWord B1 B2 cT c w = natWord 0 ++ outputWord (counterOnCall B1 B2 cT c w) := by
  classical
  unfold reqOf at h
  unfold dispatchWord
  by_cases hA : c.Admitted B1 B2 ∧ c.W ≠ 0
  · rw [dif_pos hA] at h
    rw [if_pos hA]
    split at h
    · rename_i hp; rw [hp]
    · rename_i p hp
      split at h
      · rename_i hw; rw [hp]; simp only []; rw [hw]
      · exact absurd h (by simp)
  · rw [if_neg hA]

theorem reqOf_some {B1 B2 cT : ℕ} {c : Call} {w : List Bool} {r : CellReq B1 B2 cT}
    (h : reqOf B1 B2 cT c w = some r) :
    r.c = c ∧ dispatchWord B1 B2 cT c w = natWord 1 ++ cellInput r ∧
      counterOnCall B1 B2 cT c w = outputOf r.c r.p r.wt := by
  classical
  unfold reqOf at h
  by_cases hA : c.Admitted B1 B2 ∧ c.W ≠ 0
  · rw [dif_pos hA] at h
    split at h
    · exact absurd h (by simp)
    · rename_i p hp
      split at h
      · exact absurd h (by simp)
      · rename_i wt hw
        cases h
        refine ⟨rfl, ?_, ?_⟩
        · unfold dispatchWord; rw [if_pos hA]; simp only [hp, hw]; rfl
        · unfold counterOnCall; rw [if_pos hA.1, if_neg hA.2]; simp only [hp, hw]
  · rw [dif_neg hA] at h; exact absurd h (by simp)

/-! ## Step 2: value links -/

theorem kOf_eq_inner (cT n : ℕ) : kOf cT n = Counter.inner cT n := by
  unfold kOf Counter.inner Jmax muOf lamOf Target.mu Target.lambda
  rw [Recovery.TableSem.clog_eq_size, Recovery.TableSem.clog_eq_size]
  ring

/-- The selected `k` is the program's `kOf`. -/
theorem req_k {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : r.p.k = kOf cT r.c.n := by
  rw [kOf_eq_inner]; exact (selectParams_spec cT (header r.c) r.p r.hp).k_eq

theorem req_k_lt {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : r.p.k < r.c.n :=
  (selectParams_spec cT (header r.c) r.p r.hp).k_lt

theorem req_ivl {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    ∃ S : ℕ, certainSum r.c r.p r.wt = S ∧
      S + 2 ^ (kOf cT r.c.n - 1) * uncCount r.c r.p r.wt < 2 ^ (r.c.n + 1) ∧
      ivl S (uncCount r.c r.p r.wt) (kOf cT r.c.n) r.c.n = outputOf r.c r.p r.wt := by
  obtain ⟨S, hS, hfit⟩ := certainSum_nat r.c r.p r.wt
  obtain ⟨w, hw⟩ := r.hw
  have hcard : r.wt.I.card = r.p.k := decodeWitness_card r.c r.p w r.wt hw
  have hk := req_k r
  have hlt := req_k_lt r
  rw [card_cells, hcard] at hfit
  have h2 : 2 ^ r.p.k * 2 ^ (r.c.n - r.p.k) = 2 ^ r.c.n := by rw [← pow_add]; congr 1; omega
  refine ⟨S, hS, ?_, ?_⟩
  · rw [← hk]
    have : 2 ^ r.c.n < 2 ^ (r.c.n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [outputOf_eq, ← hk, hS]
    unfold ivl
    push_cast
    rfl

theorem cellN_head (c : Call) (p : Params) (wt : Wit c.n) :
    CounterMachine.cellN c p wt = c.n :: (CounterMachine.cellN c p wt).tail := by
  simp [CounterMachine.cellN, CounterMachine.callN]

/-- The cell input as the natural-number list `cell_run` reads. -/
theorem cellInput_eq {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    cellInput r = (r.c.n :: (CounterMachine.cellN r.c r.p r.wt).tail).flatMap natWord := by
  rw [← cellN_head, CounterMachine.cellN_word]; rfl

/-- The dispatch word on the cell path. -/
theorem dispatch_cell {B1 B2 cT : ℕ} {c : Call} {w : List Bool} {r : CellReq B1 B2 cT}
    (h : reqOf B1 B2 cT c w = some r) :
    dispatchWord B1 B2 cT c w = natWord 1 ++ (r.c.n :: (CounterMachine.cellN r.c r.p r.wt).tail).flatMap natWord := by
  rw [(reqOf_some h).2.1, cellInput_eq]

/-- The dispatch word on the final-answer path. -/
theorem dispatch_zero {B1 B2 cT : ℕ} {c : Call} {w : List Bool} (h : reqOf B1 B2 cT c w = none) :
    dispatchWord B1 B2 cT c w = natWord 0 ++ (CounterMachine.ratN (counterOnCall B1 B2 cT c w).1 ++
      CounterMachine.ratN (counterOnCall B1 B2 cT c w).2).flatMap natWord := by
  rw [reqOf_none h, List.flatMap_append, CounterMachine.ratN_word, CounterMachine.ratN_word]; rfl

/-! ## Step 3: the cell tables as records, the counter program's lens, cost and cap -/

/-- The sorted, width-`recWidth` cell records whose record stream is `cellWord`. -/
noncomputable def recsOf {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : List (List Bool) :=
  ((((List.range (2 ^ cellBits r.wt.I)).flatMap fun i => (reqIds r.c r.p).map (cellRec r.c r.p r.wt i)).insertionSort
    (· ≤ ·)).map (SignedSortKey.binary (recWidth r.c r.p r.wt)))

theorem cellWord_eq {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    cellWord r.c r.p r.wt = (recsOf r).flatMap frame ++ [false] := rfl

theorem recsOf_ne {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : ∀ x ∈ recsOf r, x ≠ [] := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  intro h
  have := congrArg List.length h
  rw [SignedSortKey.binary_length] at this
  unfold recWidth valueWidth at this
  simp at this

section Pack
variable {B1 B2 cT : ℕ} (D : DispatchMachine B1 B2 cT) (CellTables : TablesMachine B1 B2 cT) (CellsProc : CellsMachine B1 B2 cT)

noncomputable def lensOf (c : Call) (w : List Bool) :
    Fin (NSc D.wf.program CellTables.wf.program CellsProc.wf.program + 1) → ℕ := fun i =>
  if i = sLD D.wf.program CellTables.wf.program CellsProc.wf.program then D.budget c w
  else if i = sLK D.wf.program CellTables.wf.program CellsProc.wf.program then
    (match reqOf B1 B2 cT c w with | some r => CellTables.budget r | none => 0)
  else if i = sLO D.wf.program CellTables.wf.program CellsProc.wf.program then
    (match reqOf B1 B2 cT c w with | some r => CellsProc.budget r | none => 0)
  else 0

/-- The final-answer path's printed naturals. -/
noncomputable def zeroVs (c : Call) (w : List Bool) : List ℕ :=
  CounterMachine.ratN (counterOnCall B1 B2 cT c w).1 ++ CounterMachine.ratN (counterOnCall B1 B2 cT c w).2

/-- The run's cost. -/
noncomputable def costOf (c : Call) (w : List Bool) : ℕ :=
  match reqOf B1 B2 cT c w with
  | some r => cellCost (D.budget c w) (CellTables.budget r) (CellsProc.budget r)
      ((r.c.n :: (CounterMachine.cellN r.c r.p r.wt).tail).flatMap natWord).length ((recsOf r).flatMap frame).length
      r.c.n cT
  | none => zeroCost (D.budget c w) ((zeroVs (B1 := B1) (B2 := B2) (cT := cT) c w).flatMap natWord).length

/-- The run's capacity. -/
noncomputable def capOf (c : Call) (w : List Bool) : ℕ :=
  match reqOf B1 B2 cT c w with
  | some r => cellCap ((r.c.n :: (CounterMachine.cellN r.c r.p r.wt).tail).flatMap natWord).length
      ((recsOf r).flatMap frame).length r.c.n cT
  | none => 2 * ((zeroVs (B1 := B1) (B2 := B2) (cT := cT) c w).flatMap natWord).length + 2

theorem lensOf_LD (c : Call) (w : List Bool) :
    lensOf D CellTables CellsProc c w (sLD D.wf.program CellTables.wf.program CellsProc.wf.program) = D.budget c w := by
  simp [lensOf]

theorem lensOf_zero (c : Call) (w : List Bool) (i : Fin (NSc D.wf.program CellTables.wf.program CellsProc.wf.program + 1))
    (h1 : i ≠ sLD D.wf.program CellTables.wf.program CellsProc.wf.program) (h2 : i ≠ sLK D.wf.program CellTables.wf.program CellsProc.wf.program)
    (h3 : i ≠ sLO D.wf.program CellTables.wf.program CellsProc.wf.program) : lensOf D CellTables CellsProc c w i = 0 := by
  simp [lensOf, h1, h2, h3]

theorem lensOf_OUT (c : Call) (w : List Bool) :
    lensOf D CellTables CellsProc c w (sOUT D.wf.program CellTables.wf.program CellsProc.wf.program) = 0 := by
  apply lensOf_zero <;> intro h <;> have := congrArg Fin.val h <;>
    simp [sOUT_val, sLD_val, sLK_val, sLO_val] at this

/-- **The counter program prints the counter's interval**, from the ideal start, on every (call, witness word). -/
theorem ctr_run (c : Call) (w : List Bool) :
    ∃ τ : WState (NSc D.wf.program CellTables.wf.program CellsProc.wf.program) 64,
      WXExec (capOf (B1 := B1) (B2 := B2) (cT := cT) c w) (ctrP D.wf.program CellTables.wf.program CellsProc.wf.program cT)
        (idealStart _ 64 (frame (callWord c) ++ frame w) (lensOf D CellTables CellsProc c w)) τ (costOf D CellTables CellsProc c w) ∧
      τ.st (sOUT D.wf.program CellTables.wf.program CellsProc.wf.program) = outputWord (counterOnCall B1 B2 cT c w) := by
  have hlz := lensOf_zero D CellTables CellsProc c w
  cases hr : reqOf B1 B2 cT c w with
  | none =>
    have hD : dispatchWord B1 B2 cT c w = natWord 0 ++ (zeroVs (B1 := B1) (B2 := B2) (cT := cT) c w).flatMap natWord :=
      dispatch_zero hr
    obtain ⟨τ, e, hout⟩ := zero_run (RD := Call × List Bool) D.wf CellTables.wf.program CellsProc.wf.program (c, w) cT
      (zeroVs (B1 := B1) (B2 := B2) (cT := cT) c w) hD (lensOf D CellTables CellsProc c w) (lensOf_LD D CellTables CellsProc c w) hlz
      (capOf (B1 := B1) (B2 := B2) (cT := cT) c w) (by simp [capOf, hr])
    refine ⟨τ, by simpa [costOf, hr] using e, ?_⟩
    rw [hout, zeroVs, List.flatMap_append, CounterMachine.ratN_word, CounterMachine.ratN_word]; rfl
  | some r =>
    obtain ⟨hrc, hdisp, hval⟩ := reqOf_some hr
    obtain ⟨S, hS, hfit, hivl⟩ := req_ivl r
    have hLK : lensOf D CellTables CellsProc c w (sLK D.wf.program CellTables.wf.program CellsProc.wf.program) = CellTables.budget r := by
      have : sLK D.wf.program CellTables.wf.program CellsProc.wf.program ≠ sLD D.wf.program CellTables.wf.program CellsProc.wf.program := by
        intro h; have := congrArg Fin.val h; simp [sLK_val, sLD_val] at this
      simp [lensOf, this, hr]
    have hLO : lensOf D CellTables CellsProc c w (sLO D.wf.program CellTables.wf.program CellsProc.wf.program) = CellsProc.budget r := by
      have h1 : sLO D.wf.program CellTables.wf.program CellsProc.wf.program ≠ sLD D.wf.program CellTables.wf.program CellsProc.wf.program := by
        intro h; have := congrArg Fin.val h; simp [sLO_val, sLD_val] at this
      have h2 : sLO D.wf.program CellTables.wf.program CellsProc.wf.program ≠ sLK D.wf.program CellTables.wf.program CellsProc.wf.program := by
        intro h; have := congrArg Fin.val h; simp [sLO_val, sLK_val] at this
      simp [lensOf, h1, h2, hr]
    obtain ⟨τ, e, hout⟩ := cell_run (RD := Call × List Bool) D.wf CellTables.wf CellsProc.wf (c, w) r r cT r.c.n S
      (uncCount r.c r.p r.wt) (CounterMachine.cellN r.c r.p r.wt).tail (recsOf r) (recsOf_ne r)
      (dispatch_cell hr) (cellInput_eq r) (cellWord_eq r) rfl
      (by simp only [hS]) hfit (lensOf D CellTables CellsProc c w) (lensOf_LD D CellTables CellsProc c w) hLK hLO hlz
      (capOf (B1 := B1) (B2 := B2) (cT := cT) c w) (by simp [capOf, hr])
    refine ⟨τ, by simpa [costOf, hr] using e, ?_⟩
    rw [hout, hivl, hval]

/-- **The counter program as a word function** (budget `2·cost + 2`). -/
noncomputable def ctrWF : WordFunction (Call × List Bool) (fun r => frame (callWord r.1) ++ frame r.2)
    (fun r => outputWord (counterOnCall B1 B2 cT r.1 r.2)) (fun r => 2 * costOf D CellTables CellsProc r.1 r.2 + 2) :=
  Expand.PolyTab.wordFunction_of_ideal (ctrP D.wf.program CellTables.wf.program CellsProc.wf.program cT)
    (sOUT D.wf.program CellTables.wf.program CellsProc.wf.program) (by rw [sOUT_val]; decide)
    (fun r => capOf (B1 := B1) (B2 := B2) (cT := cT) r.1 r.2) (fun r => lensOf D CellTables CellsProc r.1 r.2)
    (fun r => costOf D CellTables CellsProc r.1 r.2) (fun _ => le_rfl)
    (fun r => ⟨lensOf_OUT D CellTables CellsProc r.1 r.2, ctr_run D CellTables CellsProc r.1 r.2⟩)

end Pack

/-! ## Step 4a: arithmetic for `fast` -/

theorem two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases Nat.lt_or_ge 1 m with h | h
  · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    rw [Nat.pred_eq_sub_one] at this
    have hc : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    calc 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * m := by omega
  · have : m = 1 := by omega
    subst this; simp

theorem two_pow_Jmax_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ (2 * Jmax n) ≤ 16 * n ^ 2 := by
  unfold Jmax Target.mu
  have hl : Target.lambda n ≤ n := by
    unfold Target.lambda; exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have h1 : 2 ^ Nat.clog 2 (Target.lambda n) ≤ 2 * n := by
    rcases Nat.eq_zero_or_pos (Target.lambda n) with h0 | hpos
    · rw [h0]; simp; omega
    · exact (two_pow_clog_le _ hpos).trans (by omega)
  calc 2 ^ (2 * (Nat.clog 2 (Target.lambda n) + 1)) = 4 * (2 ^ Nat.clog 2 (Target.lambda n)) ^ 2 := by ring
    _ ≤ 4 * (2 * n) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
    _ = 16 * n ^ 2 := by ring

/-- `(n+1)^{2J+e} ≤ 16·2^e · n^{2J+e+2}` for `n ≥ 1`. -/
theorem succ_pow_le (n e : ℕ) (hn : 1 ≤ n) :
    (n + 1) ^ (2 * Jmax n + e) ≤ 16 * 2 ^ e * n ^ (2 * Jmax n + (e + 2)) := by
  have h2n : n + 1 ≤ 2 * n := by omega
  calc (n + 1) ^ (2 * Jmax n + e) ≤ (2 * n) ^ (2 * Jmax n + e) := Nat.pow_le_pow_left h2n _
    _ = 2 ^ (2 * Jmax n) * 2 ^ e * n ^ (2 * Jmax n + e) := by rw [mul_pow, pow_add]
    _ ≤ 16 * n ^ 2 * 2 ^ e * n ^ (2 * Jmax n + e) := by
        gcongr; exact two_pow_Jmax_le n hn
    _ = 16 * 2 ^ e * n ^ (2 * Jmax n + (e + 2)) := by ring

/-! ## Step 4b: the call word is polynomial in `n` for admitted calls -/

def callBound (B2 n : ℕ) : ℕ :=
  (14 + (n + 1) + 4 * (n + 1) ^ 4 * (2 * (n + 1) + 7)) *
    (2 * (4 * (n + 1) ^ 2 + 4 * (n + 1) ^ 4 + 2 * (n + 1) + 4 + (n + 1) ^ B2) + 1)

theorem callWord_le {B1 B2 : ℕ} (c : Call) (hadm : c.Admitted B1 B2) : (callWord c).length ≤ callBound B2 c.n := by
  rw [← CounterMachine.callN_word]
  refine (NearCubicGates.Close.Cells.flat_len_le _ _ (NearCubicGates.Close.Cells.call_bits c hadm)).trans ?_
  exact Nat.mul_le_mul (NearCubicGates.Close.Cells.call_len c hadm) le_rfl

theorem pb_succ_pow (k : ℕ) : PolynomiallyBounded (fun n => (n + 1) ^ k) :=
  polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) k

theorem callBound_poly (B2 : ℕ) : PolynomiallyBounded (callBound B2) := by
  have h1 : PolynomiallyBounded (fun n => n + 1) :=
    polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)
  unfold callBound
  refine polynomiallyBounded_mul ?_ ?_
  · exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_constant 14) h1)
      (polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (pb_succ_pow 4))
        (polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2) h1)
          (polynomiallyBounded_constant 7)))
  · refine polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2) ?_)
      (polynomiallyBounded_constant 1)
    exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (pb_succ_pow 2))
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (pb_succ_pow 4)))
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2) h1)) (polynomiallyBounded_constant 4)) (pb_succ_pow B2)

/-! ## Step 4c: the budget on each path -/

theorem two_pow_nbl_le (n : ℕ) : 2 ^ natBitLength n ≤ 2 * (n + 1) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    rw [pow_succ]; omega

theorem nbl_le (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 n; omega

theorem kOf_le (cT n : ℕ) : kOf cT n ≤ (3 * n + cT + 2) * n := by
  unfold kOf
  have h1 := lamOf_le n
  have h2 := (muOf_le n).trans h1
  exact Nat.mul_le_mul (by omega) h1

/-- The polynomial part of the counter's budget (both paths), at fixed `cT` and fixed classes. -/
def polyAll (B2 cT CD eD CI eI n : ℕ) : ℕ :=
  4 * (CD * (callBound B2 n + 1) ^ eD) + 2 * (100 * (CI * (n + 1) ^ eI) + 100 + (n + 3) * (80 * (n + 1) + 40)) +
    800 * (CI * (n + 1) ^ eI) + 20000 * (n + (3 * n + cT + 2) * n + cT + 10) ^ 2 + 1602 + 60 * (8 * n + 30) + 42

theorem polyAll_poly (B2 cT CD eD CI eI : ℕ) : PolynomiallyBounded (polyAll B2 cT CD eD CI eI) := by
  have h1 : PolynomiallyBounded (fun n => n + 1) :=
    polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)
  have hc := polynomiallyBounded_add (callBound_poly B2) (polynomiallyBounded_constant 1)
  have hI : PolynomiallyBounded (fun n => CI * (n + 1) ^ eI) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant CI) (pb_succ_pow eI)
  unfold polyAll
  refine polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add (polynomiallyBounded_add ?_ ?_) ?_) ?_) (polynomiallyBounded_constant 1602)) ?_)
    (polynomiallyBounded_constant 42)
  · exact polynomiallyBounded_mul (polynomiallyBounded_constant 4)
      (polynomiallyBounded_mul (polynomiallyBounded_constant CD) (polynomiallyBounded_pow hc eD))
  · refine polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_add
      (polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 100) hI)
        (polynomiallyBounded_constant 100)) (polynomiallyBounded_mul
          (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 3))
          (polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 80) h1)
            (polynomiallyBounded_constant 40))))
  · exact polynomiallyBounded_mul (polynomiallyBounded_constant 800) hI
  · refine polynomiallyBounded_mul (polynomiallyBounded_constant 20000) (polynomiallyBounded_pow ?_ 2)
    exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add polynomiallyBounded_id
      (polynomiallyBounded_mul (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_mul
        (polynomiallyBounded_constant 3) polynomiallyBounded_id) (polynomiallyBounded_constant cT))
        (polynomiallyBounded_constant 2)) polynomiallyBounded_id)) (polynomiallyBounded_constant cT))
      (polynomiallyBounded_constant 10)
  · exact polynomiallyBounded_mul (polynomiallyBounded_constant 60) (polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_constant 8) polynomiallyBounded_id)
      (polynomiallyBounded_constant 30))

section Budget
variable {B1 B2 cT : ℕ} (D : DispatchMachine B1 B2 cT) (CellTables : TablesMachine B1 B2 cT) (CellsProc : CellsMachine B1 B2 cT)

theorem zeroVs_len (c : Call) (w : List Bool) :
    ((zeroVs (B1 := B1) (B2 := B2) (cT := cT) c w).flatMap natWord).length ≤ 8 * c.n + 30 := by
  rw [zeroVs, List.flatMap_append, CounterMachine.ratN_word, CounterMachine.ratN_word]
  exact counterOnCall_outLen B1 B2 cT c w

/-- The final-answer path's budget. -/
theorem budget_zero {CD eD : ℕ} (hD : ∀ c w, D.budget c w ≤ CD * ((callWord c).length + 1) ^ eD) (CI eI : ℕ)
    (c : Call) (w : List Bool) (hadm : c.Admitted B1 B2) (hr : reqOf B1 B2 cT c w = none) :
    2 * costOf D CellTables CellsProc c w + 2 ≤ polyAll B2 cT CD eD CI eI c.n := by
  have h1 : D.budget c w ≤ CD * (callBound B2 c.n + 1) ^ eD :=
    (hD c w).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := callWord_le c hadm; omega) _))
  have h2 := zeroVs_len (B1 := B1) (B2 := B2) (cT := cT) c w
  simp only [costOf, hr, zeroCost]
  unfold polyAll
  omega

/-- The cell path's budget: the polynomial part plus the two cell machines' budgets. -/
theorem budget_cell {CD eD : ℕ} (hD : ∀ c w, D.budget c w ≤ CD * ((callWord c).length + 1) ^ eD) {CI eI : ℕ}
    (hI : ∀ r : CellReq B1 B2 cT, (cellInput r).length ≤ CI * (r.c.n + 1) ^ eI)
    (c : Call) (w : List Bool) (r : CellReq B1 B2 cT) (hr : reqOf B1 B2 cT c w = some r) :
    2 * costOf D CellTables CellsProc c w + 2 ≤ polyAll B2 cT CD eD CI eI c.n + 804 * CellTables.budget r + 4 * CellsProc.budget r := by
  obtain ⟨hrc, -, -⟩ := reqOf_some hr
  subst hrc
  have h1 : D.budget r.c w ≤ CD * (callBound B2 r.c.n + 1) ^ eD :=
    (hD r.c w).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := callWord_le r.c r.adm; omega) _))
  have hL : ((r.c.n :: (CounterMachine.cellN r.c r.p r.wt).tail).flatMap natWord).length ≤ CI * (r.c.n + 1) ^ eI := by
    rw [← cellInput_eq]; exact hI r
  have hF : ((recsOf r).flatMap frame).length ≤ CellTables.budget r := by
    have := NearCubicGates.Close.Cells.wf_out_len CellTables.wf r
    simp only [cellWord_eq, List.length_append, List.length_singleton] at this
    omega
  have hn := nbl_le r.c.n
  have hp := two_pow_nbl_le r.c.n
  have hk := kOf_le cT r.c.n
  have hin : inKCost ((r.c.n :: (CounterMachine.cellN r.c r.p r.wt).tail).flatMap natWord).length r.c.n ≤
      100 * (CI * (r.c.n + 1) ^ eI) + 100 + (r.c.n + 3) * (80 * (r.c.n + 1) + 40) := by
    unfold inKCost
    have : (natBitLength r.c.n + 2) * (40 * 2 ^ natBitLength r.c.n + 40) ≤ (r.c.n + 3) * (80 * (r.c.n + 1) + 40) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have ht : tailCost cT r.c.n ≤ 10000 * (r.c.n + (3 * r.c.n + cT + 2) * r.c.n + cT + 10) ^ 2 := by
    unfold tailCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  simp only [costOf, hr, cellCost]
  unfold polyAll
  omega

end Budget

/-! ## Step 4d: `fast` and `rest` -/

section Time
variable {B1 B2 cT : ℕ} (D : DispatchMachine B1 B2 cT) (CellTables : TablesMachine B1 B2 cT) (CellsProc : CellsMachine B1 B2 cT)

theorem fast_of {CD eD : ℕ} (hD : ∀ c w, D.budget c w ≤ CD * ((callWord c).length + 1) ^ eD) {CI eI : ℕ}
    (hI : ∀ r : CellReq B1 B2 cT, (cellInput r).length ≤ CI * (r.c.n + 1) ^ eI) {e CK CO : ℕ}
    (hK : ∀ r : CellReq B1 B2 cT, CellTables.budget r ≤ CK * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e))
    (hO : ∀ r : CellReq B1 B2 cT, CellsProc.budget r ≤ CO * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e))
    (hcT : e + 4 ≤ cT) :
    ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 → ∀ w : List Bool,
      (2 * costOf D CellTables CellsProc c w + 2) * c.n ^ Target.mu c.n ≤ 2 ^ c.n := by
  obtain ⟨A, a, -, hA⟩ := polyAll_poly B2 cT CD eD CI eI
  obtain ⟨o1, h1⟩ := poly_fits_clock (2 * A) a
  set B := (804 * CK + 4 * CO) * (16 * 2 ^ e) with hB
  refine ⟨o1 + 2 * B + 1, fun c hn hadm w => ?_⟩
  have hn1 : 1 ≤ c.n := by omega
  have hpoly : 2 * (A * (c.n + 1) ^ a * c.n ^ Target.mu c.n) ≤ 2 ^ c.n := by
    have := h1 c.n (by omega); nlinarith
  cases hr : reqOf B1 B2 cT c w with
  | none =>
    have hb := (budget_zero D CellTables CellsProc hD CI eI c w hadm hr).trans (hA c.n)
    calc (2 * costOf D CellTables CellsProc c w + 2) * c.n ^ Target.mu c.n ≤ A * (c.n + 1) ^ a * c.n ^ Target.mu c.n :=
          Nat.mul_le_mul_right _ hb
      _ ≤ 2 ^ c.n := by omega
  | some r =>
    obtain ⟨hrc, -, -⟩ := reqOf_some hr
    have hb := budget_cell D CellTables CellsProc hD hI c w r hr
    have hs := selectParams_spec cT (header r.c) r.p r.hp
    have hsucc := succ_pow_le r.c.n e (by rw [hrc]; exact hn1)
    have hbig : 804 * CellTables.budget r + 4 * CellsProc.budget r ≤
        B * (2 ^ (r.c.n - r.p.k) * r.c.n ^ (2 * Jmax r.c.n + (e + 2))) := by
      have hk := hK r
      have ho := hO r
      have hX : 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e) ≤
          16 * 2 ^ e * (2 ^ (r.c.n - r.p.k) * r.c.n ^ (2 * Jmax r.c.n + (e + 2))) := by
        calc 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e)
            ≤ 2 ^ (r.c.n - r.p.k) * (16 * 2 ^ e * r.c.n ^ (2 * Jmax r.c.n + (e + 2))) := Nat.mul_le_mul_left _ hsucc
          _ = 16 * 2 ^ e * (2 ^ (r.c.n - r.p.k) * r.c.n ^ (2 * Jmax r.c.n + (e + 2))) := by ring
      rw [mul_assoc] at hk ho
      generalize 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e) = Y at hk ho hX
      generalize 2 ^ (r.c.n - r.p.k) * r.c.n ^ (2 * Jmax r.c.n + (e + 2)) = X at hX ⊢
      rw [hB]
      calc 804 * CellTables.budget r + 4 * CellsProc.budget r ≤ 804 * (CK * Y) + 4 * (CO * Y) := by omega
        _ = (804 * CK + 4 * CO) * Y := by ring
        _ ≤ (804 * CK + 4 * CO) * (16 * 2 ^ e * X) := Nat.mul_le_mul_left _ hX
        _ = (804 * CK + 4 * CO) * (16 * 2 ^ e) * X := by ring
    have htb := time_budget r.c r.p hs (e + 2) (2 * B) (by omega) (by
      rw [hrc]; nlinarith)
    rw [hrc] at hbig htb
    have hpa := hA c.n
    calc (2 * costOf D CellTables CellsProc c w + 2) * c.n ^ Target.mu c.n
        ≤ (A * (c.n + 1) ^ a + B * (2 ^ (c.n - r.p.k) * c.n ^ (2 * Jmax c.n + (e + 2)))) * c.n ^ Target.mu c.n := by
          apply Nat.mul_le_mul_right; omega
      _ = A * (c.n + 1) ^ a * c.n ^ Target.mu c.n +
            B * (2 ^ (c.n - r.p.k) * c.n ^ (2 * Jmax c.n + (e + 2))) * c.n ^ Target.mu c.n := by ring
      _ ≤ 2 ^ c.n := by
          have : 2 * (B * (2 ^ (c.n - r.p.k) * c.n ^ (2 * Jmax c.n + (e + 2))) * c.n ^ Target.mu c.n) ≤ 2 ^ c.n := by
            calc 2 * (B * (2 ^ (c.n - r.p.k) * c.n ^ (2 * Jmax c.n + (e + 2))) * c.n ^ Target.mu c.n)
                = 2 * B * (2 ^ (c.n - r.p.k) * c.n ^ (2 * Jmax c.n + (e + 2))) * c.n ^ Target.mu c.n := by ring
              _ ≤ 2 ^ c.n := htb
          omega

theorem rest_of {CD eD : ℕ} (hD : ∀ c w, D.budget c w ≤ CD * ((callWord c).length + 1) ^ eD) :
    ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), ¬ c.Admitted B1 B2 →
      2 * costOf D CellTables CellsProc c w + 2 ≤ K * ((callWord c).length + 1) ^ e := by
  refine ⟨4 * CD + 1602, eD, fun c w hna => ?_⟩
  have hr : reqOf B1 B2 cT c w = none := by
    unfold reqOf; rw [dif_neg (fun h => hna h.1)]
  have hv : counterOnCall B1 B2 cT c w = defaultValue := by
    unfold counterOnCall; rw [if_neg hna]
  have hL : ((zeroVs (B1 := B1) (B2 := B2) (cT := cT) c w).flatMap natWord).length ≤ 26 := by
    rw [zeroVs, List.flatMap_append, CounterMachine.ratN_word, CounterMachine.ratN_word, hv]
    exact pair_len_le _ len_half len_half
  have h1 : 1 ≤ ((callWord c).length + 1) ^ eD := Nat.one_le_pow _ _ (by omega)
  have hd := hD c w
  simp only [costOf, hr, zeroCost]
  generalize ((callWord c).length + 1) ^ eD = Z at hd h1 ⊢
  nlinarith

end Time

/-! ## Step 5: `O1asm_of` and `counterSupply_of` -/

theorem counterOfProducers : CounterOfProducersStatement := by
  intro s B1 B2 hB1 hB2 D CellTables CellsProc hK6 hCellsProc
  obtain ⟨eK, hK⟩ := hK6
  obtain ⟨eO, hO⟩ := hCellsProc
  set e := eK + eO with he
  set cT := e + 4 with hcT
  obtain ⟨CK, hCK⟩ := hK cT
  obtain ⟨CO, hCO⟩ := hO cT
  have hK' : ∀ r : CellReq B1 B2 cT, (CellTables cT).budget r ≤ CK * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e) :=
    fun r => (hCK r).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have hO' : ∀ r : CellReq B1 B2 cT, (CellsProc cT).budget r ≤ CO * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e) :=
    fun r => (hCO r).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  obtain ⟨CD, eD, hD⟩ := (D cT).cls
  obtain ⟨CI, eI, hI⟩ := NearCubicGates.Close.Cells.cellInput_length_le B1 B2 cT
  have fast := fast_of (D cT) (CellTables cT) (CellsProc cT) hD hI hK' hO' (by omega)
  have rest := rest_of (D cT) (CellTables cT) (CellsProc cT) hD
  exact ⟨counterOfMachine s.restriction s.bernstein s.primes B1 B2 cT (by omega) (by omega)
      (fun c w => 2 * costOf (D cT) (CellTables cT) (CellsProc cT) c w + 2) (ctrWF (D cT) (CellTables cT) (CellsProc cT)) fast rest,
    counterOfMachine_denOK _ _ _ _ _ _ _ _ _ _ _ _,
    counterOfMachine_outOK _ _ _ _ _ _ _ _ _ _ _ _⟩

theorem counterSupply_of (h : CounterInputsAll) : Closure.CounterSupply :=
  counterSupply_of_statement counterOfProducers h

end NearCubicGates.Close.CounterAsm
