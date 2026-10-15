import Proof.Wire_3_5.PrimAsmRecords
import Proof.Wire_3_5.PrimAsmUnaryArith
import Proof.Wire_3_5.PrimAsmWriteNat

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass

/-! ## Marks -/

theorem frame_eq (w : List Bool) : frame w = Streaming.marks w ++ [false] := by
  have h := Streaming.frame_append w []
  simpa [frame] using h

theorem marks_eq (w : List Bool) : Streaming.marks w = w.flatMap fun b => [true, b] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [Streaming.marks]

theorem marks_append' (u v : List Bool) : Streaming.marks (u ++ v) = Streaming.marks u ++ Streaming.marks v := by
  rw [marks_eq, marks_eq, marks_eq, List.flatMap_append]

/-- A bit at marks-level 2. -/
def m2 (b : Bool) : List Bool := [true, true, true, b]

/-- A bit at marks-level 3. -/
def m3 (b : Bool) : List Bool := [true, true, true, true, true, true, true, b]

theorem marks2 (w : List Bool) : Streaming.marks (Streaming.marks w) = w.flatMap m2 := by
  rw [marks_eq, marks_eq, List.flatMap_assoc]
  refine List.flatMap_congr fun b _ => ?_
  simp [m2]

/-- `n` copies of a word. -/
def reps (n : ℕ) (u : List Bool) : List Bool := (List.replicate n u).flatten

@[simp] theorem reps_zero (u : List Bool) : reps 0 u = [] := rfl

theorem reps_succ (n : ℕ) (u : List Bool) : reps (n + 1) u = reps n u ++ u := by
  unfold reps; rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]

theorem flatMap_replicate (n : ℕ) (b : Bool) (f : Bool → List Bool) : (List.replicate n b).flatMap f = reps n (f b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', List.flatMap_append, ih, reps_succ]; simp

/-- A field at level 2 with its frame end. -/
def fieldE (f : List Bool) : List Bool := f.flatMap m2 ++ [true, false]

theorem frame_fieldsWord (ws : List (List Bool)) : frame (fieldsWord ws) = ws.flatMap fieldE ++ [false] := by
  rw [frame_eq]
  congr 1
  unfold fieldsWord
  induction ws with
  | nil => rfl
  | cons f ws ih =>
    rw [List.flatMap_cons, marks_append', ih, List.flatMap_cons, frame_eq, marks_append', marks2]
    simp [fieldE, Streaming.marks]

theorem fieldE_frameZeros (n : ℕ) : fieldE (frame (List.replicate n false)) = reps n (m3 false) ++ m2 false ++ [true, false] := by
  unfold fieldE
  rw [frame_eq, List.flatMap_append, marks_eq, List.flatMap_assoc, flatMap_replicate]
  simp [m2, m3]

theorem fieldE_bit (b : Bool) : fieldE [b] = m2 b ++ [true, false] := by simp [fieldE]

theorem fieldE_ones (n : ℕ) : fieldE (List.replicate n true ++ [false]) = reps n (m2 true) ++ m2 false ++ [true, false] := by
  unfold fieldE; rw [List.flatMap_append, flatMap_replicate]; simp

theorem fieldE_zeros (n : ℕ) : fieldE (List.replicate n false) = reps n (m2 false) ++ [true, false] := by
  unfold fieldE; rw [flatMap_replicate]

/-- A label at level 2: `lab` ones and the code's end. -/
def labE (lab : ℕ) : List Bool := reps lab (m2 true) ++ m2 false

theorem fieldE_labels (labs : List ℕ) :
    fieldE (ListMachine.Row.labelWord labs) = labs.flatMap labE ++ m2 false ++ [true, false] := by
  unfold fieldE ListMachine.Row.labelWord
  rw [List.flatMap_append, List.flatMap_assoc]
  congr 2
  refine List.flatMap_congr fun lab _ => ?_
  unfold ListMachine.Rec.atomCode labE
  rw [List.flatMap_append, flatMap_replicate]; simp

/-! ## The schedule -/

/-- **The FILTER row's input word, field by field** (point length `Lp = 4L`, degree `d`, log `cap1`, threshold `thr`,
register capacity `c`, the table word `tw`, the labels `labs`). -/
def filtEmit (Lp d cap1 thr c : ℕ) (tw : List Bool) (labs : List ℕ) : List Bool :=
  (reps Lp (m3 false) ++ m2 false ++ [true, false]) ++ (reps Lp (m3 false) ++ m2 false ++ [true, false]) ++
  (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++
  (m2 true ++ [true, false]) ++ (m2 false ++ [true, false]) ++
  (reps Lp (m3 false) ++ m2 false ++ [true, false]) ++ (reps Lp (m3 false) ++ m2 false ++ [true, false]) ++
  (reps d (m2 true) ++ m2 false ++ [true, false]) ++
  (labs.flatMap labE ++ m2 false ++ [true, false]) ++
  (reps cap1 (m2 false) ++ [true, false]) ++ [true, false] ++
  (tw.flatMap m2 ++ [true, false]) ++
  (reps thr (m2 true) ++ m2 false ++ [true, false]) ++
  (reps (c + 1) (m2 false) ++ [true, false]) ++
  (m2 true ++ [true, false]) ++
  (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++
  (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++
  (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++
  (reps (c + 1) (m2 false) ++ [true, false]) ++ [false]

theorem goods_pos (L d : ℕ) : decide (0 < (Interp.goods L d).length) = true := by
  apply decide_eq_true
  apply List.length_pos_of_mem (a := 0)
  unfold Interp.goods
  refine List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.two_pow_pos L), ?_⟩
  unfold Interp.good
  rw [decide_eq_true_eq]
  rw [Interp.binary_zero]
  simp [Interp.pop, List.count_replicate]

theorem unary_eq (n : ℕ) : ListEval.unary n = List.replicate n true ++ [false] := rfl

/-- C5's stage-3∘7 data tapes, listed. -/
theorem stage37Data_list (tbl : List (List (List Bool))) (thr : ℕ) (sgn : Bool) (c : ℕ) :
    List.ofFn (Filt.stage37Data tbl thr sgn c) =
      [Filt.tableWord tbl, ListEval.unary thr, List.replicate (c + 1) false, [sgn], List.replicate (c + 1) false,
        List.replicate (c + 1) false, List.replicate (c + 1) false, List.replicate (c + 1) false,
        List.replicate (c + 1) false, List.replicate (c + 1) false, List.replicate (c + 1) false] := by
  simp [List.ofFn_succ, Filt.stage37Data]

/-- **The FILTER row's input word is the schedule.** -/
theorem filtEmit_eq (tbl : List (List (List Bool))) (thr L : ℕ) (labs : List ℕ) :
    frame (filtRecC tbl thr L true labs) =
      filtEmit (4 * L) (filtDeg tbl) (cap1C L labs) thr (cap37 tbl thr L) (Filt.tableWord tbl) labs := by
  unfold filtRecC filterRecord factorBlock
  rw [frame_fieldsWord]
  unfold factorFields
  have hx : Print.xsAt (4 * L) (filtDeg tbl) 0 = List.replicate (4 * L) false := by
    unfold Print.xsAt
    simp only [Function.iterate_zero, id]
    exact Interp.binary_zero _
  rw [hx, goods_pos, stage37Data_list, unary_eq]
  simp only [List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    fieldE_frameZeros, fieldE_bit, fieldE_ones, fieldE_zeros, fieldE_labels, reps_zero]
  unfold fieldE filtEmit
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-! ## The numbers of C5's table -/

/-- The label field's log capacity: `5 + Σ_{lab} (2·lab + 10)`. -/
def labSum (labs : List ℕ) : ℕ := 5 + (labs.map fun lab => 2 * lab + 10).sum

theorem loopL_sum (labs : List ℕ) :
    ((List.range labs.length).map fun i => Print.bodyLCost (labs.getD i 0) + 2).sum =
      (labs.map fun lab => 2 * lab + 10).sum := by
  rw [Records.range_map_getD labs 0 (fun lab => Print.bodyLCost lab + 2)]
  congr 1
  refine List.map_congr_left fun lab _ => ?_
  unfold Print.bodyLCost; omega

theorem labCost_eq (labs : List ℕ) : labCost labs.length labs = labSum labs := by
  unfold labCost Print.recInnerLCost Print.loopLCost labSum
  rw [List.length_replicate, loopL_sum]
  omega

theorem labSum_ge (labs : List ℕ) : 10 * labs.length ≤ (labs.map fun lab => 2 * lab + 10).sum := by
  induction labs with
  | nil => simp
  | cons x xs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- **The FILTER record's label log** is the label sum (it exceeds `2·(4L) + 1`). -/
theorem cap1C_eq (L : ℕ) (labs : List ℕ) (h : labs.length = 4 * L) : cap1C L labs = labSum labs := by
  unfold cap1C
  rw [← h, labCost_eq]
  have hs := labSum_ge labs
  unfold labSum
  omega

theorem copyWord_length (cs : List Bool) : (Filt.copyWord cs).length = 2 * cs.length + 2 := by
  unfold Filt.copyWord
  rw [List.length_cons, frame_eq, List.length_append, marks_eq, List.length_flatMap]
  simp; ring

theorem filterTable_visit (P : Filters.GapParams) (e : Filters.GapSeed P) (L : ℕ) :
    ∀ vs ∈ Filt.filterTable P e L, vs.length = 128 ∧ ∀ cs ∈ vs, cs.length = L := by
  intro vs hvs
  refine ⟨?_, fun cs hcs => Filt.filterTable_lengths P e L vs hvs cs hcs⟩
  simp only [Filt.filterTable, List.mem_map] at hvs
  obtain ⟨i, _, rfl⟩ := hvs
  simp

/-- **The table word's length**: `walkLen` visits of `128` copies of `L`-bit coefficient words. -/
theorem tableWord_length (P : Filters.GapParams) (e : Filters.GapSeed P) (L : ℕ) :
    (Filt.tableWord (Filt.filterTable P e L)).length = P.walkLen * (256 * L + 258) + 1 := by
  have hv : ∀ vs ∈ Filt.filterTable P e L, (Filt.visitWord vs).length = 256 * L + 258 := by
    intro vs hvs
    obtain ⟨h128, hL⟩ := filterTable_visit P e L vs hvs
    unfold Filt.visitWord
    rw [List.length_cons, List.length_append, List.length_flatMap, List.length_singleton]
    have : (vs.map fun cs => (Filt.copyWord cs).length) = vs.map fun _ => 2 * L + 2 :=
      List.map_congr_left fun cs hcs => by rw [copyWord_length, hL cs hcs]
    rw [this, List.map_const', List.sum_replicate, h128]
    simp; ring
  unfold Filt.tableWord
  rw [List.length_append, List.length_flatMap, List.length_singleton]
  have : ((Filt.filterTable P e L).map fun vs => (Filt.visitWord vs).length) =
      (Filt.filterTable P e L).map fun _ => 256 * L + 258 := List.map_congr_left hv
  rw [this, List.map_const', List.sum_replicate]
  simp [Filt.filterTable]

theorem vmax_const (tbl : List (List (List Bool))) (k : ℕ) (h : ∀ vs ∈ tbl, vs.length = k) (hne : tbl ≠ []) :
    vmax tbl = k := by
  induction tbl with
  | nil => exact absurd rfl hne
  | cons v tbl ih =>
    unfold vmax
    simp only [List.map_cons, List.foldr_cons]
    rw [h v List.mem_cons_self]
    by_cases ht : tbl = []
    · subst ht; simp
    · have := ih (fun vs hvs => h vs (List.mem_cons_of_mem v hvs)) ht
      unfold vmax at this
      rw [this, max_self]

/-- **The interpolation degree of C5's table**: `3·(128·walkLen) + 1`. -/
theorem filtDeg_filterTable (P : Filters.GapParams) (e : Filters.GapSeed P) (L : ℕ) :
    filtDeg (Filt.filterTable P e L) = 384 * P.walkLen + 1 := by
  unfold filtDeg
  have hne : Filt.filterTable P e L ≠ [] := by
    unfold Filt.filterTable
    simp [Filters.GapParams.walkLen]
  rw [vmax_const _ 128 (fun vs hvs => (filterTable_visit P e L vs hvs).1) hne]
  simp [Filt.filterTable]
  ring

/-- **The stage-7 register capacity of C5's table.** -/
theorem cap37_filterTable (P : Filters.GapParams) (e : Filters.GapSeed P) (L thr : ℕ) :
    cap37 (Filt.filterTable P e L) thr L = P.walkLen * (256 * L + 258) + 1 + 2 * L + thr + 40 := by
  unfold cap37 Filt.capOf7
  rw [tableWord_length]

end NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
