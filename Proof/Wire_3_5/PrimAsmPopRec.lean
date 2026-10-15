import Proof.Wire_3_5.PrimAsmFiltRecW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopRec
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW

/-! ## Marks -/

theorem marks_fieldsWord (ws : List (List Bool)) : Streaming.marks (fieldsWord ws) = ws.flatMap fieldE := by
  unfold fieldsWord
  induction ws with
  | nil => rfl
  | cons f ws ih =>
    rw [List.flatMap_cons, marks_append', ih, List.flatMap_cons, frame_eq, marks_append', marks2]
    simp [fieldE, Streaming.marks]

theorem marks_cons (b : Bool) (w : List Bool) : Streaming.marks (b :: w) = [true, b] ++ Streaming.marks w := by
  rw [marks_eq, marks_eq]; rfl

theorem marks_flatMap {α : Type} (l : List α) (f : α → List Bool) :
    Streaming.marks (l.flatMap f) = l.flatMap fun a => Streaming.marks (f a) := by
  rw [marks_eq, List.flatMap_assoc]
  exact List.flatMap_congr fun a _ => (marks_eq (f a)).symm

theorem marks_frame (w : List Bool) : Streaming.marks (frame w) = w.flatMap m2 ++ [true, false] := by
  rw [frame_eq, marks_append', marks2]; rfl

theorem flatMap_replicate_gen {α : Type} (n : ℕ) (a : α) (f : α → List Bool) :
    (List.replicate n a).flatMap f = reps n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', List.flatMap_append, ih, reps_succ]; simp

/-! ## A factor block -/

/-- The stage-3∘5 data fields and the negation flag (the table word `lvE` given at level 2). -/
def pieceP (lvE : List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) (neg : Bool) : List Bool :=
  (lvE ++ [true, false]) ++ (reps s (m2 true) ++ (m2 false ++ [true, false])) ++
  (reps (c + 1) (m2 false) ++ [true, false]) ++ (m2 sgn ++ [true, false]) ++
  reps 15 (reps (c + 1) (m2 false) ++ [true, false]) ++ (m2 neg ++ [true, false])

/-- **A POP factor block, emitted**: its marker, the FILTER bank's first fields, the stage-3∘5 data. -/
def blockE (Lp d cap1 : ℕ) (labs : List ℕ) (lvE : List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) (neg : Bool) :
    List Bool :=
  [true, true] ++ (pieceA Lp d ++ (pieceB labs cap1 ++ pieceP lvE s sgn c neg))

theorem stage35Data_list (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) :
    List.ofFn (Pop.stage35Data M J W row s sgn c) =
      [ListEval.levelWord M J W row, ListEval.unary s, List.replicate (c + 1) false, [sgn]] ++
        List.replicate 15 (List.replicate (c + 1) false) := by
  simp [List.ofFn_succ, Pop.stage35Data, List.replicate_succ]

theorem dataC_list (D : ListData) (L s : ℕ) (sgn neg : Bool) :
    List.ofFn (dataC D L s sgn neg) =
      List.ofFn (Pop.stage35Data D.M D.J D.W (ListEval.rowsOf D L) s sgn (capC D L)) ++ [[neg]] := by
  unfold dataC
  rw [List.ofFn_add]
  congr 1

/-- **The block's emission**: `marks (true :: blockC D L s sgn neg labs)` field by field. -/
theorem blockE_eq (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) :
    Streaming.marks (true :: blockC D L s sgn neg labs) =
      blockE (4 * L) (3 * listBound D) (cap1C L labs) labs
        ((ListEval.levelWord D.M D.J D.W (ListEval.rowsOf D L)).flatMap m2) s sgn (capC D L) neg := by
  rw [marks_cons]
  unfold blockC factorBlock
  rw [marks_fieldsWord]
  unfold factorFields
  have hx : Print.xsAt (4 * L) (3 * listBound D) 0 = List.replicate (4 * L) false := by
    unfold Print.xsAt
    simp only [Function.iterate_zero, id]
    exact Interp.binary_zero _
  rw [hx, goods_pos, dataC_list, stage35Data_list, unary_eq]
  simp only [List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
    fieldE_frameZeros, fieldE_bit, fieldE_ones, fieldE_zeros, fieldE_labels, reps_zero, flatMap_replicate_gen]
  unfold fieldE blockE pieceA pieceB pieceP
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, reps_zero]

/-! ## The record -/

/-- The setup fields, emitted (`n` visits, threshold `θ`, capacities `R`, `Lg`, `cap`). -/
def setupE (n θ R Lg cap : ℕ) : List Bool :=
  (reps R (m2 true) ++ [true, false]) ++ (reps Lg (m2 false) ++ [true, false]) ++
  (reps n (m3 false) ++ m2 false ++ [true, false]) ++ (reps n (m3 false) ++ m2 false ++ [true, false]) ++
  (reps θ (m2 true) ++ m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++
  [true, false] ++ (reps cap (m2 false) ++ [true, false])

theorem setupE_eq (u n θ R Lg cap : ℕ) : (setupFields u n θ R Lg cap).flatMap fieldE = setupE n θ R Lg cap := by
  rw [setupFields_eq]
  have hb : SignedSortKey.binary n 0 = List.replicate n false := Interp.binary_zero n
  rw [hb]
  simp only [List.flatMap_cons, List.flatMap_nil, fieldE_frameZeros, fieldE_bit, fieldE_ones, fieldE_zeros,
    List.append_nil]
  unfold fieldE setupE
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.flatMap_nil, flatMap_replicate]

/-- A state, emitted: its marker, its coefficient, its blocks `blks` (already emitted), the store's end. -/
def stateE (c : ℤ) (blks : List Bool) : List Bool :=
  [true, true] ++ (((Rec.coefWord c).flatMap m2 ++ [true, false]) ++ (blks ++ [true, false]))

/-- The blocks of visit `k` of state `s'`, emitted (`neg = true`, then `false`). -/
def visitE (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ) (s' : ℕ)
    (k : Fin P.walkLen) : List Bool :=
  blockE (4 * L) (3 * listBound (visitData P e k)) (cap1C L labs) labs
      ((ListEval.levelWord (visitData P e k).M (visitData P e k).J (visitData P e k).W
        (ListEval.rowsOf (visitData P e k) L)).flatMap m2) s' sgn (capC (visitData P e k) L) true ++
    blockE (4 * L) (3 * listBound (visitData P e k)) (cap1C L labs) labs
      ((ListEval.levelWord (visitData P e k).M (visitData P e k).J (visitData P e k).W
        (ListEval.rowsOf (visitData P e k) L)).flatMap m2) s' sgn (capC (visitData P e k) L) false

/-- The population's states, emitted. -/
def statesE (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ) (s : Fin (P.M + 1)) :
    List Bool :=
  (statesC P s).flatMap fun st =>
    stateE st.1 ((List.finRange P.walkLen).flatMap fun k => visitE P e L sgn labs st.2.val k)

theorem stateRec_marks (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)
    (st : ℤ × Fin (P.M + 1)) :
    Streaming.marks (stateRecC P e L sgn labs st) =
      stateE st.1 ((List.finRange P.walkLen).flatMap fun k => visitE P e L sgn labs st.2.val k) := by
  unfold stateRecC stateE
  rw [marks_cons, marks_append', marks_frame, marks_append', marks_flatMap]
  unfold blocksC
  rw [List.flatMap_assoc]
  have hk : ∀ k : Fin P.walkLen,
      ([blockC (visitData P e k) L st.2.val sgn true labs, blockC (visitData P e k) L st.2.val sgn false labs].flatMap
        fun b => Streaming.marks (true :: b)) = visitE P e L sgn labs st.2.val k := by
    intro k
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, blockE_eq]
    rfl
  rw [List.flatMap_congr fun k _ => hk k]
  simp [Streaming.marks]

/-- **The POP row's input word is the schedule** (at any capacities `R`, `Lg`, `cap` and threshold `θ`). -/
theorem popEmit_eq (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)
    (hlabs : 4 * L ≤ labs.length) (s : Fin (P.M + 1)) (θ R Lg cap : ℕ) :
    frame (popRowRec P.walkLen θ R Lg cap (oneWC P s) (popStates P e L sgn labs hlabs s)) =
      setupE P.walkLen θ R Lg cap ++ (((oneWC P s).flatMap m2 ++ [true, false]) ++
        (statesE P e L sgn labs s ++ [true, false])) ++ [false] := by
  unfold popRowRec popRec
  rw [popStates_eq, List.flatMap_map]
  have hs : ∀ st ∈ statesC P s, srec (st.1, visitFs P e L sgn labs hlabs st.2) = stateRecC P e L sgn labs st := by
    intro st _
    simp only [srec, stateRec, storeRec_visitFs]
    rfl
  rw [List.flatMap_congr hs, frame_eq, marks_append', marks_fieldsWord, setupE_eq, marks_append', marks_frame,
    marks_append', marks_flatMap]
  unfold statesE
  rw [List.flatMap_congr fun st _ => stateRec_marks P e L sgn labs st]
  simp [Streaming.marks]

end NearCubicWires.WireExponent3_5.PrimAsm.PopRec
