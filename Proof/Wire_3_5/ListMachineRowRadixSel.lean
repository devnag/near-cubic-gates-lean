import Proof.Wire_3_5.ListMachineRowRadixProg

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun atomCode monoBits recW polyWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5

/-- A store of printed polynomials. -/
def stF (fs : List (List (List ℕ))) : List Bool := fs.flatMap polyWord

/-- The records of the marked entries. -/
def mselW (r : List Bool) (fs : List (List (List ℕ))) : List Bool :=
  (r.zip fs).flatMap fun bq => if bq.1 then true :: polyWord bq.2 else []

/-- One entry: copy it after a `true` record marker, or pass it. -/
noncomputable def mbr := Block.branchM (0 : Fin 3) (Composition.machine putT (pc true)) (pc false)
noncomputable def mselBody := Composition.machine (Composition.machine skipX mbr) skipX
/-- **The masked selection loop.** -/
noncomputable def mselM := StreamController.machine mselBody (0 : Fin 3)

theorem mbr_step (b : Bool) (h : ℕ) (X pre : List Bool) (P : List (List ℕ)) (tail o B : List Bool)
    (hb : readTapeBit X h = b) :
    Step mbr ((polyWord P).length + 4) ![h, pre.length, o.length] ![X, pre ++ polyWord P ++ tail, overlay o B]
      ![h, pre.length + (polyWord P).length, (o ++ if b then true :: polyWord P else []).length]
      ![X, pre ++ polyWord P ++ tail, overlay (o ++ if b then true :: polyWord P else []) B] := by
  cases b
  · have s := pc_step false h X pre P tail o B
    have t := Block.branch_false (0 : Fin 3) (Composition.machine putT (pc true)) s (by simpa using hb)
    refine (t.congr ?_ ?_).enlarge (by omega)
    · simp [ow]
    · simp [ow]
  · have s1 := putT_step h pre.length X (pre ++ polyWord P ++ tail) o B
    have s2 := pc_step true h X pre P tail (o ++ [true]) B
    have t := Block.branch_true (0 : Fin 3) (pc false) (s1.seq s2) (by simpa using hb)
    refine (t.congr ?_ ?_).enlarge (by omega)
    · simp [ow]
    · simp [ow]

theorem stF_split (fs : List (List (List ℕ))) (j : ℕ) (hj : j < fs.length) :
    stF fs = stF (fs.take j) ++ polyWord fs[j] ++ stF (fs.drop (j + 1)) := by
  conv_lhs => rw [← List.take_append_drop j fs, List.drop_eq_getElem_cons hj]
  simp only [stF, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem stF_take_succ (fs : List (List (List ℕ))) (j : ℕ) (hj : j < fs.length) :
    stF (fs.take (j + 1)) = stF (fs.take j) ++ polyWord fs[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [stF, List.flatMap_append, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem mselW_take_succ (r : List Bool) (fs : List (List (List ℕ))) (j : ℕ) (hj : j < r.length)
    (hl : r.length = fs.length) :
    mselW (r.take (j + 1)) (fs.take (j + 1)) =
      mselW (r.take j) (fs.take j) ++ (if r[j] then true :: polyWord fs[j] else []) := by
  have hj' : j < fs.length := hl ▸ hj
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj']
  unfold mselW
  rw [List.zip_append (by simp [List.length_take]; omega)]
  simp

/-- The cost of pass `j`. -/
def mselPass (fs : List (List (List ℕ))) (j : ℕ) : ℕ := 1 + 1 + ((polyWord (fs.getD j [])).length + 4) + 1 + 1

def mselH (r : List Bool) (fs : List (List (List ℕ))) (o : List Bool) (j : ℕ) : Fin 3 → ℕ :=
  ![2 * j, (stF (fs.take j)).length, (o ++ mselW (r.take j) (fs.take j)).length]
def mselA (r : List Bool) (fs : List (List (List ℕ))) (tail o B : List Bool) (j : ℕ) : Fin 3 → List Bool :=
  ![frame r, stF fs ++ tail, overlay (o ++ mselW (r.take j) (fs.take j)) B]

theorem mselBody_step (r : List Bool) (fs : List (List (List ℕ))) (hl : r.length = fs.length)
    (tail o B : List Bool) (j : ℕ) (hj : j < r.length) :
    Step mselBody (mselPass fs j) (mselH r fs o j) (mselA r fs tail o B j) (mselH r fs o (j + 1))
      (mselA r fs tail o B (j + 1)) := by
  have hj' : j < fs.length := hl ▸ hj
  set sel := o ++ mselW (r.take j) (fs.take j) with hsel
  have s1 := skipX_step (2 * j) (stF (fs.take j)).length sel.length (frame r) (stF fs ++ tail) (overlay sel B)
  have hsplit : stF fs ++ tail = stF (fs.take j) ++ polyWord fs[j] ++ (stF (fs.drop (j + 1)) ++ tail) := by
    rw [stF_split fs j hj']; simp [List.append_assoc]
  rw [hsplit] at s1
  have s2 := mbr_step r[j] (2 * j + 1) (frame r) (stF (fs.take j)) fs[j] (stF (fs.drop (j + 1)) ++ tail) sel B
    (frame_read_bit r j hj)
  have s3 := skipX_step (2 * j + 1) ((stF (fs.take j)).length + (polyWord fs[j]).length)
    (sel ++ if r[j] then true :: polyWord fs[j] else []).length (frame r)
    (stF (fs.take j) ++ polyWord fs[j] ++ (stF (fs.drop (j + 1)) ++ tail))
    (overlay (sel ++ if r[j] then true :: polyWord fs[j] else []) B)
  have t := (s1.seq s2).seq s3
  rw [← hsplit] at t
  have eo : sel ++ (if r[j] then true :: polyWord fs[j] else []) = o ++ mselW (r.take (j + 1)) (fs.take (j + 1)) := by
    rw [mselW_take_succ r fs j hj hl, hsel]; simp [List.append_assoc]
  rw [eo] at t
  refine (t.congr ?_ rfl).enlarge (le_of_eq ?_)
  · simp only [mselH, stF_take_succ fs j hj', List.length_append]
    funext i; fin_cases i <;> simp; omega
  · simp [mselPass, List.getElem?_eq_getElem hj']

/-- The cost of the masked selection. -/
def mselCost (fs : List (List (List ℕ))) : ℕ := ((List.range fs.length).map fun j => mselPass fs j + 2).sum + 1

/-- **The masked selection**: the output receives the records of the marked store entries. -/
theorem msel_run (r : List Bool) (fs : List (List (List ℕ))) (hl : r.length = fs.length) (tail o B : List Bool) :
    Step mselM (mselCost fs) ![0, 0, o.length] ![frame r, stF fs ++ tail, overlay o B]
      ![2 * r.length, (stF fs).length, (o ++ mselW r fs).length] ![frame r, stF fs ++ tail, overlay (o ++ mselW r fs) B] := by
  have hW := Block.WhileBody.run ({
    body := mselBody
    tape := (0 : Fin 3)
    bound := r.length
    H := mselH r fs o
    A := mselA r fs tail o B
    cost := mselPass fs
    step := fun j hj => mselBody_step r fs hl tail o B j hj
    cont := by
      intro j hj
      simpa [mselH, mselA] using frame_read_mark r j hj
    halt := by simpa [mselH, mselA] using frame_read_end r } : Block.WhileBody 3 _)
  have e0 : mselH r fs o 0 = ![0, 0, o.length] := by simp [mselH, mselW, stF]
  have e1 : mselA r fs tail o B 0 = ![frame r, stF fs ++ tail, overlay o B] := by simp [mselA, mselW]
  have t1 : r.take r.length = r := List.take_length
  have t2 : fs.take r.length = fs := by rw [hl]; exact List.take_length
  have e2 : mselH r fs o r.length = ![2 * r.length, (stF fs).length, (o ++ mselW r fs).length] := by
    simp only [mselH, t1, t2]
  have e3 : mselA r fs tail o B r.length = ![frame r, stF fs ++ tail, overlay (o ++ mselW r fs) B] := by
    simp only [mselA, t1, t2]
  have hW' : Step mselM (((List.range (r.length - 0)).map fun i => mselPass fs (0 + i) + 2).sum + 1)
      (mselH r fs o 0) (mselA r fs tail o B 0) (mselH r fs o r.length) (mselA r fs tail o B r.length) := hW
  simp only [Nat.sub_zero, Nat.zero_add] at hW'
  rw [e0, e1, e2, e3] at hW'
  unfold mselCost
  rw [← hl]
  exact hW'

end NearCubicWires.WireExponent3_5.ListMachine.Row
