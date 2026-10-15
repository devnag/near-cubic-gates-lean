import Proof.Wire_3_5.BlockJoin
import Proof.Wire_3_5.BlockWhile

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Streams -/

/-- A stream tape: the framed records, the `false` terminator, then stale cells. -/
def streamTape (rs : List (List Bool)) (stale : List Bool) : List Bool := rs.flatMap frame ++ false :: stale

/-- The cell where record `j` starts. -/
def off (rs : List (List Bool)) (j : ℕ) : ℕ := ((rs.take j).flatMap frame).length

theorem streamTape_split (rs : List (List Bool)) (stale : List Bool) (j : ℕ) (hj : j < rs.length) :
    streamTape rs stale =
      (rs.take j).flatMap frame ++ frame rs[j] ++ ((rs.drop (j + 1)).flatMap frame ++ false :: stale) := by
  have e : rs = rs.take j ++ rs[j] :: rs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  calc streamTape rs stale = streamTape (rs.take j ++ rs[j] :: rs.drop (j + 1)) stale :=
        congrArg (fun r => streamTape r stale) e
    _ = _ := by simp only [streamTape, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem off_succ (rs : List (List Bool)) (j : ℕ) (hj : j < rs.length) :
    off rs (j + 1) = off rs j + (2 * rs[j].length + 1) := by
  unfold off
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_length]

theorem off_length (rs : List (List Bool)) : off rs rs.length = (rs.flatMap frame).length := by
  simp [off]

theorem read_stream_record (rs : List (List Bool)) (stale : List Bool) (j : ℕ) (hj : j < rs.length)
    (hne : rs[j] ≠ []) : readTapeBit (streamTape rs stale) (off rs j) = true := by
  rw [streamTape_split rs stale j hj]
  obtain ⟨b, w, hw⟩ : ∃ b w, rs[j] = b :: w := by
    cases h : rs[j] with
    | nil => exact absurd h hne
    | cons b w => exact ⟨b, w, rfl⟩
  rw [hw]
  simpa [frame, List.append_assoc, off] using
    Streaming.read_append ((rs.take j).flatMap frame) (b :: frame w ++ ((rs.drop (j + 1)).flatMap frame ++
      false :: stale)) true

theorem read_stream_end (rs : List (List Bool)) (stale : List Bool) :
    readTapeBit (streamTape rs stale) (rs.flatMap frame).length = false := by
  simpa [streamTape] using Streaming.read_append (rs.flatMap frame) stale false

/-- Writing a stream and its terminator over a backing leaves a stream tape. -/
theorem overlay_stream (rs : List (List Bool)) (T : List Bool) :
    overlay (rs.flatMap frame ++ [false]) T = streamTape rs (T.drop ((rs.flatMap frame).length + 1)) := by
  simp [overlay, streamTape, List.append_assoc]

/-- **A uniform body over the records of a stream.** The source tape holds `streamTape rs stale` in every bank, with
its head at the record's start. From the bank of each prefix state to the next, the body takes one `Step` of cost at
most `c`; the loop ends in the bank of the whole fold, the source head on the terminator. -/
theorem streamRun {t s : ℕ} (body : Machine t s) (src : Fin t) (rs : List (List Bool)) (stale : List Bool)
    (hne : ∀ r ∈ rs, r ≠ []) {σ : Type} (f : σ → List Bool → σ) (s0 : σ)
    (bH : σ → ℕ → Fin t → ℕ) (bA : σ → Fin t → List Bool)
    (hsrcA : ∀ st, bA st src = streamTape rs stale) (hsrcH : ∀ st p, bH st p src = p) (c : ℕ)
    (hstep : ∀ j, j < rs.length → Step body c (bH ((rs.take j).foldl f s0) (off rs j))
      (bA ((rs.take j).foldl f s0)) (bH ((rs.take (j + 1)).foldl f s0) (off rs (j + 1)))
      (bA ((rs.take (j + 1)).foldl f s0))) :
    Step (StreamController.machine body src) (rs.length * (c + 2) + 1) (bH s0 0) (bA s0)
      (bH (rs.foldl f s0) (rs.flatMap frame).length) (bA (rs.foldl f s0)) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := rs.length
      H := fun j => bH ((rs.take j).foldl f s0) (off rs j)
      A := fun j => bA ((rs.take j).foldl f s0)
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA ((rs.take j).foldl f s0) src) (bH ((rs.take j).foldl f s0) (off rs j) src) = true
        rw [hsrcA, hsrcH]
        exact read_stream_record rs stale j hj (hne _ (List.getElem_mem hj))
      halt := by
        show readTapeBit (bA ((rs.take rs.length).foldl f s0) src)
          (bH ((rs.take rs.length).foldl f s0) (off rs rs.length) src) = false
        rw [hsrcA, hsrcH, off_length]
        exact read_stream_end rs stale }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  have e0 : W.H 0 = bH s0 0 := by simp [W, off]
  have e1 : W.A 0 = bA s0 := by simp [W]
  have e2 : W.H W.bound = bH (rs.foldl f s0) (rs.flatMap frame).length := by
    simp only [W, List.take_length, off_length]
  have e3 : W.A W.bound = bA (rs.foldl f s0) := by simp only [W, List.take_length]
  rw [e0, e1, e2, e3] at hW
  exact hW

/-! ## The primitive steps -/

/-- Copy `frame w` from the source cursor onto the output cursor, over the output's backing (`copyBlock`). -/
theorem copyStep (pre w tail out BW : List Bool) :
    Step CopyO.machine (2 * w.length + 1) ![pre.length, out.length] ![pre ++ frame w ++ tail, overlay out BW]
      ![pre.length + 2 * w.length, out.length + (2 * w.length + 1)]
      ![pre ++ frame w ++ tail, overlay (out ++ frame w) BW] := by
  have hb := (copyBlock pre w tail out BW).run
  obtain ⟨h1, h2, h3, h4, h5⟩ := copyBlock_spec pre w tail out BW
  rw [h1, h2, h3, h4, h5] at hb
  exact hb

/-- The framed map of two words written at the output cursor, over its backing (`mapBlockO`). -/
theorem mapStepO (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preL preR left right tailL tailR output BW : List Bool) (hw : left.length = right.length) :
    Step (ZipMap.machine out nxt init) (2 * left.length + 1) ![preL.length, preR.length, output.length]
      ![preL ++ frame left ++ tailL, preR ++ frame right ++ tailR, overlay output BW]
      ![preL.length + 2 * left.length, preR.length + 2 * right.length, output.length + (2 * left.length + 1)]
      ![preL ++ frame left ++ tailL, preR ++ frame right ++ tailR,
        overlay (output ++ frame (ZipMap.map out nxt left right init)) BW] := by
  have hb := (mapBlockO out nxt init preL preR left right tailL tailR output BW hw).run
  obtain ⟨h1, h2, h3, h4, h5⟩ := mapBlockO_spec out nxt init preL preR left right tailL tailR output BW hw
  rw [h1, h2, h3, h4, h5] at hb
  exact hb

/-- Bitwise OR (the union of two masks). -/
def orOut (a b _ : Bool) : Bool := a || b

theorem map_or (left right : List Bool) (hw : left.length = right.length) (old : Bool) :
    ZipMap.map orOut keep left right old = List.zipWith (· || ·) left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [ZipMap.map, orOut, keep, ih right (by simpa using hw)]

/-- Write a bit under the head and step right. -/
def putM (b : Bool) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some b, fun _ => .right⟩ else none

theorem putStep (b : Bool) (T : List Bool) (h : ℕ) :
    Step (putM b) 1 ![h] ![T] ![h + 1] ![writeTapeBit T h b] := by
  have hs : step (putM b) ⟨(putM b).start, ![h], ![T]⟩ = some ⟨1, ![h + 1], ![writeTapeBit T h b]⟩ := by
    simp [step, putM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := putM b) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-- Write a fixed bit into a one-cell tape. -/
def cellM (b : Bool) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some b, fun _ => .stay⟩ else none

theorem cellStep (b c : Bool) : Step (cellM b) 1 ![0] ![[c]] ![0] ![[b]] := by
  have hs : step (cellM b) ⟨(cellM b).start, ![0], ![[c]]⟩ = some ⟨1, ![0], ![[b]]⟩ := by
    simp [step, cellM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, writeTapeBit]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := cellM b) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-- The halted program: no step. -/
theorem idleStep {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) : Step (idle t) 0 H A H A :=
  Step.of_run (runFrom_zero_of_halted (idle t) ⟨(idle t).start, H, A⟩ rfl) rfl rfl

/-! ## Masked register steps (the log is the last local tape) -/

/-- Load a record from a stream cursor into a register (head back to cell 0). -/
noncomputable def loadM := MaskedReset.machine CopyO.machine ![false, true]

theorem loadStep (pre w tail Y : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step loadM (2 * (2 * w.length + 1) + 2) ![pre.length, 0, 0]
      ![pre ++ frame w ++ tail, Y, List.replicate cap false] ![pre.length + 2 * w.length, 0, 0]
      ![pre ++ frame w ++ tail, overlay (frame w) Y, List.replicate cap false] := by
  have h0 := copyStep pre w tail [] Y
  have hY : overlay [] Y = Y := by simp [overlay]
  rw [hY, List.nil_append, List.length_nil, Nat.zero_add] at h0
  have hm := h0.mask ![false, true] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- Emit a register (head at cell 0, returned there) onto a stream cursor, over its backing. -/
noncomputable def emitM := MaskedReset.machine CopyO.machine ![true, false]

theorem emitStep (w out BW : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step emitM (2 * (2 * w.length + 1) + 2) ![0, out.length, 0]
      ![frame w, overlay out BW, List.replicate cap false] ![0, out.length + (2 * w.length + 1), 0]
      ![frame w, overlay (out ++ frame w) BW, List.replicate cap false] := by
  have h0 := copyStep [] w [] out BW
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h0
  have hm := h0.mask ![true, false] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- Word equality of two registers into a cell (both register heads back at cell 0). -/
noncomputable def eqM := MaskedReset.machine (EqCell.machine false) ![true, true, false]

theorem eqStep (u v : List Bool) (e : Bool) (hl : u.length = v.length) (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) :
    Step eqM (2 * (2 * u.length + 1) + 2) ![0, 0, 0, 0] ![frame u, frame v, [e], List.replicate cap false]
      ![0, 0, 0, 0] ![frame u, frame v, [decide (u = v)], List.replicate cap false] := by
  have h0 := EqCell.run false u v e hl
  rw [Bool.false_xor] at h0
  have h1 : Step (EqCell.machine false) (2 * u.length + 1) (fun _ => 0) ![frame u, frame v, [e]]
      ![2 * u.length, 2 * u.length, 0] ![frame u, frame v, [decide (u = v)]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have hm := h1.mask ![true, true, false] (by intro i _; rfl) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- The union of two registers written into a third (all three heads back at cell 0). -/
noncomputable def orM := MaskedReset.machine (ZipMap.machine orOut keep false) ![true, true, true]

theorem orStep (u v Z : List Bool) (hl : u.length = v.length) (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) :
    Step orM (2 * (2 * u.length + 1) + 2) ![0, 0, 0, 0] ![frame u, frame v, Z, List.replicate cap false]
      ![0, 0, 0, 0] ![frame u, frame v, overlay (frame (List.zipWith (· || ·) u v)) Z, List.replicate cap false] := by
  have h0 := mapStepO orOut keep false [] [] u v [] [] [] Z hl
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add, map_or u v hl] at h0
  have hZ : overlay [] Z = Z := by simp [overlay]
  rw [hZ] at h0
  have hm := h0.mask ![true, true, true] (by intro i _; fin_cases i <;> rfl) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## Evaluating a docked bank -/

/-- Evaluate an install or a head dock at one concrete tape of a concrete layout. -/
macro "slot_eval" : tactic => `(tactic| first
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0 | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2 | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4 | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6 | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8 | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
  | exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  | exact dockH_slot _ (by decide) _ _ 0 | exact dockH_slot _ (by decide) _ _ 1
  | exact dockH_slot _ (by decide) _ _ 2 | exact dockH_slot _ (by decide) _ _ 3
  | exact dockH_slot _ (by decide) _ _ 4 | exact dockH_slot _ (by decide) _ _ 5
  | exact dockH_slot _ (by decide) _ _ 6 | exact dockH_slot _ (by decide) _ _ 7
  | exact dockH_slot _ (by decide) _ _ 8 | exact dockH_slot _ (by decide) _ _ 9
  | exact dockH_other _ _ _ _ (by decide))

end NearCubicWires.WireExponent3_5.CompilerMachine.Kit
