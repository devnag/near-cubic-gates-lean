import Proof.Wire_3_5.CompilerMachineCancel

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The filter pass -/

/-- The filter pass's heads: the stream cursor `p`, the output cursor after `outs`. -/
def fH (p : ℕ) (outs : List (List Bool)) : Fin 7 → ℕ := ![p, (outs.flatMap frame).length, 0, 0, 0, 0, 0]

/-- The filter pass's tapes in state `(outs, found, y, e)`. -/
def fA (S BW x : List Bool) (cap : ℕ) (st : List (List Bool) × Bool × List Bool × Bool) : Fin 7 → List Bool :=
  ![S, overlay (st.1.flatMap frame) BW, frame x, frame st.2.2.1, [st.2.2.2], [st.2.1], List.replicate cap false]

theorem read_cell (c : Bool) : readTapeBit [c] 0 = c := by cases c <;> rfl

/-- **One record of the filter pass.** -/
theorem filter_body (pre r post BW x : List Bool) (cap : ℕ) (st : List (List Bool) × Bool × List Bool × Bool)
    (hr : r.length = x.length) (hy : st.2.2.1.length = x.length) (hcap : 2 * r.length + 1 ≤ cap) :
    Step filterBodyM (12 * r.length + 18) (fH pre.length st.1) (fA (pre ++ frame r ++ post) BW x cap st)
      (fH (pre.length + (2 * r.length + 1)) (fstep x st r).1) (fA (pre ++ frame r ++ post) BW x cap (fstep x st r)) := by
  obtain ⟨outs, f, y, e⟩ := st
  simp only at hy
  have s1 := load_step (cap := cap) (T1 := overlay (outs.flatMap frame) BW) (T2 := frame x) (T4 := [e]) (T5 := [f])
    (h1 := (outs.flatMap frame).length) pre r post y (by rw [hy, hr]) hcap
  have s2 := nudgeS_step (cap := cap) (T0 := pre ++ frame r ++ post) (T1 := overlay (outs.flatMap frame) BW)
    (T2 := frame x) (T3 := frame r) (T4 := [e]) (T5 := [f]) (h0 := pre.length + 2 * r.length)
    (h1 := (outs.flatMap frame).length)
  have s3 := eq_step (cap := cap) (T0 := pre ++ frame r ++ post) (T1 := overlay (outs.flatMap frame) BW) (T5 := [f])
    (h0 := pre.length + 2 * r.length + 1) (h1 := (outs.flatMap frame).length) x r e hr hcap
  have s123 := (s1.seq s2).seq s3
  by_cases hrx : r = x
  · have s4 := setF_step (cap := cap) (T0 := pre ++ frame r ++ post) (T1 := overlay (outs.flatMap frame) BW)
      (T2 := frame x) (T3 := frame r) (T4 := [decide (r = x)]) (h0 := pre.length + 2 * r.length + 1)
      (h1 := (outs.flatMap frame).length) f
    have s5 := branch_true (4 : Fin 7) emitYD s4 (by simp [hrx, read_cell])
    refine ((s123.seq s5).enlarge (by omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp [fH, fstep, hrx]
      all_goals omega
    · funext i; fin_cases i <;> simp [fA, fstep, hrx]
  · have s4 := emitY_step (cap := cap) (T0 := pre ++ frame r ++ post) (T2 := frame x) (T4 := [decide (r = x)])
      (T5 := [f]) (h0 := pre.length + 2 * r.length + 1) r (outs.flatMap frame) BW hcap
    have s5 := branch_false (4 : Fin 7) setFD s4 (by simp [hrx, read_cell])
    refine ((s123.seq s5).enlarge (by omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp [fH, fstep, hrx]
      all_goals omega
    · funext i; fin_cases i <;> simp [fA, fstep, hrx]

theorem fstep_y_length (x : List Bool) (G : List (List Bool)) (st : List (List Bool) × Bool × List Bool × Bool)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : st.2.2.1.length = x.length) :
    (G.foldl (fstep x) st).2.2.1.length = x.length := by
  rcases (foldl_fstep x G st).2.2 with h | h
  · rw [h, hy]
  · exact hG _ h

/-- **The stream loop of the filter pass.** -/
theorem filter_loop (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool) (cap : ℕ)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : y.length = x.length) (hx : x ≠ []) (hcap : 2 * x.length + 1 ≤ cap) :
    Step (StreamController.machine filterBodyM 0) (G.length * (12 * x.length + 18 + 2) + 1)
      (fH 0 []) (fA (streamTape G staleS) BW x cap ([], false, y, e))
      (fH (G.flatMap frame).length (G.foldl (fstep x) ([], false, y, e)).1)
      (fA (streamTape G staleS) BW x cap (G.foldl (fstep x) ([], false, y, e))) := by
  refine streamRun filterBodyM 0 G staleS (fun r hr h => hx (List.length_eq_zero_iff.mp (by rw [← hG r hr, h]; rfl)))
    (fstep x) ([], false, y, e) (fun st p => fH p st.1) (fun st => fA (streamTape G staleS) BW x cap st)
    (fun _ => rfl) (fun _ _ => rfl) (12 * x.length + 18) ?_
  intro j hj
  have hlen := hG _ (List.getElem_mem hj)
  have hst : (G.take (j + 1)).foldl (fstep x) ([], false, y, e) =
      fstep x ((G.take j).foldl (fstep x) ([], false, y, e)) G[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  have hyst := fstep_y_length x (G.take j) ([], false, y, e) (fun r hr => hG r (List.mem_of_mem_take hr)) hy
  have hb := filter_body ((G.take j).flatMap frame) G[j] ((G.drop (j + 1)).flatMap frame ++ false :: staleS) BW x cap
    ((G.take j).foldl (fstep x) ([], false, y, e)) hlen hyst (by omega)
  rw [← streamTape_split G staleS j hj, hlen] at hb
  rw [hst, off_succ G j hj, hlen]
  exact hb

/-- The cost of the filter pass before its reset, for `n` records of width `W`. -/
def filterLoopCost (n W : ℕ) : ℕ := n * (12 * W + 18 + 2) + 1 + 1 + (2 * (2 * W + 1) + 2 + 2) + 1 + 1 + 1 + 1

/-- **The filter pass**: the kept records, then `X` unless found, then the terminator; `F` cleared. -/
theorem filter_run (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool) (cap : ℕ)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : y.length = x.length) (hx : x ≠ []) (hcap : 2 * x.length + 1 ≤ cap) :
    Step filterLoopM (filterLoopCost G.length x.length) (fH 0 [])
      (fA (streamTape G staleS) BW x cap ([], false, y, e))
      ![(G.flatMap frame).length, ((symInsertW G x).flatMap frame).length + 1, 0, 0, 0, 0, 0]
      ![streamTape G staleS, overlay ((symInsertW G x).flatMap frame ++ [false]) BW, frame x,
        frame (G.foldl (fstep x) ([], false, y, e)).2.2.1, [(G.foldl (fstep x) ([], false, y, e)).2.2.2], [false],
        List.replicate cap false] := by
  obtain ⟨h1, h2, _⟩ := foldl_fstep x G ([], false, y, e)
  have L := filter_loop G staleS BW x y e cap hG hy hx hcap
  by_cases hxG : x ∈ G
  · have hsym : symInsertW G x = (G.foldl (fstep x) ([], false, y, e)).1 := by simp [symInsertW, hxG, h1]
    have hf : (G.foldl (fstep x) ([], false, y, e)).2.1 = true := by simp [h2, hxG]
    have B := branch_true (5 : Fin 7) emitXD (idleStep (fH (G.flatMap frame).length (G.foldl (fstep x) ([], false, y, e)).1)
      (fA (streamTape G staleS) BW x cap (G.foldl (fstep x) ([], false, y, e))))
      (by show readTapeBit [(G.foldl (fstep x) ([], false, y, e)).2.1] 0 = true; rw [hf]; rfl)
    have P := putO_step (cap := cap) (T0 := streamTape G staleS) (T2 := frame x)
      (T3 := frame (G.foldl (fstep x) ([], false, y, e)).2.2.1) (T4 := [(G.foldl (fstep x) ([], false, y, e)).2.2.2])
      (T5 := [(G.foldl (fstep x) ([], false, y, e)).2.1]) (h0 := (G.flatMap frame).length)
      ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame) BW
    have C := clrF_step (cap := cap) (T0 := streamTape G staleS)
      (T1 := overlay ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame ++ [false]) BW) (T2 := frame x)
      (T3 := frame (G.foldl (fstep x) ([], false, y, e)).2.2.1) (T4 := [(G.foldl (fstep x) ([], false, y, e)).2.2.2])
      (h0 := (G.flatMap frame).length) (h1 := ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame).length + 1)
      (G.foldl (fstep x) ([], false, y, e)).2.1
    rw [hsym]
    exact (((L.seq B).seq P).seq C).enlarge (by unfold filterLoopCost; omega)
  · have hfil : G.filter (fun a => decide (a ≠ x)) = G :=
      List.filter_eq_self.mpr (fun a ha => decide_eq_true (fun h => hxG (h ▸ ha)))
    have hsym : symInsertW G x = (G.foldl (fstep x) ([], false, y, e)).1 ++ [x] := by
      rw [h1]
      show symInsertW G x = [] ++ G.filter (fun a => decide (a ≠ x)) ++ [x]
      rw [List.nil_append, hfil]
      simp [symInsertW, hxG]
    have hf : (G.foldl (fstep x) ([], false, y, e)).2.1 = false := by simp [h2, hxG]
    have E0 := emitX_step (cap := cap) (T0 := streamTape G staleS)
      (T3 := frame (G.foldl (fstep x) ([], false, y, e)).2.2.1) (T4 := [(G.foldl (fstep x) ([], false, y, e)).2.2.2])
      (T5 := [(G.foldl (fstep x) ([], false, y, e)).2.1]) (h0 := (G.flatMap frame).length) x
      ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame) BW hcap
    have B := branch_false (5 : Fin 7) (idle 7) E0
      (by show readTapeBit [(G.foldl (fstep x) ([], false, y, e)).2.1] 0 = false; rw [hf]; rfl)
    have P := putO_step (cap := cap) (T0 := streamTape G staleS) (T2 := frame x)
      (T3 := frame (G.foldl (fstep x) ([], false, y, e)).2.2.1) (T4 := [(G.foldl (fstep x) ([], false, y, e)).2.2.2])
      (T5 := [(G.foldl (fstep x) ([], false, y, e)).2.1]) (h0 := (G.flatMap frame).length)
      ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame ++ frame x) BW
    have C := clrF_step (cap := cap) (T0 := streamTape G staleS)
      (T1 := overlay ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame ++ frame x ++ [false]) BW) (T2 := frame x)
      (T3 := frame (G.foldl (fstep x) ([], false, y, e)).2.2.1) (T4 := [(G.foldl (fstep x) ([], false, y, e)).2.2.2])
      (h0 := (G.flatMap frame).length)
      (h1 := ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame ++ frame x).length + 1)
      (G.foldl (fstep x) ([], false, y, e)).2.1
    have B' := B.congr (hout' := ![(G.flatMap frame).length,
      ((G.foldl (fstep x) ([], false, y, e)).1.flatMap frame ++ frame x).length, 0, 0, 0, 0, 0]) (by simp) rfl
    rw [hsym]
    refine ((((L.seq B').seq P).seq C).enlarge (by unfold filterLoopCost; omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp

/-! ## The copy-back pass -/

/-- The copy-back pass's heads: the written cursor on `S`, the stream cursor `p` on `O`. -/
def cH (p : ℕ) (written : List (List Bool)) : Fin 7 → ℕ := ![(written.flatMap frame).length, p, 0, 0, 0, 0, 0]

/-- The copy-back pass's tapes. -/
def cA (Sold O X Y E F : List Bool) (cap : ℕ) (written : List (List Bool)) : Fin 7 → List Bool :=
  ![overlay (written.flatMap frame) Sold, O, X, Y, E, F, List.replicate cap false]

theorem copy_body (pre w post Sold X Y E F : List Bool) (cap : ℕ) (written : List (List Bool)) :
    Step copyBodyM (2 * w.length + 1 + 1 + 1) (cH pre.length written) (cA Sold (pre ++ frame w ++ post) X Y E F cap written)
      (cH (pre.length + (2 * w.length + 1)) (written ++ [w])) (cA Sold (pre ++ frame w ++ post) X Y E F cap (written ++ [w])) := by
  have s1 := copyOS_step (cap := cap) (T2 := X) (T3 := Y) (T4 := E) (T5 := F) pre w post (written.flatMap frame) Sold
  have s2 := nudgeO_step (cap := cap) (T0 := overlay (written.flatMap frame ++ frame w) Sold) (T1 := pre ++ frame w ++ post)
    (T2 := X) (T3 := Y) (T4 := E) (T5 := F) (h0 := (written.flatMap frame).length + (2 * w.length + 1))
    (h1 := pre.length + 2 * w.length)
  refine (s1.seq s2).congr ?_ ?_
  · funext i; fin_cases i <;> simp [cH, frame_length]
    all_goals omega
  · funext i; fin_cases i <;> simp [cA]

theorem foldl_snoc_nil (l : List (List Bool)) : l.foldl (fun acc r => acc ++ [r]) [] = l := by
  have : ∀ acc : List (List Bool), l.foldl (fun acc r => acc ++ [r]) acc = acc ++ l := by
    induction l with
    | nil => simp
    | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp
  simpa using this []

theorem copy_loop (outs : List (List Bool)) (staleO Sold X Y E F : List Bool) (cap W : ℕ)
    (hw : ∀ r ∈ outs, r.length = W) (hW : 1 ≤ W) :
    Step (StreamController.machine copyBodyM 1) (outs.length * (2 * W + 1 + 1 + 1 + 2) + 1)
      (cH 0 []) (cA Sold (streamTape outs staleO) X Y E F cap [])
      (cH (outs.flatMap frame).length outs) (cA Sold (streamTape outs staleO) X Y E F cap outs) := by
  have h := streamRun copyBodyM 1 outs staleO (fun r hr h => by have := hw r hr; rw [h] at this; simp at this; omega)
    (fun acc r => acc ++ [r]) ([] : List (List Bool)) (fun st p => cH p st)
    (fun st => cA Sold (streamTape outs staleO) X Y E F cap st) (fun _ => rfl) (fun _ _ => rfl)
    (2 * W + 1 + 1 + 1) (by
      intro j hj
      have hlen := hw _ (List.getElem_mem hj)
      have hst : (outs.take (j + 1)).foldl (fun acc r => acc ++ [r]) [] =
          (outs.take j).foldl (fun acc r => acc ++ [r]) [] ++ [outs[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
        rfl
      have hb := copy_body ((outs.take j).flatMap frame) outs[j] ((outs.drop (j + 1)).flatMap frame ++ false :: staleO)
        Sold X Y E F cap ((outs.take j).foldl (fun acc r => acc ++ [r]) [])
      rw [← streamTape_split outs staleO j hj, hlen] at hb
      rw [hst, off_succ outs j hj, hlen]
      exact hb)
  rwa [foldl_snoc_nil] at h

/-- The cost of the copy-back pass before its reset, for `n` records of width `W`. -/
def copyLoopCost (n W : ℕ) : ℕ := n * (2 * W + 1 + 1 + 1 + 2) + 1 + 1 + 1

theorem copy_run (outs : List (List Bool)) (staleO Sold X Y E F : List Bool) (cap W : ℕ)
    (hw : ∀ r ∈ outs, r.length = W) (hW : 1 ≤ W) :
    Step copyLoopM (copyLoopCost outs.length W) (cH 0 []) (cA Sold (streamTape outs staleO) X Y E F cap [])
      ![(outs.flatMap frame).length + 1, (outs.flatMap frame).length, 0, 0, 0, 0, 0]
      ![overlay (outs.flatMap frame ++ [false]) Sold, streamTape outs staleO, X, Y, E, F, List.replicate cap false] := by
  have L := copy_loop outs staleO Sold X Y E F cap W hw hW
  have P := putS_step (cap := cap) (T1 := streamTape outs staleO) (T2 := X) (T3 := Y) (T4 := E) (T5 := F)
    (h1 := (outs.flatMap frame).length) (outs.flatMap frame) Sold
  exact (L.seq P).enlarge (by unfold copyLoopCost; omega)

/-! ## The two passes with their resets, and the insertion -/

theorem filter_pass (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool) (cap cap2 : ℕ)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : y.length = x.length) (hx : x ≠ []) (hcap : 2 * x.length + 1 ≤ cap)
    (hcap2 : filterLoopCost G.length x.length ≤ cap2) :
    Step filterPassM (2 * filterLoopCost G.length x.length + 2) (fun _ => 0)
      ![streamTape G staleS, BW, frame x, frame y, [e], [false], List.replicate cap false, List.replicate cap2 false]
      (fun _ => 0)
      ![streamTape G staleS, overlay ((symInsertW G x).flatMap frame ++ [false]) BW, frame x,
        frame (G.foldl (fstep x) ([], false, y, e)).2.2.1, [(G.foldl (fstep x) ([], false, y, e)).2.2.2], [false],
        List.replicate cap false, List.replicate cap2 false] := by
  have h := filter_run G staleS BW x y e cap hG hy hx hcap
  have hm := h.mask selSO (by intro i hi; fin_cases i <;> simp_all [selSO, fH]) hcap2
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

theorem copy_pass (outs : List (List Bool)) (staleO Sold X Y E F : List Bool) (cap cap2 W : ℕ)
    (hw : ∀ r ∈ outs, r.length = W) (hW : 1 ≤ W) (hcap2 : copyLoopCost outs.length W ≤ cap2) :
    Step copyPassM (2 * copyLoopCost outs.length W + 2) (fun _ => 0)
      ![Sold, streamTape outs staleO, X, Y, E, F, List.replicate cap false, List.replicate cap2 false] (fun _ => 0)
      ![overlay (outs.flatMap frame ++ [false]) Sold, streamTape outs staleO, X, Y, E, F, List.replicate cap false,
        List.replicate cap2 false] := by
  have h := copy_run outs staleO Sold X Y E F cap W hw hW
  have hm := h.mask selSO (by intro i hi; fin_cases i <;> simp_all [selSO, cH]) hcap2
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

theorem mem_symInsertW (G : List (List Bool)) (x r : List Bool) (h : r ∈ symInsertW G x) : r ∈ G ∨ r = x := by
  unfold symInsertW at h
  split_ifs at h
  · exact Or.inl (List.mem_filter.mp h).1
  · simpa using h

theorem length_symInsertW_le (G : List (List Bool)) (x : List Bool) : (symInsertW G x).length ≤ G.length + 1 := by
  unfold symInsertW
  split_ifs
  · exact (List.length_filter_le _ _).trans (Nat.le_succ _)
  · simp

theorem copyLoopCost_mono {n m : ℕ} (W : ℕ) (h : n ≤ m) : copyLoopCost n W ≤ copyLoopCost m W := by
  unfold copyLoopCost
  have := Nat.mul_le_mul_right (2 * W + 1 + 1 + 1 + 2) h
  omega

/-- The scratch contents after one insertion: the stale cells of `S` and `O`, the register `Y`, the cell `E`. -/
def symNext (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool) : List Bool × List Bool × List Bool × Bool :=
  ((streamTape G staleS).drop (((symInsertW G x).flatMap frame).length + 1),
    BW.drop (((symInsertW G x).flatMap frame).length + 1),
    (G.foldl (fstep x) ([], false, y, e)).2.2.1, (G.foldl (fstep x) ([], false, y, e)).2.2.2)

theorem symNext_y_length (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : y.length = x.length) : (symNext G staleS BW x y e).2.2.1.length = x.length :=
  fstep_y_length x G _ hG hy

/-- The cost of one insertion into a list of `n` words of width `W`. -/
def symCost (n W : ℕ) : ℕ := (2 * filterLoopCost n W + 2) + 1 + (2 * copyLoopCost (n + 1) W + 2)

theorem sym_run (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool) (cap cap2 : ℕ)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : y.length = x.length) (hx : x ≠ []) (hcap : 2 * x.length + 1 ≤ cap)
    (hcap2 : filterLoopCost G.length x.length ≤ cap2 ∧ copyLoopCost (G.length + 1) x.length ≤ cap2) :
    Step symM (symCost G.length x.length) (fun _ => 0)
      ![streamTape G staleS, BW, frame x, frame y, [e], [false], List.replicate cap false, List.replicate cap2 false]
      (fun _ => 0)
      ![streamTape (symInsertW G x) (symNext G staleS BW x y e).1, streamTape (symInsertW G x) (symNext G staleS BW x y e).2.1,
        frame x, frame (symNext G staleS BW x y e).2.2.1, [(symNext G staleS BW x y e).2.2.2], [false],
        List.replicate cap false, List.replicate cap2 false] := by
  have hf := filter_pass G staleS BW x y e cap cap2 hG hy hx hcap hcap2.1
  have hw : ∀ r ∈ symInsertW G x, r.length = x.length := by
    intro r hr
    rcases mem_symInsertW G x r hr with h | h
    · exact hG r h
    · rw [h]
  have hW : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hlen := length_symInsertW_le G x
  have hc := copy_pass (symInsertW G x) (BW.drop (((symInsertW G x).flatMap frame).length + 1)) (streamTape G staleS)
    (frame x) (frame (G.foldl (fstep x) ([], false, y, e)).2.2.1) [(G.foldl (fstep x) ([], false, y, e)).2.2.2] [false]
    cap cap2 x.length hw hW
    ((copyLoopCost_mono x.length hlen).trans hcap2.2)
  rw [← overlay_stream] at hc
  have hall := (hf.seq hc).enlarge (m := symCost G.length x.length) (by
    unfold symCost
    have := copyLoopCost_mono x.length hlen
    omega)
  rw [overlay_stream, overlay_stream] at hall
  exact hall

end NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
