import Proof.Wire_3_5.CompilerMachineCancelRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The state of the loop over the words to insert -/

/-- The running list with the scratch contents of the insertion machine's tapes. -/
structure AllState where
  G : List (List Bool)
  staleS : List Bool
  O : List Bool
  xp : List Bool
  y : List Bool
  e : Bool

/-- One word inserted. -/
def allStep (st : AllState) (x : List Bool) : AllState :=
  ⟨symInsertW st.G x, (symNext st.G st.staleS st.O x st.y st.e).1,
    streamTape (symInsertW st.G x) (symNext st.G st.staleS st.O x st.y st.e).2.1, x,
    (symNext st.G st.staleS st.O x st.y st.e).2.2.1, (symNext st.G st.staleS st.O x st.y st.e).2.2.2⟩

theorem foldl_allStep_G : ∀ (Ls : List (List Bool)) (st : AllState), (Ls.foldl allStep st).G = Ls.foldl symInsertW st.G
  | [], _ => rfl
  | x :: Ls, st => by rw [List.foldl_cons, foldl_allStep_G Ls, List.foldl_cons]; rfl

/-- The widths are kept: every word of the running list, the last word and the register have width `W`, and the list
grows by at most one word per insertion. -/
def AllInv (W n : ℕ) (st : AllState) : Prop :=
  (∀ r ∈ st.G, r.length = W) ∧ st.xp.length = W ∧ st.y.length = W ∧ st.G.length ≤ n

theorem allStep_inv (W n : ℕ) (st : AllState) (x : List Bool) (hx : x.length = W) (h : AllInv W n st) :
    AllInv W (n + 1) (allStep st x) := by
  obtain ⟨hG, _, hy, hn⟩ := h
  refine ⟨?_, hx, ?_, ?_⟩
  · intro r hr
    rcases mem_symInsertW st.G x r hr with h | h
    · exact hG r h
    · rw [h, hx]
  · show (symNext st.G st.staleS st.O x st.y st.e).2.2.1.length = W
    rw [symNext_y_length st.G st.staleS st.O x st.y st.e (fun r hr => (hG r hr).trans hx.symm) (hy.trans hx.symm), hx]
  · exact (length_symInsertW_le st.G x).trans (by omega)

theorem foldl_allStep_inv (W : ℕ) : ∀ (Ls : List (List Bool)) (n : ℕ) (st : AllState),
    (∀ x ∈ Ls, x.length = W) → AllInv W n st → AllInv W (n + Ls.length) (Ls.foldl allStep st)
  | [], n, st, _, h => by simpa using h
  | x :: Ls, n, st, hL, h => by
    rw [List.foldl_cons, List.length_cons, show n + (Ls.length + 1) = n + 1 + Ls.length by omega]
    exact foldl_allStep_inv W Ls (n + 1) (allStep st x) (fun y hy => hL y (List.mem_cons_of_mem x hy))
      (allStep_inv W n st x (hL x List.mem_cons_self) h)

/-! ## The machines -/

def sLoadLX : Fin 3 → Fin 9 := ![8, 2, 6]
def sNudgeL : Fin 1 → Fin 9 := ![8]
def sSym : Fin 8 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7]
def selL : Fin 9 → Bool := ![false, false, false, false, false, false, false, false, true]

noncomputable def loadLXD := RecoveryFocus.machine sLoadLX loadM
noncomputable def nudgeLD := RecoveryFocus.machine sNudgeL nudgeM
noncomputable def symD := RecoveryFocus.machine sSym symM

/-- The loop body: load the next word into `X`, step past it, insert it. -/
noncomputable def allBodyM := Composition.machine (Composition.machine loadLXD nudgeLD) symD
noncomputable def allLoopM := StreamController.machine allBodyM 8

/-- **The insert-all machine**: the loop over the words, then the `Ls` head back to cell 0. -/
noncomputable def insertAllM := MaskedReset.machine allLoopM selL

/-! ## One word -/

/-- The loop's heads: every head at cell 0 but the words' cursor. -/
def aH (p : ℕ) : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, p]

/-- The loop's tapes in state `st`. -/
def aA (Lt : List Bool) (cap cap2 : ℕ) (st : AllState) : Fin 9 → List Bool :=
  ![streamTape st.G st.staleS, st.O, frame st.xp, frame st.y, [st.e], [false], List.replicate cap false,
    List.replicate cap2 false, Lt]

/-- The per-word cost bound, for running lists of at most `n` words of width `W`. -/
def allCost (n W : ℕ) : ℕ := 2 * (2 * W + 1) + 2 + 1 + 1 + 1 + symCost n W

theorem filterLoopCost_mono {n m : ℕ} (W : ℕ) (h : n ≤ m) : filterLoopCost n W ≤ filterLoopCost m W := by
  unfold filterLoopCost
  have := Nat.mul_le_mul_right (12 * W + 18 + 2) h
  omega

theorem symCost_mono {n m : ℕ} (W : ℕ) (h : n ≤ m) : symCost n W ≤ symCost m W := by
  unfold symCost
  have h1 := filterLoopCost_mono W h
  have h2 := copyLoopCost_mono W (Nat.add_le_add_right h 1)
  omega

theorem sLoadLX_inj : Function.Injective sLoadLX := by decide

theorem install_sLoadLX (A : Fin 9 → List Bool) (v : Fin 3 → List Bool) :
    install sLoadLX A v = ![A 0, A 1, v 1, A 3, A 4, A 5, v 2, A 7, v 0] := by
  funext i
  fin_cases i
  · exact install_other sLoadLX A v 0 (by decide)
  · exact install_other sLoadLX A v 1 (by decide)
  · exact install_slot sLoadLX sLoadLX_inj A v 1
  · exact install_other sLoadLX A v 3 (by decide)
  · exact install_other sLoadLX A v 4 (by decide)
  · exact install_other sLoadLX A v 5 (by decide)
  · exact install_slot sLoadLX sLoadLX_inj A v 2
  · exact install_other sLoadLX A v 7 (by decide)
  · exact install_slot sLoadLX sLoadLX_inj A v 0

theorem dockH_sLoadLX (H : Fin 9 → ℕ) (v : Fin 3 → ℕ) :
    dockH sLoadLX H v = ![H 0, H 1, v 1, H 3, H 4, H 5, v 2, H 7, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other sLoadLX H v 0 (by decide)
  · exact dockH_other sLoadLX H v 1 (by decide)
  · exact dockH_slot sLoadLX sLoadLX_inj H v 1
  · exact dockH_other sLoadLX H v 3 (by decide)
  · exact dockH_other sLoadLX H v 4 (by decide)
  · exact dockH_other sLoadLX H v 5 (by decide)
  · exact dockH_slot sLoadLX sLoadLX_inj H v 2
  · exact dockH_other sLoadLX H v 7 (by decide)
  · exact dockH_slot sLoadLX sLoadLX_inj H v 0

theorem sNudgeL_inj : Function.Injective sNudgeL := by decide

theorem install_sNudgeL (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install sNudgeL A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 0] := by
  funext i
  fin_cases i
  · exact install_other sNudgeL A v 0 (by decide)
  · exact install_other sNudgeL A v 1 (by decide)
  · exact install_other sNudgeL A v 2 (by decide)
  · exact install_other sNudgeL A v 3 (by decide)
  · exact install_other sNudgeL A v 4 (by decide)
  · exact install_other sNudgeL A v 5 (by decide)
  · exact install_other sNudgeL A v 6 (by decide)
  · exact install_other sNudgeL A v 7 (by decide)
  · exact install_slot sNudgeL sNudgeL_inj A v 0

theorem dockH_sNudgeL (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH sNudgeL H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other sNudgeL H v 0 (by decide)
  · exact dockH_other sNudgeL H v 1 (by decide)
  · exact dockH_other sNudgeL H v 2 (by decide)
  · exact dockH_other sNudgeL H v 3 (by decide)
  · exact dockH_other sNudgeL H v 4 (by decide)
  · exact dockH_other sNudgeL H v 5 (by decide)
  · exact dockH_other sNudgeL H v 6 (by decide)
  · exact dockH_other sNudgeL H v 7 (by decide)
  · exact dockH_slot sNudgeL sNudgeL_inj H v 0

theorem sSym_inj : Function.Injective sSym := by decide

theorem install_sSym (A : Fin 9 → List Bool) (v : Fin 8 → List Bool) :
    install sSym A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, A 8] := by
  funext i
  fin_cases i
  · exact install_slot sSym sSym_inj A v 0
  · exact install_slot sSym sSym_inj A v 1
  · exact install_slot sSym sSym_inj A v 2
  · exact install_slot sSym sSym_inj A v 3
  · exact install_slot sSym sSym_inj A v 4
  · exact install_slot sSym sSym_inj A v 5
  · exact install_slot sSym sSym_inj A v 6
  · exact install_slot sSym sSym_inj A v 7
  · exact install_other sSym A v 8 (by decide)

theorem dockH_sSym (H : Fin 9 → ℕ) (v : Fin 8 → ℕ) :
    dockH sSym H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_slot sSym sSym_inj H v 0
  · exact dockH_slot sSym sSym_inj H v 1
  · exact dockH_slot sSym sSym_inj H v 2
  · exact dockH_slot sSym sSym_inj H v 3
  · exact dockH_slot sSym sSym_inj H v 4
  · exact dockH_slot sSym sSym_inj H v 5
  · exact dockH_slot sSym sSym_inj H v 6
  · exact dockH_slot sSym sSym_inj H v 7
  · exact dockH_other sSym H v 8 (by decide)

section Docked
variable (cap cap2 : ℕ) (T0 T1 T2 T3 T4 T5 T8 : List Bool) (p : ℕ)

theorem loadLX_step (pre x post xp : List Bool) (hl : xp.length = x.length) (hcap : 2 * x.length + 1 ≤ cap) :
    Step loadLXD (2 * (2 * x.length + 1) + 2) ![0, 0, 0, 0, 0, 0, 0, 0, pre.length]
      ![T0, T1, frame xp, T3, T4, T5, List.replicate cap false, List.replicate cap2 false, pre ++ frame x ++ post]
      ![0, 0, 0, 0, 0, 0, 0, 0, pre.length + 2 * x.length]
      ![T0, T1, frame x, T3, T4, T5, List.replicate cap false, List.replicate cap2 false, pre ++ frame x ++ post] := by
  have e0 := loadStep pre x post (frame xp) cap hcap
  rw [overlay_exact _ _ (by simp [frame_length, hl])] at e0
  have e1 := dockRun e0 sLoadLX sLoadLX_inj ![0, 0, 0, 0, 0, 0, 0, 0, pre.length]
    ![T0, T1, frame xp, T3, T4, T5, List.replicate cap false, List.replicate cap2 false, pre ++ frame x ++ post]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_sLoadLX, dockH_sLoadLX] at e1
  exact e1

theorem nudgeL_step :
    Step nudgeLD 1 ![0, 0, 0, 0, 0, 0, 0, 0, p]
      ![T0, T1, T2, T3, T4, T5, List.replicate cap false, List.replicate cap2 false, T8]
      ![0, 0, 0, 0, 0, 0, 0, 0, p + 1]
      ![T0, T1, T2, T3, T4, T5, List.replicate cap false, List.replicate cap2 false, T8] := by
  have e1 := dockRun (nudge_run T8 p) sNudgeL sNudgeL_inj ![0, 0, 0, 0, 0, 0, 0, 0, p]
    ![T0, T1, T2, T3, T4, T5, List.replicate cap false, List.replicate cap2 false, T8]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_sNudgeL, dockH_sNudgeL] at e1
  exact e1

theorem symD_step (G : List (List Bool)) (staleS BW x y : List Bool) (e : Bool)
    (hG : ∀ r ∈ G, r.length = x.length) (hy : y.length = x.length) (hx : x ≠ []) (hcap : 2 * x.length + 1 ≤ cap)
    (hcap2 : filterLoopCost G.length x.length ≤ cap2 ∧ copyLoopCost (G.length + 1) x.length ≤ cap2) :
    Step symD (symCost G.length x.length) ![0, 0, 0, 0, 0, 0, 0, 0, p]
      ![streamTape G staleS, BW, frame x, frame y, [e], [false], List.replicate cap false, List.replicate cap2 false, T8]
      ![0, 0, 0, 0, 0, 0, 0, 0, p]
      ![streamTape (symInsertW G x) (symNext G staleS BW x y e).1,
        streamTape (symInsertW G x) (symNext G staleS BW x y e).2.1, frame x, frame (symNext G staleS BW x y e).2.2.1,
        [(symNext G staleS BW x y e).2.2.2], [false], List.replicate cap false, List.replicate cap2 false, T8] := by
  have e1 := dockKeep (sym_run G staleS BW x y e cap cap2 hG hy hx hcap hcap2) sSym sSym_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, p]
    ![streamTape G staleS, BW, frame x, frame y, [e], [false], List.replicate cap false, List.replicate cap2 false, T8]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_sSym] at e1
  exact e1

end Docked

theorem all_body (pre x post : List Bool) (cap cap2 W n : ℕ) (st : AllState)
    (hx : x.length = W) (hW : 1 ≤ W) (h : AllInv W n st) (hcap : 2 * W + 1 ≤ cap)
    (hcap2 : filterLoopCost n W ≤ cap2 ∧ copyLoopCost (n + 1) W ≤ cap2) :
    Step allBodyM (allCost n W) (aH pre.length) (aA (pre ++ frame x ++ post) cap cap2 st)
      (aH (pre.length + (2 * x.length + 1))) (aA (pre ++ frame x ++ post) cap cap2 (allStep st x)) := by
  subst hx
  obtain ⟨hG, hxp, hy, hn⟩ := h
  have s1 := loadLX_step cap cap2 (streamTape st.G st.staleS) st.O (frame st.y) [st.e] [false] pre x post st.xp hxp
    (by omega)
  have s2 := nudgeL_step cap cap2 (streamTape st.G st.staleS) st.O (frame x) (frame st.y) [st.e] [false]
    (pre ++ frame x ++ post) (pre.length + 2 * x.length)
  have s3 := symD_step cap cap2 (pre ++ frame x ++ post) (pre.length + 2 * x.length + 1) st.G st.staleS st.O x st.y
    st.e hG hy (by intro h; rw [h] at hW; simp at hW) (by omega)
    ⟨(filterLoopCost_mono x.length hn).trans hcap2.1,
      (copyLoopCost_mono x.length (Nat.succ_le_succ hn)).trans hcap2.2⟩
  have hall := (s1.seq s2).seq s3
  refine (hall.enlarge ?_).congr ?_ rfl
  · unfold allCost
    have := symCost_mono x.length hn
    omega
  · funext i; fin_cases i <;> simp [aH]
    all_goals omega

/-! ## The loop over the words, and its reset -/

theorem allCost_mono {n m : ℕ} (W : ℕ) (h : n ≤ m) : allCost n W ≤ allCost m W := by
  unfold allCost
  have := symCost_mono W h
  omega

/-- **The stream loop over the words to insert.** -/
theorem all_loop (Ls : List (List Bool)) (staleL : List Bool) (cap cap2 W n0 : ℕ) (s0 : AllState)
    (hL : ∀ x ∈ Ls, x.length = W) (hW : 1 ≤ W) (h0 : AllInv W n0 s0) (hcap : 2 * W + 1 ≤ cap)
    (hcap2 : filterLoopCost (n0 + Ls.length) W ≤ cap2 ∧ copyLoopCost (n0 + Ls.length + 1) W ≤ cap2) :
    Step allLoopM (Ls.length * (allCost (n0 + Ls.length) W + 2) + 1) (aH 0) (aA (streamTape Ls staleL) cap cap2 s0)
      (aH (Ls.flatMap frame).length) (aA (streamTape Ls staleL) cap cap2 (Ls.foldl allStep s0)) := by
  refine streamRun allBodyM 8 Ls staleL (fun r hr h => by have := hL r hr; rw [h] at this; simp at this; omega)
    allStep s0 (fun _ p => aH p) (fun st => aA (streamTape Ls staleL) cap cap2 st) (fun _ => rfl) (fun _ _ => rfl)
    (allCost (n0 + Ls.length) W) ?_
  intro j hj
  have hlen := hL _ (List.getElem_mem hj)
  have hst : (Ls.take (j + 1)).foldl allStep s0 = allStep ((Ls.take j).foldl allStep s0) Ls[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  have hinv := foldl_allStep_inv W (Ls.take j) n0 s0 (fun x hx => hL x (List.mem_of_mem_take hx)) h0
  have hjl : n0 + (Ls.take j).length ≤ n0 + Ls.length := by simp
  have hb := all_body ((Ls.take j).flatMap frame) Ls[j] ((Ls.drop (j + 1)).flatMap frame ++ false :: staleL)
    cap cap2 W (n0 + (Ls.take j).length) ((Ls.take j).foldl allStep s0) hlen hW hinv hcap
    ⟨(filterLoopCost_mono W hjl).trans hcap2.1, (copyLoopCost_mono W (Nat.succ_le_succ hjl)).trans hcap2.2⟩
  rw [← streamTape_split Ls staleL j hj] at hb
  rw [hst, off_succ Ls j hj]
  exact hb.enlarge (allCost_mono W hjl)

/-- The cost of inserting `m` words of width `W` into a list of at most `n0` words. -/
def insertAllCost (m n0 W : ℕ) : ℕ := 2 * (m * (allCost (n0 + m) W + 2) + 1) + 2

theorem insertAll_run (Ls : List (List Bool)) (staleL : List Bool) (cap cap2 cap3 W n0 : ℕ) (s0 : AllState)
    (hL : ∀ x ∈ Ls, x.length = W) (hW : 1 ≤ W) (h0 : AllInv W n0 s0) (hcap : 2 * W + 1 ≤ cap)
    (hcap2 : filterLoopCost (n0 + Ls.length) W ≤ cap2 ∧ copyLoopCost (n0 + Ls.length + 1) W ≤ cap2)
    (hcap3 : Ls.length * (allCost (n0 + Ls.length) W + 2) + 1 ≤ cap3) :
    Step insertAllM (insertAllCost Ls.length n0 W) (fun _ => 0)
      ![streamTape s0.G s0.staleS, s0.O, frame s0.xp, frame s0.y, [s0.e], [false], List.replicate cap false,
        List.replicate cap2 false, streamTape Ls staleL, List.replicate cap3 false]
      (fun _ => 0)
      ![streamTape (Ls.foldl allStep s0).G (Ls.foldl allStep s0).staleS, (Ls.foldl allStep s0).O,
        frame (Ls.foldl allStep s0).xp, frame (Ls.foldl allStep s0).y, [(Ls.foldl allStep s0).e], [false],
        List.replicate cap false, List.replicate cap2 false, streamTape Ls staleL, List.replicate cap3 false] := by
  have h := all_loop Ls staleL cap cap2 W n0 s0 hL hW h0 hcap hcap2
  have hm := h.mask selL (by intro i hi; fin_cases i <;> simp_all [selL, aH]) hcap3
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## Twin -/

/-- The words `10`, `01`, `10` inserted into the empty list: the repeated word cancels. -/
theorem symInsertW_twin :
    [[true, false], [false, true], [true, false]].foldl symInsertW [] = [[false, true]] := by decide

end NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
