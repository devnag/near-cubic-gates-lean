import Proof.Wire_3_5.SeedFixSplitT

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open NearCubicWires.BlockPlatform
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages JBody SplitT

namespace JEnum

/-! ## The state recursion and the banks between cells -/

/-- The cell's state before counter value `j`. -/
def stAt (X : JCtx) (S0 : JState) : ℕ → JState
  | 0 => S0
  | j + 1 => (at_ X (tOf X j)).jNext j (stAt X S0 j)

/-- The output before counter value `j`. -/
def outAt (X : JCtx) (j : ℕ) : SExpr := (List.range j).flatMap fun i => (at_ X (tOf X i)).emitJ i

theorem outAt_succ (X : JCtx) (j : ℕ) : outAt X (j + 1) = outAt X j ++ (at_ X (tOf X j)).emitJ j := by
  unfold outAt
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The bank before counter value `j`: the fields of `j − 1` (of `0` at the start), the state, the output. -/
def src (X : JCtx) (S0 : JState) (j : ℕ) : JT := (at_ X (tOf X (j - 1))).jt (j - 1) (stAt X S0 j) (outAt X j) 0

/-! ## The cell after its split: the cell words, the test, the group (JBody's `jWorkM` without its split) -/

noncomputable def restM := Composition.machine (Composition.machine (RecoveryFocus.machine slCells cellsM)
  (RecoveryFocus.machine slValid validM)) (branchM (8 : Fin 60) groupM (idle 60))

noncomputable def restCost (X : JCtx) (j : ℕ) (V : SExpr) : ℕ :=
  (2 * cellsInnerCost X.P.kh + 2) + 1 + (2 * validInnerCost 8 X.P.ell + 2) + 1 +
    ((if X.validJ j = true then groupCost X j V else 0) + 2)

/-- The bank after the split of `j`: the fields of `j`, everything else of `jp`. -/
def splitBank (X : JCtx) (jp j : ℕ) (S : JState) (V : SExpr) : JT :=
  { X.jt jp S V 0 with BT := frame (binary 8 j), AL := (alphasOf X.P.ell j).flatMap frame ++ [false],
                       DG := (digsOf X.P.ell X.P.kh j).flatMap frame ++ [false],
                       DN := ((digsOf X.P.ell X.P.kh j).tail ++ [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++
                         [false] }

theorem clW_length (X : JCtx) (i : ℕ) : (X.clW i).length = 8 * (2 * (2 * X.P.kh) + 1) + 1 := by
  unfold JCtx.clW
  rw [List.length_append, flatMap_frame_length (2 * X.P.kh) _ (csJ_width X i), csJ_length]; rfl

theorem rest_run (X : JCtx) (j jp : ℕ) (S : JState) (V : SExpr) (hc : CellOk X)
    (hg : X.validJ j = true → GroupOk X j S V) :
    Step restM (restCost X j V) (fun _ => 0) (splitBank X jp j S V).vec (fun _ => 0)
      (X.jt j (X.jNext j S) (V ++ X.emitJ j) 0).vec := by
  set T1 := splitBank X jp j S V
  -- 1: the cell words
  have h2 := stage_cells T1 X.P.kh X.c0 (digW X.P j 0) (digW X.P j 1) (digW X.P j 2) (digW X.P j 3) (digW X.P j 4)
    (digW X.P j 5) (digW X.P j 6) (digW X.P j 7) [false] [false]
    (by show (digsOf X.P.ell X.P.kh j).flatMap frame ++ [false] = _; rw [digsOf_eq])
    (by show ((digsOf X.P.ell X.P.kh j).tail ++ [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++ [false] = _
        rw [digsOf_eq]; rfl)
    rfl (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _)
    (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _) hc.hcells
  have eCL : cellsOut (digW X.P j 0) (digW X.P j 1) (digW X.P j 2) (digW X.P j 3) (digW X.P j 4) (digW X.P j 5)
      (digW X.P j 6) (digW X.P j 7) ++ [false] = X.clW j := by
    rw [cellsOut_eq]; unfold JCtx.clW JCtx.csJ; rw [List.flatMap_map]
  rw [eCL, overlay_same _ T1.CL (by show _ = (X.clW jp).length; rw [clW_length, clW_length])] at h2
  set T2 := { T1 with CL := X.clW j }
  -- 2: the labels below `Q`
  have h3 := stage_valid T2 X.P.ell X.c0 X.c1 ((X.asJ jp).getD 7 []) X.q [false] (cmpQ X.q ((X.asJ jp).getD 7 []))
    (X.validJ jp) (X.asJ j)
    (by show _ = List.replicate (alphasOf X.P.ell j).length true ++ [false]; rw [alphasOf_length]; rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl (asJ_width X j) (lab_width X jp) (binary_length _ _) hc.hv0
    (by show validInnerCost (alphasOf X.P.ell j).length X.P.ell ≤ X.c1; rw [alphasOf_length]; exact hc.hv1)
  have eL : (X.asJ j).length = 8 := alphasOf_length _ _
  rw [eL] at h3
  have eT3 : ({ T2 with LAB := frame (labAt ((X.asJ jp).getD 7 []) (X.asJ j) 8),
                        CC := [ccAt (cmpQ X.q ((X.asJ jp).getD 7 [])) X.q (X.asJ j) 8],
                        V := [(X.asJ j).all (cmpQ X.q)] } : JT) = X.jt j S V 0 := rfl
  rw [eT3] at h3
  -- 3: the group, if the labels are valid
  have h4 : Step (branchM (8 : Fin 60) groupM (idle 60)) ((if X.validJ j = true then groupCost X j V else 0) + 2)
      (fun _ => 0) (X.jt j S V 0).vec (fun _ => 0) (X.jt j (X.jNext j S) (V ++ X.emitJ j) 0).vec := by
    by_cases hv : X.validJ j = true
    · rw [if_pos hv]
      exact branch_true (8 : Fin 60) (idle 60) (group_run' X j S V 0 hv (hg hv))
        (by show readTapeBit [X.validJ j] 0 = true; rw [hv]; rfl)
    · rw [if_neg hv]
      have eF : X.jNext j S = S := by unfold JCtx.jNext; rw [if_neg hv]
      have eV : X.emitJ j = [] := by unfold JCtx.emitJ; rw [if_neg (fun h => hv h.1)]
      rw [eF, eV, List.append_nil]
      exact branch_false (8 : Fin 60) groupM (read_idle (fun _ => 0) (X.jt j S V 0).vec)
        (by show readTapeBit [X.validJ j] 0 = false; simp only [Bool.not_eq_true] at hv; rw [hv]; rfl)
  unfold restCost
  exact (h2.seq h3).seq h4

/-! ## The cell -/

/-- **The cell body**: the split with the state word, the rest (on the bank), the counter increment. -/
noncomputable def bodyT := Composition.machine (Composition.machine (RecoveryFocus.machine slSplitT splitTM)
  (TapeEmbedding.machine 4 restM)) (RecoveryFocus.machine slInc (Rewind.machine BinaryIncrement.machine))

noncomputable def cellCost (X : JCtx) (j : ℕ) (V : SExpr) : ℕ :=
  splitTCost X.P.ell X.P.kh X.TWd + 1 + restCost (at_ X (tOf X j)) j V + 1 + (2 * (wT X + 1) + 2)

/-- The split's capacities beyond JBody's (the state word). -/
structure SplitOk (X : JCtx) : Prop where
  hT : X.TWd * (2 + 2) + 1 ≤ X.c0
  hc3 : ((2 * splitFieldsCost X.P.ell X.P.kh + 2) + 1 + splitRotCost X.P.kh) + 1 + (1 * (fieldCost X.TWd + 2) + 1)
    ≤ X.c3

theorem addCases_zero : (Fin.addCases (m := 60) (n := 4) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0)) =
    fun _ => 0 := by
  funext i
  refine Fin.addCases (motive := fun i => Fin.addCases (m := 60) (n := 4) (motive := fun _ => ℕ) (fun _ => 0)
    (fun _ => 0) i = 0) (fun k => ?_) (fun k => ?_) i <;> simp

theorem frame_binary_length (w a : ℕ) : (frame (binary w a)).length = 2 * w + 1 := by
  rw [frame_length, binary_length]

/-- The bank of context `at_ X t` is the bank of any other state's context with the state word replaced. -/
theorem jt_at (X : JCtx) (t t' j : ℕ) (S : JState) (V : SExpr) (c : ℕ) :
    ({ (at_ X t).jt j S V c with TW := frame (binary X.TWd t') } : JT) = (at_ X t').jt j S V c := rfl

theorem cellOk_at (X : JCtx) (t : ℕ) (h : CellOk X) : CellOk (at_ X t) :=
  ⟨h.hℓ, h.hl, h.hk, h.hl2, h.hk2, h.hr2, h.hcM1, h.hcM2, h.hcells, h.hv0, h.hv1⟩

theorem cell_run (X : JCtx) (S0 : JState) (j : ℕ) (hj : j < 2 ^ wT X) (hc : CellOk X) (hs : SplitOk X)
    (hg : (at_ X (tOf X j)).validJ j = true → GroupOk (at_ X (tOf X j)) j (stAt X S0 j) (outAt X j)) :
    Step bodyT (cellCost X j (outAt X j)) (fun _ => 0) (lay X (src X S0 j) j) (fun _ => 0)
      (lay X (src X S0 (j + 1)) (j + 1)) := by
  -- 1: the split
  have h1 := stage_splitT X (src X S0 j) j X.c0 X.c1 X.c2 X.c3 rfl rfl rfl rfl rfl rfl rfl rfl rfl hc.hℓ hc.hl hc.hk
    hs.hT hc.hl2 hc.hk2 hc.hr2 hc.hcM1 hs.hc3
  have hdg : ∀ i, ((digsOf X.P.ell X.P.kh i).flatMap frame ++ [false]).length = 8 * (2 * X.P.kh + 1) + 1 := by
    intro i
    rw [List.length_append, flatMap_frame_length X.P.kh _ (digs_width _ _ i), digsOf_length]; rfl
  have hdn : ∀ i, (((digsOf X.P.ell X.P.kh i).tail ++ [(digsOf X.P.ell X.P.kh i).headD []]).flatMap frame ++
      [false]).length = 8 * (2 * X.P.kh + 1) + 1 := by
    intro i
    rw [List.length_append, flatMap_frame_length X.P.kh _ (rot_width _ _ i), rot_length]; rfl
  have hal : ∀ i, ((alphasOf X.P.ell i).flatMap frame ++ [false]).length = 8 * (2 * X.P.ell + 1) + 1 := by
    intro i
    rw [List.length_append, flatMap_frame_length X.P.ell (alphasOf X.P.ell i) (fields8_width _ _), alphasOf_length]; rfl
  rw [overlay_same (frame (binary 8 j)) (src X S0 j).BT
      (by show _ = (frame (binary 8 (j - 1))).length; rw [frame_binary_length, frame_binary_length]),
    overlay_same _ (src X S0 j).AL
      (by show _ = ((alphasOf X.P.ell (j - 1)).flatMap frame ++ [false]).length; rw [hal, hal]),
    overlay_same _ (src X S0 j).DG
      (by show _ = ((digsOf X.P.ell X.P.kh (j - 1)).flatMap frame ++ [false]).length; rw [hdg, hdg]),
    overlay_same _ (src X S0 j).DN (by show _ = (((digsOf X.P.ell X.P.kh (j - 1)).tail ++
        [(digsOf X.P.ell X.P.kh (j - 1)).headD []]).flatMap frame ++ [false]).length; rw [hdn, hdn]),
    overlay_same (frame (binary X.TWd (tOf X j))) (src X S0 j).TW
      (by show _ = (frame (binary X.TWd (tOf X (j - 1)))).length; rw [frame_binary_length, frame_binary_length])] at h1
  have e1 : ({ src X S0 j with BT := frame (binary 8 j), AL := (alphasOf X.P.ell j).flatMap frame ++ [false],
                               DG := (digsOf X.P.ell X.P.kh j).flatMap frame ++ [false],
                               DN := ((digsOf X.P.ell X.P.kh j).tail ++
                                 [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++ [false],
                               TW := frame (binary X.TWd (tOf X j)) } : JT) =
      splitBank (at_ X (tOf X j)) (j - 1) j (stAt X S0 j) (outAt X j) := by
    unfold splitBank src
    rw [← jt_at X (tOf X (j - 1)) (tOf X j)]
    rfl
  rw [e1] at h1
  -- 2: the rest, on the bank
  have h2 := (rest_run (at_ X (tOf X j)) j (j - 1) (stAt X S0 j) (outAt X j) (cellOk_at X _ hc) hg).embed
    (fun _ : Fin 4 => 0) (ext X j)
  rw [addCases_zero] at h2
  -- 3: the increment
  have h3 := stage_inc X ((at_ X (tOf X j)).jt j ((at_ X (tOf X j)).jNext j (stAt X S0 j))
    (outAt X j ++ (at_ X (tOf X j)).emitJ j) 0) j hj
  have e3 : (at_ X (tOf X j)).jt j ((at_ X (tOf X j)).jNext j (stAt X S0 j)) (outAt X j ++ (at_ X (tOf X j)).emitJ j) 0 =
      src X S0 (j + 1) := by
    unfold src
    rw [Nat.add_sub_cancel, outAt_succ]
    rfl
  exact (h1.seq h2).seq (h3.congr rfl (congrArg (fun T => lay X T (j + 1)) e3))

/-! ## The loop of cells over `j' < bound` -/

/-- A uniform cell body at a uniform cost bound `K` (`Step.enlarge`), as a bounded loop. -/
noncomputable def cellsOf {s : ℕ} (M : Machine 64 s) (K bound : ℕ) (D : ℕ → Fin 64 → List Bool)
    (h : ∀ j, j < bound → Step M K (fun _ => 0) (D j) (fun _ => 0) (D (j + 1))) : Cells 64 s where
  body := M
  cost := K
  bound := bound
  source := fun j _ => ⟨M.start, fun _ => 0, D j⟩
  emit := fun _ => []
  entry := fun _ _ _ => rfl
  step := fun j hj _ => h j hj

/-- **The loop as one `Step`**: from the bank before `0` to the bank before `bound`. -/
theorem loop_run {s : ℕ} (M : Machine 64 s) (K bound : ℕ) (D : ℕ → Fin 64 → List Bool)
    (h : ∀ j, j < bound → Step M K (fun _ => 0) (D j) (fun _ => 0) (D (j + 1))) :
    Step (CloseoutRowsDegreeLoop.machine M) (bound * (K + 3) + 3)
      (Fin.addCases (fun _ : Fin 64 => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (D 0) (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound))
      (Fin.addCases (fun _ : Fin 64 => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (D bound) (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound)) :=
  (cellsOf M K bound D h).loopStep []

/-- **The enumeration**: from the bank before counter value `0` to the bank before `nT·2^{w₀}`, whose output tape
holds `outAt X (nT·2^{w₀})`, at a uniform cell cost bound `K`. -/
theorem enum_run (X : JCtx) (S0 : JState) (nT K : ℕ) (hnT : nT ≤ 2 ^ X.TWd) (hc : CellOk X) (hs : SplitOk X)
    (hK : ∀ j, j < nT * 2 ^ X.w → cellCost X j (outAt X j) ≤ K)
    (hg : ∀ j, j < nT * 2 ^ X.w → (at_ X (tOf X j)).validJ j = true →
      GroupOk (at_ X (tOf X j)) j (stAt X S0 j) (outAt X j)) :
    Step (CloseoutRowsDegreeLoop.machine bodyT) (nT * 2 ^ X.w * (K + 3) + 3)
      (Fin.addCases (fun _ : Fin 64 => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (lay X (src X S0 0) 0)
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ X.w)))
      (Fin.addCases (fun _ : Fin 64 => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (lay X (src X S0 (nT * 2 ^ X.w)) (nT * 2 ^ X.w))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ X.w))) := by
  refine loop_run bodyT K (nT * 2 ^ X.w) (fun j => lay X (src X S0 j) j) fun j hj => ?_
  have hj' : j < 2 ^ wT X := by
    unfold wT
    rw [pow_add]
    calc j < nT * 2 ^ X.w := hj
      _ ≤ 2 ^ X.TWd * 2 ^ X.w := Nat.mul_le_mul_right _ hnT
      _ = 2 ^ X.w * 2 ^ X.TWd := Nat.mul_comm _ _
  exact (cell_run X S0 j hj' hc hs (hg j hj)).enlarge (hK j hj)

end JEnum

end NearCubicWires.WireExponent3_5.SeedFix
