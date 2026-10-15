import Proof.Wire_3_5.CompilerMachineMasksExpand
import Proof.Wire_3_5.CompilerMachineCancelRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def mNudge : Fin 1 → Fin 11 := ![0]
def mLook : Fin 4 → Fin 11 := ![0, 1, 2, 10]
def mExp : Fin 9 → Fin 11 := ![3, 4, 2, 5, 6, 7, 8, 9, 10]
def mCopy : Fin 8 → Fin 11 := ![3, 4, 5, 6, 7, 1, 8, 10]

noncomputable def mNudgeD := RecoveryFocus.machine mNudge nudgeM
noncomputable def mLookD := RecoveryFocus.machine mLook lookupResetM
noncomputable def mExpD := RecoveryFocus.machine mExp expandM
noncomputable def mCopyD := RecoveryFocus.machine mCopy copyPassM

/-- One atom: step onto its code's first bit, look up its children, step past the code, expand, copy back. -/
noncomputable def atomM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine mNudgeD mLookD) mNudgeD) mExpD) mCopyD
noncomputable def atomLoopM := StreamController.machine atomM 0

theorem mNudge_inj : Function.Injective mNudge := by decide

theorem install_mNudge (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install mNudge A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_slot mNudge mNudge_inj A v 0
  · exact install_other mNudge A v 1 (by decide)
  · exact install_other mNudge A v 2 (by decide)
  · exact install_other mNudge A v 3 (by decide)
  · exact install_other mNudge A v 4 (by decide)
  · exact install_other mNudge A v 5 (by decide)
  · exact install_other mNudge A v 6 (by decide)
  · exact install_other mNudge A v 7 (by decide)
  · exact install_other mNudge A v 8 (by decide)
  · exact install_other mNudge A v 9 (by decide)
  · exact install_other mNudge A v 10 (by decide)

theorem dockH_mNudge (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH mNudge H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_slot mNudge mNudge_inj H v 0
  · exact dockH_other mNudge H v 1 (by decide)
  · exact dockH_other mNudge H v 2 (by decide)
  · exact dockH_other mNudge H v 3 (by decide)
  · exact dockH_other mNudge H v 4 (by decide)
  · exact dockH_other mNudge H v 5 (by decide)
  · exact dockH_other mNudge H v 6 (by decide)
  · exact dockH_other mNudge H v 7 (by decide)
  · exact dockH_other mNudge H v 8 (by decide)
  · exact dockH_other mNudge H v 9 (by decide)
  · exact dockH_other mNudge H v 10 (by decide)

theorem mLook_inj : Function.Injective mLook := by decide

theorem install_mLook (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install mLook A v = ![v 0, v 1, v 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 3] := by
  funext i
  fin_cases i
  · exact install_slot mLook mLook_inj A v 0
  · exact install_slot mLook mLook_inj A v 1
  · exact install_slot mLook mLook_inj A v 2
  · exact install_other mLook A v 3 (by decide)
  · exact install_other mLook A v 4 (by decide)
  · exact install_other mLook A v 5 (by decide)
  · exact install_other mLook A v 6 (by decide)
  · exact install_other mLook A v 7 (by decide)
  · exact install_other mLook A v 8 (by decide)
  · exact install_other mLook A v 9 (by decide)
  · exact install_slot mLook mLook_inj A v 3

theorem dockH_mLook (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH mLook H v = ![v 0, v 1, v 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot mLook mLook_inj H v 0
  · exact dockH_slot mLook mLook_inj H v 1
  · exact dockH_slot mLook mLook_inj H v 2
  · exact dockH_other mLook H v 3 (by decide)
  · exact dockH_other mLook H v 4 (by decide)
  · exact dockH_other mLook H v 5 (by decide)
  · exact dockH_other mLook H v 6 (by decide)
  · exact dockH_other mLook H v 7 (by decide)
  · exact dockH_other mLook H v 8 (by decide)
  · exact dockH_other mLook H v 9 (by decide)
  · exact dockH_slot mLook mLook_inj H v 3

theorem mExp_inj : Function.Injective mExp := by decide

theorem install_mExp (A : Fin 11 → List Bool) (v : Fin 9 → List Bool) :
    install mExp A v = ![A 0, A 1, v 2, v 0, v 1, v 3, v 4, v 5, v 6, v 7, v 8] := by
  funext i
  fin_cases i
  · exact install_other mExp A v 0 (by decide)
  · exact install_other mExp A v 1 (by decide)
  · exact install_slot mExp mExp_inj A v 2
  · exact install_slot mExp mExp_inj A v 0
  · exact install_slot mExp mExp_inj A v 1
  · exact install_slot mExp mExp_inj A v 3
  · exact install_slot mExp mExp_inj A v 4
  · exact install_slot mExp mExp_inj A v 5
  · exact install_slot mExp mExp_inj A v 6
  · exact install_slot mExp mExp_inj A v 7
  · exact install_slot mExp mExp_inj A v 8

theorem dockH_mExp (H : Fin 11 → ℕ) (v : Fin 9 → ℕ) :
    dockH mExp H v = ![H 0, H 1, v 2, v 0, v 1, v 3, v 4, v 5, v 6, v 7, v 8] := by
  funext i
  fin_cases i
  · exact dockH_other mExp H v 0 (by decide)
  · exact dockH_other mExp H v 1 (by decide)
  · exact dockH_slot mExp mExp_inj H v 2
  · exact dockH_slot mExp mExp_inj H v 0
  · exact dockH_slot mExp mExp_inj H v 1
  · exact dockH_slot mExp mExp_inj H v 3
  · exact dockH_slot mExp mExp_inj H v 4
  · exact dockH_slot mExp mExp_inj H v 5
  · exact dockH_slot mExp mExp_inj H v 6
  · exact dockH_slot mExp mExp_inj H v 7
  · exact dockH_slot mExp mExp_inj H v 8

theorem mCopy_inj : Function.Injective mCopy := by decide

theorem install_mCopy (A : Fin 11 → List Bool) (v : Fin 8 → List Bool) :
    install mCopy A v = ![A 0, v 5, A 2, v 0, v 1, v 2, v 3, v 4, v 6, A 9, v 7] := by
  funext i
  fin_cases i
  · exact install_other mCopy A v 0 (by decide)
  · exact install_slot mCopy mCopy_inj A v 5
  · exact install_other mCopy A v 2 (by decide)
  · exact install_slot mCopy mCopy_inj A v 0
  · exact install_slot mCopy mCopy_inj A v 1
  · exact install_slot mCopy mCopy_inj A v 2
  · exact install_slot mCopy mCopy_inj A v 3
  · exact install_slot mCopy mCopy_inj A v 4
  · exact install_slot mCopy mCopy_inj A v 6
  · exact install_other mCopy A v 9 (by decide)
  · exact install_slot mCopy mCopy_inj A v 7

theorem dockH_mCopy (H : Fin 11 → ℕ) (v : Fin 8 → ℕ) :
    dockH mCopy H v = ![H 0, v 5, H 2, v 0, v 1, v 2, v 3, v 4, v 6, H 9, v 7] := by
  funext i
  fin_cases i
  · exact dockH_other mCopy H v 0 (by decide)
  · exact dockH_slot mCopy mCopy_inj H v 5
  · exact dockH_other mCopy H v 2 (by decide)
  · exact dockH_slot mCopy mCopy_inj H v 0
  · exact dockH_slot mCopy mCopy_inj H v 1
  · exact dockH_slot mCopy mCopy_inj H v 2
  · exact dockH_slot mCopy mCopy_inj H v 3
  · exact dockH_slot mCopy mCopy_inj H v 4
  · exact dockH_slot mCopy mCopy_inj H v 6
  · exact dockH_other mCopy H v 9 (by decide)
  · exact dockH_slot mCopy mCopy_inj H v 7

/-! ## One atom -/

/-- The running list with the scratch contents. -/
structure MState where
  L : List (List Bool)
  staleA : List Bool
  LB : List Bool
  Ea : List Bool
  R : List Bool
  R2 : List Bool
  R3 : List Bool

/-- The registers after expanding `st.L` by the children `E`. -/
def mfin (E : List (List Bool)) (st : MState) : List (List Bool) × List Bool × List Bool × List Bool :=
  st.L.foldl (outerStep E) ([], st.R, st.R2, st.R3)

/-- One atom substituted. -/
def mstep (Es : List (List (List Bool))) (st : MState) (a : ℕ) : MState :=
  ⟨expandW st.L (Es.getD a []),
    (streamTape st.L st.staleA).drop (((expandW st.L (Es.getD a [])).flatMap frame).length + 1),
    streamTape (expandW st.L (Es.getD a [])) (st.LB.drop (((expandW st.L (Es.getD a [])).flatMap frame).length + 1)),
    streamTape (Es.getD a []) (st.Ea.drop (((Es.getD a []).flatMap frame).length + 1)),
    (mfin (Es.getD a []) st).2.1, (mfin (Es.getD a []) st).2.2.1, (mfin (Es.getD a []) st).2.2.2⟩

def mH (p : ℕ) : Fin 11 → ℕ := ![p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def mA (Mt Tt : List Bool) (cap cap2 cap3 : ℕ) (st : MState) : Fin 11 → List Bool :=
  ![Mt, Tt, st.Ea, streamTape st.L st.staleA, st.LB, frame st.R, frame st.R2, frame st.R3, List.replicate cap false,
    List.replicate cap2 false, List.replicate cap3 false]

/-- The uniform cost of one atom: atoms below `P`, children at most `K`, running lists at most `N`, width `L`. -/
def atomCost (P K N L : ℕ) : ℕ :=
  1 + 1 + (2 * lookupCost P K L + 2) + 1 + 1 + 1 + (2 * expandLoopCost N K L + 2) + 1 + (2 * copyLoopCost N L + 2)

theorem expandW_length (Lw Ea : List (List Bool)) : (expandW Lw Ea).length = Lw.length * Ea.length := by
  induction Lw with
  | nil => simp [expandW]
  | cons U Lw ih =>
    simp only [expandW, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem expandW_widths (Lw Ea : List (List Bool)) (L : ℕ) (hLw : ∀ U ∈ Lw, U.length = L) (hE : ∀ e ∈ Ea, e.length = L) :
    ∀ r ∈ expandW Lw Ea, r.length = L := by
  intro r hr
  unfold expandW at hr
  obtain ⟨U, hU, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  unfold orW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hLw U hU, hE e he]), hLw U hU]

theorem mcapOK (P K N L : ℕ) : lookupCost P K L ≤ max (lookupCost P K L) (max (expandLoopCost N K L) (copyLoopCost N L)) ∧
    expandLoopCost N K L ≤ max (lookupCost P K L) (max (expandLoopCost N K L) (copyLoopCost N L)) ∧
    copyLoopCost N L ≤ max (lookupCost P K L) (max (expandLoopCost N K L) (copyLoopCost N L)) := by
  omega

theorem expandLoopCost_mono {m m' : ℕ} (K L : ℕ) (h : m ≤ m') : expandLoopCost m K L ≤ expandLoopCost m' K L := by
  unfold expandLoopCost
  have := Nat.mul_le_mul_right (outerCost K L + 2) h
  omega

theorem atom_step (P' post' : List Bool) (a : ℕ) (Es : List (List (List Bool))) (staleT : List Bool)
    (cap cap2 cap3 K N L : ℕ) (st : MState) (ha : a < Es.length)
    (hEs : ∀ E ∈ Es, (∀ r ∈ E, r.length = L) ∧ E.length ≤ K) (hL : 1 ≤ L)
    (hLw : ∀ U ∈ st.L, U.length = L) (hN : st.L.length ≤ N) (hN' : st.L.length * K ≤ N)
    (h1 : st.R.length = L) (h2 : st.R2.length = L) (h3 : st.R3.length = L) (hcap : 2 * L + 1 ≤ cap)
    (hcap2 : K * (innerCost L + 2) + 1 ≤ cap2)
    (hcap3 : max (lookupCost Es.length K L) (max (expandLoopCost N K L) (copyLoopCost N L)) ≤ cap3) :
    Step atomM (atomCost Es.length K N L) (mH P'.length)
      (mA (P' ++ pairsTape a ++ post') (tableTape Es staleT) cap cap2 cap3 st)
      (mH (P'.length + 2 * a + 2)) (mA (P' ++ pairsTape a ++ post') (tableTape Es staleT) cap cap2 cap3 (mstep Es st a)) := by
  obtain ⟨c1, c2, c3⟩ := mcapOK Es.length K N L
  have hget : Es.getD a [] = Es[a] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
  obtain ⟨hw, hk⟩ := hEs _ (List.getElem_mem ha)
  set Mt := P' ++ pairsTape a ++ post'
  set Tt := tableTape Es staleT
  set L' := expandW st.L Es[a]
  have hL'len : L'.length ≤ N := by
    rw [expandW_length]; exact (Nat.mul_le_mul_left _ hk).trans hN'
  have hL'w := expandW_widths st.L Es[a] L hLw hw
  -- step onto the code
  have s1 := dockRun (nudge_run Mt P'.length) mNudge mNudge_inj (mH P'.length)
    (mA Mt Tt cap cap2 cap3 st) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_mNudge, dockH_mNudge] at s1
  -- look up the children
  have e2 := lookup_run P' post' a Es staleT st.Ea K L cap3 ha hEs hL (c1.trans hcap3)
  have s2 := dockRun e2 mLook mLook_inj ![P'.length + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Mt, Tt, st.Ea, streamTape st.L st.staleA, st.LB, frame st.R, frame st.R2, frame st.R3, List.replicate cap false,
      List.replicate cap2 false, List.replicate cap3 false] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_mLook, dockH_mLook] at s2
  -- step past the code
  have s3 := dockRun (nudge_run Mt (P'.length + 2 * a + 1)) mNudge mNudge_inj
    ![P'.length + 2 * a + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Mt, Tt, streamTape Es[a] (st.Ea.drop ((Es[a].flatMap frame).length + 1)), streamTape st.L st.staleA, st.LB,
      frame st.R, frame st.R2, frame st.R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_mNudge, dockH_mNudge] at s3
  -- expand
  have e4 := expand_run st.L st.staleA st.LB Es[a] (st.Ea.drop ((Es[a].flatMap frame).length + 1)) st.R st.R2 st.R3
    cap cap2 cap3 K L hLw hw hk hL h1 h2 h3 hcap hcap2 ((expandLoopCost_mono K L hN).trans (c2.trans hcap3))
  have s4 := dockKeep e4 mExp mExp_inj ![P'.length + 2 * a + 1 + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Mt, Tt, streamTape Es[a] (st.Ea.drop ((Es[a].flatMap frame).length + 1)), streamTape st.L st.staleA, st.LB,
      frame st.R, frame st.R2, frame st.R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_mExp] at s4
  -- copy back
  obtain ⟨g1, g2, g3⟩ := foldl_outerStep_regs Es[a] L hw st.L ([], st.R, st.R2, st.R3) hLw h1 h2 h3
  have e5 := copy_pass L' (st.LB.drop ((L'.flatMap frame).length + 1)) (streamTape st.L st.staleA)
    (frame (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.1)
    (frame (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.2.1)
    (frame (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.2.2) Tt cap cap3 L hL'w hL
    ((copyLoopCost_mono L hL'len).trans (c3.trans hcap3))
  have s5 := dockKeep e5 mCopy mCopy_inj ![P'.length + 2 * a + 1 + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Mt, Tt, streamTape Es[a] (st.Ea.drop ((Es[a].flatMap frame).length + 1)), streamTape st.L st.staleA,
      streamTape L' (st.LB.drop ((L'.flatMap frame).length + 1)),
      frame (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.1,
      frame (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.2.1,
      frame (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.2.2, List.replicate cap false,
      List.replicate cap2 false, List.replicate cap3 false] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_mCopy, overlay_stream] at s5
  have hall := (((s1.seq s2).seq s3).seq s4).seq s5
  have hcost := expandLoopCost_mono K L hN
  have hcost2 := copyLoopCost_mono L hL'len
  have hms : mstep Es st a = ⟨L', (streamTape st.L st.staleA).drop ((L'.flatMap frame).length + 1),
      streamTape L' (st.LB.drop ((L'.flatMap frame).length + 1)),
      streamTape Es[a] (st.Ea.drop ((Es[a].flatMap frame).length + 1)),
      (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.1,
      (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.2.1,
      (st.L.foldl (outerStep Es[a]) ([], st.R, st.R2, st.R3)).2.2.2⟩ := by
    simp only [mstep, mfin, hget, L']
  rw [hms]
  refine (hall.enlarge (by unfold atomCost; omega)).congr ?_ ?_
  · funext i; fin_cases i <;> simp [mH]
  · funext i; fin_cases i <;> rfl

/-! ## The loop over the monomial's atoms -/

theorem pairsTape_head (a : ℕ) : ∃ l, pairsTape a = true :: l := by
  cases a with
  | zero => exact ⟨[false], rfl⟩
  | succ a => exact ⟨true :: ((List.replicate a [true, true]).flatten ++ [true, false]), by simp [pairsTape, List.replicate_succ]⟩

theorem codes_split (mono : List ℕ) (j : ℕ) (hj : j < mono.length) :
    mono.flatMap pairsTape = (mono.take j).flatMap pairsTape ++ pairsTape mono[j] ++ (mono.drop (j + 1)).flatMap pairsTape := by
  have e : mono = mono.take j ++ mono[j] :: mono.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  conv_lhs => rw [e]
  rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem pairsTape_length (a : ℕ) : (pairsTape a).length = 2 * a + 2 := by
  simp [pairsTape, List.length_flatten, List.sum_replicate]; omega

/-- **A uniform body once per atom code of a monomial**: the codes sit after a prefix `P`, then a `false`. -/
theorem codesRun {t s : ℕ} (body : Machine t s) (src : Fin t) (P : List Bool) (mono : List ℕ) (post : List Bool)
    {σ : Type} (f : σ → ℕ → σ) (s0 : σ) (bH : σ → ℕ → Fin t → ℕ) (bA : σ → Fin t → List Bool)
    (hsrcA : ∀ st, bA st src = P ++ mono.flatMap pairsTape ++ false :: post) (hsrcH : ∀ st p, bH st p src = p) (c : ℕ)
    (hstep : ∀ j, j < mono.length → Step body c
      (bH ((mono.take j).foldl f s0) (P.length + ((mono.take j).flatMap pairsTape).length)) (bA ((mono.take j).foldl f s0))
      (bH ((mono.take (j + 1)).foldl f s0) (P.length + ((mono.take (j + 1)).flatMap pairsTape).length))
      (bA ((mono.take (j + 1)).foldl f s0))) :
    Step (StreamController.machine body src) (mono.length * (c + 2) + 1) (bH s0 P.length) (bA s0)
      (bH (mono.foldl f s0) (P.length + (mono.flatMap pairsTape).length)) (bA (mono.foldl f s0)) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := mono.length
      H := fun j => bH ((mono.take j).foldl f s0) (P.length + ((mono.take j).flatMap pairsTape).length)
      A := fun j => bA ((mono.take j).foldl f s0)
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA ((mono.take j).foldl f s0) src)
          (bH ((mono.take j).foldl f s0) (P.length + ((mono.take j).flatMap pairsTape).length) src) = true
        rw [hsrcA, hsrcH, codes_split mono j hj]
        obtain ⟨l, hl⟩ := pairsTape_head mono[j]
        rw [hl]
        have := Streaming.read_append (P ++ (mono.take j).flatMap pairsTape)
          (l ++ (mono.drop (j + 1)).flatMap pairsTape ++ false :: post) true
        simpa [List.append_assoc] using this
      halt := by
        show readTapeBit (bA ((mono.take mono.length).foldl f s0) src)
          (bH ((mono.take mono.length).foldl f s0) (P.length + ((mono.take mono.length).flatMap pairsTape).length) src)
          = false
        rw [hsrcA, hsrcH, List.take_length]
        have := Streaming.read_append (P ++ mono.flatMap pairsTape) post false
        simpa [List.append_assoc] using this }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  have e0 : W.H 0 = bH s0 P.length := by simp [W]
  have e1 : W.A 0 = bA s0 := by simp [W]
  have e2 : W.H W.bound = bH (mono.foldl f s0) (P.length + (mono.flatMap pairsTape).length) := by
    simp only [W, List.take_length]
  have e3 : W.A W.bound = bA (mono.foldl f s0) := by simp only [W, List.take_length]
  rw [e0, e1, e2, e3] at hW
  exact hW

/-- The widths of the running list and the registers. -/
def MInv (L : ℕ) (st : MState) : Prop :=
  (∀ U ∈ st.L, U.length = L) ∧ st.R.length = L ∧ st.R2.length = L ∧ st.R3.length = L

theorem mstep_inv (Es : List (List (List Bool))) (L : ℕ) (hEs : ∀ E ∈ Es, ∀ r ∈ E, r.length = L) (st : MState) (a : ℕ)
    (ha : a < Es.length) (h : MInv L st) : MInv L (mstep Es st a) := by
  obtain ⟨hLw, h1, h2, h3⟩ := h
  have hget : Es.getD a [] = Es[a] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
  have hw := hEs _ (List.getElem_mem ha)
  obtain ⟨g1, g2, g3⟩ := foldl_outerStep_regs Es[a] L hw st.L ([], st.R, st.R2, st.R3) hLw h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ∀ U ∈ expandW st.L (Es.getD a []), U.length = L
    rw [hget]; exact expandW_widths st.L Es[a] L hLw hw
  · show (mfin (Es.getD a []) st).2.1.length = L
    rw [hget]; exact g1
  · show (mfin (Es.getD a []) st).2.2.1.length = L
    rw [hget]; exact g2
  · show (mfin (Es.getD a []) st).2.2.2.length = L
    rw [hget]; exact g3

theorem foldl_mstep (Es : List (List (List Bool))) (L K : ℕ) (hEs : ∀ E ∈ Es, (∀ r ∈ E, r.length = L) ∧ E.length ≤ K) :
    ∀ (mono : List ℕ) (st : MState), (∀ a ∈ mono, a < Es.length) → MInv L st →
      MInv L (mono.foldl (mstep Es) st) ∧ (mono.foldl (mstep Es) st).L.length ≤ st.L.length * K ^ mono.length
  | [], st, _, h => ⟨h, by simp⟩
  | a :: mono, st, hm, h => by
    have ha := hm a List.mem_cons_self
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_mstep Es L K hEs mono (mstep Es st a) (fun a' h' => hm a' (List.mem_cons_of_mem a h'))
      (mstep_inv Es L (fun E hE => (hEs E hE).1) st a ha h)
    refine ⟨h1, h2.trans ?_⟩
    have hget : Es.getD a [] = Es[a] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
    show (expandW st.L (Es.getD a [])).length * K ^ mono.length ≤ st.L.length * K ^ (a :: mono).length
    rw [hget, expandW_length, List.length_cons, pow_succ]
    have := (hEs _ (List.getElem_mem ha)).2
    calc st.L.length * Es[a].length * K ^ mono.length ≤ st.L.length * K * K ^ mono.length :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
      _ = st.L.length * (K ^ mono.length * K) := by ring

theorem foldl_mstep_L (Es : List (List (List Bool))) : ∀ (mono : List ℕ) (st : MState),
    (mono.foldl (mstep Es) st).L = mono.foldl (fun L a => expandW L (Es.getD a [])) st.L
  | [], _ => rfl
  | a :: mono, st => by rw [List.foldl_cons, foldl_mstep_L Es mono, List.foldl_cons]; rfl

/-- The cost of the loop over a monomial of `n` atoms. -/
def atomsCost (n P K L : ℕ) : ℕ := n * (atomCost P K (K ^ n) L + 2) + 1

theorem atoms_run (P post : List Bool) (mono : List ℕ) (Es : List (List (List Bool))) (staleT : List Bool)
    (cap cap2 cap3 K L : ℕ) (st0 : MState) (hmono : ∀ a ∈ mono, a < Es.length)
    (hEs : ∀ E ∈ Es, (∀ r ∈ E, r.length = L) ∧ E.length ≤ K) (hK : 1 ≤ K) (hL : 1 ≤ L) (h0 : MInv L st0)
    (hone : st0.L.length = 1)
    (hcap : 2 * L + 1 ≤ cap) (hcap2 : K * (innerCost L + 2) + 1 ≤ cap2)
    (hcap3 : max (lookupCost Es.length K L) (max (expandLoopCost (K ^ mono.length) K L) (copyLoopCost (K ^ mono.length) L))
      ≤ cap3) :
    Step atomLoopM (atomsCost mono.length Es.length K L) (mH P.length)
      (mA (P ++ mono.flatMap pairsTape ++ false :: post) (tableTape Es staleT) cap cap2 cap3 st0)
      (mH (P.length + (mono.flatMap pairsTape).length))
      (mA (P ++ mono.flatMap pairsTape ++ false :: post) (tableTape Es staleT) cap cap2 cap3 (mono.foldl (mstep Es) st0)) := by
  refine codesRun atomM 0 P mono post (mstep Es) st0 (fun _ p => mH p)
    (fun st => mA (P ++ mono.flatMap pairsTape ++ false :: post) (tableTape Es staleT) cap cap2 cap3 st)
    (fun _ => rfl) (fun _ _ => rfl) (atomCost Es.length K (K ^ mono.length) L) ?_
  intro j hj
  have hja := hmono _ (List.getElem_mem hj)
  have hst : (mono.take (j + 1)).foldl (mstep Es) st0 = mstep Es ((mono.take j).foldl (mstep Es) st0) mono[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  obtain ⟨⟨hLw, h1, h2, h3⟩, hlen⟩ := foldl_mstep Es L K hEs (mono.take j) st0
    (fun a ha => hmono a (List.mem_of_mem_take ha)) h0
  rw [hone, Nat.one_mul, List.length_take, Nat.min_eq_left hj.le] at hlen
  have hN : ((mono.take j).foldl (mstep Es) st0).L.length ≤ K ^ mono.length :=
    hlen.trans (Nat.pow_le_pow_right hK hj.le)
  have hN' : ((mono.take j).foldl (mstep Es) st0).L.length * K ≤ K ^ mono.length := by
    calc ((mono.take j).foldl (mstep Es) st0).L.length * K ≤ K ^ j * K := Nat.mul_le_mul_right _ hlen
      _ = K ^ (j + 1) := (pow_succ K j).symm
      _ ≤ K ^ mono.length := Nat.pow_le_pow_right hK hj
  have hb := atom_step (P ++ (mono.take j).flatMap pairsTape) ((mono.drop (j + 1)).flatMap pairsTape ++ false :: post)
    mono[j] Es staleT cap cap2 cap3 K (K ^ mono.length) L ((mono.take j).foldl (mstep Es) st0) hja hEs hL hLw hN hN'
    h1 h2 h3 hcap hcap2 hcap3
  have hsplit : P ++ (mono.take j).flatMap pairsTape ++ pairsTape mono[j] ++
      ((mono.drop (j + 1)).flatMap pairsTape ++ false :: post) = P ++ mono.flatMap pairsTape ++ false :: post := by
    rw [codes_split mono j hj]; simp [List.append_assoc]
  rw [hsplit] at hb
  rw [hst]
  have hpos : (P ++ (mono.take j).flatMap pairsTape).length + 2 * mono[j] + 2 =
      P.length + ((mono.take (j + 1)).flatMap pairsTape).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]
    simp [pairsTape_length]; omega
  rw [hpos] at hb
  simpa using hb

end NearCubicWires.WireExponent3_5.CompilerMachine.Masks
