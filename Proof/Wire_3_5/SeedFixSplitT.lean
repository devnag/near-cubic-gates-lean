import Proof.Wire_3_5.SeedFixJBody
import Proof.Wire_3_5.BlockEnumerate

/-! # C4.Sb, machine part 19: the counter split with the state word

The enumeration puts the state `t` into the counter (JEnum): counter value `j'` carries the signs, labels and walk
digits of `sampTermsT_flat` in its low `w₀ = 8 + 8ℓ + 8kh` bits and the state `t = j' / 2^{w₀}` in the next `TWd`
bits. This split writes JStages' four fields (sign word, label stream, digit stream, rotated digit stream) and, from
the counter's head at `w₀` onward, the state word `TW = frame (binary TWd t)` that the entry fetches read beside the
cell words (the target `cell ‖ t` of JBody). The bank is JBody's `JT` plus two rulers, the counter and its workspace (`lay`).

Paper quantities of the main type: the counter's fields, and its state `j' / 2^{w₀}` (`splitT_run`,
`stage_splitT`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open Split JBank JStages JBody

namespace SplitT

/-! ## The layout: the bank and two rulers -/

/-- The context at state `t`. -/
def at_ (X : JCtx) (t : ℕ) : JCtx := { X with t := t }

/-- The counter's width: the fields, then the state word. -/
def wT (X : JCtx) : ℕ := X.w + X.TWd

/-- The state of counter value `j`. -/
def tOf (X : JCtx) (j : ℕ) : ℕ := j / 2 ^ X.w

/-- The tapes beside the bank: a unit ruler, the state word's ruler, the counter `binary (wT+1) j` and the
increment's workspace. -/
def ext (X : JCtx) (j : ℕ) : Fin 4 → List Bool :=
  ![List.replicate 1 true ++ [false], List.replicate X.TWd true ++ [false], binary (wT X + 1) j,
    List.replicate (wT X + 1) false]

/-- The cell's tapes at counter value `j`: the bank (60 tapes; its own `C`, `CW` stay idle), then `ext`. -/
def lay (X : JCtx) (T : JT) (j : ℕ) : Fin 64 → List Bool := Fin.addCases (m := 60) (n := 4) T.vec (ext X j)

/-! ## The counter's fields -/

/-- The counter with the state word in its top bits. -/
theorem counter_splitT (ℓ kh TWd j : ℕ) :
    binary (8 + 8 * ℓ + 8 * kh + TWd + 1) j = binary 8 j ++ (alphasOf ℓ j).flatten ++
      ((digsOf ℓ kh j).flatten ++ (binary TWd (j / 2 ^ (8 + 8 * ℓ + 8 * kh)) ++
        binary 1 (j / 2 ^ (8 + 8 * ℓ + 8 * kh + TWd)))) := by
  unfold alphasOf digsOf
  rw [binary_add_split, binary_add_split, binary_add_split, binary_add_split, fields8_flatten, fields8_flatten]
  simp only [List.append_assoc]

theorem prefix_length (ℓ kh j : ℕ) :
    (binary 8 j ++ (alphasOf ℓ j).flatten ++ (digsOf ℓ kh j).flatten).length = 8 + 8 * ℓ + 8 * kh := by
  unfold alphasOf digsOf
  rw [fields8_flatten, fields8_flatten]
  simp only [List.length_append, binary_length]

/-- JStages' fields from any counter tape that starts with the fields of `j`. -/
theorem split_fieldsG (ℓ kh j : ℕ) (C tl : List Bool)
    (hC : C = binary 8 j ++ (alphasOf ℓ j).flatten ++ ((digsOf ℓ kh j).flatten ++ tl))
    (r8s rls rks r1s r7s BTo ALo DGo DNo : List Bool) (cL cL2 : ℕ)
    (hℓ : 8 * (2 + 2) + 1 ≤ cL) (hl : ℓ * (2 + 2) + 1 ≤ cL) (hk : kh * (2 + 2) + 1 ≤ cL)
    (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ cL2) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ cL2) :
    Step splitFieldsM (splitFieldsCost ℓ kh) (fun _ => 0)
      (bank12 C BTo ALo DGo DNo (List.replicate 8 true ++ false :: r8s)
        (List.replicate ℓ true ++ false :: rls) (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
        (List.replicate 7 true ++ false :: r7s) cL cL2)
      ![8 + 8 * ℓ + 8 * kh, (frame (binary 8 j)).length, ((alphasOf ℓ j).flatMap frame).length + 1,
        ((digsOf ℓ kh j).flatMap frame).length + 1, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C (overlay (frame (binary 8 j)) BTo)
        (overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo) (overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo) DNo
        (List.replicate 8 true ++ false :: r8s) (List.replicate ℓ true ++ false :: rls)
        (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
        (List.replicate 7 true ++ false :: r7s) cL cL2) := by
  have sA := split_A j C BTo ALo DGo DNo (List.replicate ℓ true ++ false :: rls)
    (List.replicate kh true ++ false :: rks) (List.replicate 7 true ++ false :: r7s) r8s r1s
    ((alphasOf ℓ j).flatten ++ ((digsOf ℓ kh j).flatten ++ tl)) cL cL2
    (by simp only [hC, List.append_assoc]) hℓ
  have sB := split_B ℓ j (frame (binary 8 j)).length C (overlay (frame (binary 8 j)) BTo)
    ALo DGo DNo (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
    (List.replicate 7 true ++ false :: r7s) r8s rls ((digsOf ℓ kh j).flatten ++ tl) cL cL2
    (by simp only [hC, List.append_assoc]) hl hl2
  have sC := split_C ℓ kh j (frame (binary 8 j)).length (((alphasOf ℓ j).flatMap frame).length + 1)
    C (overlay (frame (binary 8 j)) BTo)
    (overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo) DGo DNo (List.replicate ℓ true ++ false :: rls)
    (List.replicate 1 true ++ false :: r1s) (List.replicate 7 true ++ false :: r7s) r8s rks tl cL cL2
    (by simp only [hC, List.append_assoc]) hk hk2
  exact (sA.seq sB).seq sC

/-- The fields and the rotated stream, the digit stream's head rewound in between (JStages' `splitM` before its
final reset). -/
noncomputable def innerM :=
  Composition.machine (MaskedReset.machine splitFieldsM selDG) (RecoveryFocus.machine s13 splitRotM)

theorem inner_run (ℓ kh j : ℕ) (C tl BTo ALo DGo DNo : List Bool) (cL cL2 cM1 : ℕ)
    (hC : C = binary 8 j ++ (alphasOf ℓ j).flatten ++ ((digsOf ℓ kh j).flatten ++ tl))
    (hℓ : 8 * (2 + 2) + 1 ≤ cL) (hl : ℓ * (2 + 2) + 1 ≤ cL) (hk : kh * (2 + 2) + 1 ≤ cL)
    (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ cL2) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ cL2)
    (hr2 : 2 * kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ cL2)
    (hcM1 : splitFieldsCost ℓ kh ≤ cM1) :
    Step innerM ((2 * splitFieldsCost ℓ kh + 2) + 1 + splitRotCost kh) (fun _ => 0)
      ![C, BTo, ALo, DGo, DNo, List.replicate 8 true ++ [false],
        List.replicate ℓ true ++ [false], List.replicate kh true ++ [false], List.replicate 1 true ++ [false],
        List.replicate 7 true ++ [false], List.replicate cL false, List.replicate cL2 false, List.replicate cM1 false]
      ![8 + 8 * ℓ + 8 * kh, (frame (binary 8 j)).length, ((alphasOf ℓ j).flatMap frame).length + 1,
        (frame ((digsOf ℓ kh j).headD [])).length,
        (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame).length + 1, 0, 0, 0, 1, 0, 0, 0, 0]
      ![C, overlay (frame (binary 8 j)) BTo,
        overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo, overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo,
        overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) DNo,
        List.replicate 8 true ++ [false], List.replicate ℓ true ++ [false], List.replicate kh true ++ [false],
        List.replicate 1 true ++ [false], List.replicate 7 true ++ [false], List.replicate cL false,
        List.replicate cL2 false, List.replicate cM1 false] := by
  set R8 := List.replicate 8 true ++ [false]
  set RL := List.replicate ℓ true ++ [false]
  set RK := List.replicate kh true ++ [false]
  set R1 := List.replicate 1 true ++ [false]
  set R7 := List.replicate 7 true ++ [false]
  set BT1 := overlay (frame (binary 8 j)) BTo
  set AL1 := overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo
  set DG1 := overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo
  set h1v := (frame (binary 8 j)).length
  set h2v := ((alphasOf ℓ j).flatMap frame).length + 1
  have h1 := split_fieldsG ℓ kh j C tl hC [] [] [] [] [] BTo ALo DGo DNo cL cL2 hℓ hl hk hl2 hk2
  have hm1 := h1.mask (cap := cM1) selDG (by intro i _; fin_cases i <;> rfl) hcM1
  have hm1' : Step (MaskedReset.machine splitFieldsM selDG) (2 * splitFieldsCost ℓ kh + 2) (fun _ => 0)
      ![C, BTo, ALo, DGo, DNo, R8, RL, RK, R1, R7, List.replicate cL false, List.replicate cL2 false,
        List.replicate cM1 false]
      ![8 + 8 * ℓ + 8 * kh, h1v, h2v, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
      ![C, BT1, AL1, DG1, DNo, R8, RL, RK, R1, R7, List.replicate cL false, List.replicate cL2 false,
        List.replicate cM1 false] := by
    refine (hm1.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have h2 := split_rot ℓ kh j [] [] [] [] [] BT1 AL1 DGo DNo C cL cL2 (8 + 8 * ℓ + 8 * kh) h1v h2v hr2
  have s2 := dockRun h2 s13 (by decide) ![8 + 8 * ℓ + 8 * kh, h1v, h2v, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    ![C, BT1, AL1, DG1, DNo, R8, RL, RK, R1, R7, List.replicate cL false, List.replicate cL2 false,
      List.replicate cM1 false] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_s13, install_s13] at s2
  refine (hm1'.seq s2).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

/-! ## The state word (tapes 0 the counter, 1–4 the fields, 5–9 the rulers of 8, ℓ, kh, 1, 7 cells, 10–12 logs,
13 the state word, 14 a unit ruler, 15 the state word's ruler) -/

def sTW : Fin 5 → Fin 16 := ![14, 15, 0, 13, 10]

theorem install_sTW (A : Fin 16 → List Bool) (v : Fin 5 → List Bool) :
    RecoveryRootRound.install sTW A v = ![v 2, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 4, A 11, A 12, v 3, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_sTW (H : Fin 16 → ℕ) (v : Fin 5 → ℕ) :
    dockH sTW H v = ![v 2, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 4, H 11, H 12, v 3, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_other _ _ _ _ (by decide)

/-- The heads the split resets: the counter, the fields, the unit rulers, the state word. -/
def selT : Fin 16 → Bool :=
  ![true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false]

/-- **The split with the state word**: the fields and the rotated stream, then the state word from the counter's
head at `w₀`; every head rewound. -/
noncomputable def splitTM :=
  MaskedReset.machine (Composition.machine (TapeEmbedding.machine 3 innerM) (RecoveryFocus.machine sTW fieldsLoopM)) selT

def splitTCost (ℓ kh TWd : ℕ) : ℕ :=
  2 * (((2 * splitFieldsCost ℓ kh + 2) + 1 + splitRotCost kh) + 1 + (1 * (fieldCost TWd + 2) + 1)) + 2

theorem splitT_run (ℓ kh TWd j : ℕ) (C post BTo ALo DGo DNo TWo : List Bool) (cL cL2 cM1 cM2 : ℕ)
    (hC : C = binary 8 j ++ (alphasOf ℓ j).flatten ++
      ((digsOf ℓ kh j).flatten ++ (binary TWd (j / 2 ^ (8 + 8 * ℓ + 8 * kh)) ++ post)))
    (hℓ : 8 * (2 + 2) + 1 ≤ cL) (hl : ℓ * (2 + 2) + 1 ≤ cL) (hk : kh * (2 + 2) + 1 ≤ cL)
    (hT : TWd * (2 + 2) + 1 ≤ cL)
    (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ cL2) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ cL2)
    (hr2 : 2 * kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ cL2)
    (hcM1 : splitFieldsCost ℓ kh ≤ cM1)
    (hcM2 : ((2 * splitFieldsCost ℓ kh + 2) + 1 + splitRotCost kh) + 1 + (1 * (fieldCost TWd + 2) + 1) ≤ cM2) :
    Step splitTM (splitTCost ℓ kh TWd) (fun _ => 0)
      ![C, BTo, ALo, DGo, DNo, List.replicate 8 true ++ [false],
        List.replicate ℓ true ++ [false], List.replicate kh true ++ [false], List.replicate 1 true ++ [false],
        List.replicate 7 true ++ [false], List.replicate cL false, List.replicate cL2 false, List.replicate cM1 false,
        TWo, List.replicate 1 true ++ [false], List.replicate TWd true ++ [false], List.replicate cM2 false]
      (fun _ => 0)
      ![C, overlay (frame (binary 8 j)) BTo,
        overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo, overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo,
        overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) DNo,
        List.replicate 8 true ++ [false], List.replicate ℓ true ++ [false], List.replicate kh true ++ [false],
        List.replicate 1 true ++ [false], List.replicate 7 true ++ [false], List.replicate cL false,
        List.replicate cL2 false, List.replicate cM1 false,
        overlay (frame (binary TWd (j / 2 ^ (8 + 8 * ℓ + 8 * kh)))) TWo, List.replicate 1 true ++ [false],
        List.replicate TWd true ++ [false], List.replicate cM2 false] := by
  set tt := j / 2 ^ (8 + 8 * ℓ + 8 * kh)
  set R1b := List.replicate 1 true ++ [false]
  set RTW := List.replicate TWd true ++ [false]
  have h1 := inner_run ℓ kh j C (binary TWd tt ++ post) BTo ALo DGo DNo cL cL2 cM1 hC hℓ hl hk hl2 hk2 hr2 hcM1
  have e1 := h1.embed (fun _ : Fin 3 => 0) ![TWo, R1b, RTW]
  have hf := fieldsLoop_run TWd [] [] (binary 8 j ++ (alphasOf ℓ j).flatten ++ (digsOf ℓ kh j).flatten) post [] TWo
    [binary TWd tt] cL (by intro f hf; rw [List.mem_singleton] at hf; rw [hf]; exact binary_length _ _) hT
  have eC : binary 8 j ++ (alphasOf ℓ j).flatten ++ (digsOf ℓ kh j).flatten ++ [binary TWd tt].flatten ++ post = C := by
    rw [hC]; simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  have eO : overlay ([] : List Bool) TWo = TWo := by simp [overlay]
  have e2 : ([] : List Bool) ++ [binary TWd tt].flatMap frame = frame (binary TWd tt) := by simp
  rw [eC, eO, e2, prefix_length, List.length_singleton] at hf
  have s2 := dockRun hf sTW (by decide)
    (Fin.addCases (m := 13) (n := 3) (motive := fun _ => ℕ) ![8 + 8 * ℓ + 8 * kh, (frame (binary 8 j)).length, ((alphasOf ℓ j).flatMap frame).length + 1,
        (frame ((digsOf ℓ kh j).headD [])).length,
        (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame).length + 1, 0, 0, 0, 1, 0, 0, 0, 0]
      (fun _ : Fin 3 => 0))
    (Fin.addCases (m := 13) (n := 3) (motive := fun _ => List Bool) ![C, overlay (frame (binary 8 j)) BTo,
        overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo, overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo,
        overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) DNo,
        List.replicate 8 true ++ [false], List.replicate ℓ true ++ [false], List.replicate kh true ++ [false],
        List.replicate 1 true ++ [false], List.replicate 7 true ++ [false], List.replicate cL false,
        List.replicate cL2 false, List.replicate cM1 false] ![TWo, R1b, RTW])
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_sTW, install_sTW] at s2
  have hall := e1.seq s2
  have hm := hall.mask (cap := cM2) selT (by intro i _; fin_cases i <;> rfl) hcM2
  unfold splitTCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

/-! ## The split and the increment docked on the layout -/

def slSplitT : Fin 17 → Fin 64 := ![62, 0, 1, 2, 3, 23, 24, 25, 26, 27, 50, 51, 52, 21, 60, 61, 53]

theorem slSplitT_inj : Function.Injective slSplitT := by decide

theorem install_slSplitT (A : Fin 64 → List Bool) (v : Fin 17 → List Bool) :
    RecoveryRootRound.install slSplitT A v =
      ![v 1, v 2, v 3, v 4, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, v 13, A 22, v 5, v 6, v 7, v 8, v 9, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 10, v 11, v 12, v 16, A 54, A 55, A 56, A 57, A 58, A 59, v 14, v 15, v 0, A 63] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 1
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 2
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 3
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 4
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 13
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 5
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 6
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 7
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 8
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 9
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 10
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 11
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 12
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 16
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 14
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 15
  · exact RecoveryRootRound.install_slot slSplitT slSplitT_inj A v 0
  · exact RecoveryRootRound.install_other slSplitT A v _ (by decide)

def slInc : Fin 2 → Fin 64 := ![62, 63]

theorem slInc_inj : Function.Injective slInc := by decide

theorem install_slInc (A : Fin 64 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slInc A v =
      ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, A 50, A 51, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59, A 60, A 61, v 0, v 1] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_other slInc A v _ (by decide)
  · exact RecoveryRootRound.install_slot slInc slInc_inj A v 0
  · exact RecoveryRootRound.install_slot slInc slInc_inj A v 1

theorem stage_splitT (X : JCtx) (T : JT) (j c0 c1 c2 c3 : ℕ)
    (hR8 : T.R8 = List.replicate 8 true ++ [false]) (hRL : T.RL = List.replicate X.P.ell true ++ [false])
    (hRK : T.RK = List.replicate X.P.kh true ++ [false]) (hR1 : T.R1 = List.replicate 1 true ++ [false])
    (hR7 : T.R7 = List.replicate 7 true ++ [false]) (hL0 : T.L0 = List.replicate c0 false)
    (hL1 : T.L1 = List.replicate c1 false) (hL2 : T.L2 = List.replicate c2 false) (hL3 : T.L3 = List.replicate c3 false)
    (hℓ : 8 * (2 + 2) + 1 ≤ c0) (hl : X.P.ell * (2 + 2) + 1 ≤ c0) (hk : X.P.kh * (2 + 2) + 1 ≤ c0)
    (hT : X.TWd * (2 + 2) + 1 ≤ c0)
    (hl2 : 8 * (fieldCost X.P.ell + 2) + 1 + 1 + 1 ≤ c1) (hk2 : 8 * (fieldCost X.P.kh + 2) + 1 + 1 + 1 ≤ c1)
    (hr2 : 2 * X.P.kh + 1 + 1 + 1 + 1 +
      (((List.range (7 - 0)).map (fun _ => 2 * X.P.kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ c1)
    (hcM1 : splitFieldsCost X.P.ell X.P.kh ≤ c2)
    (hcM2 : ((2 * splitFieldsCost X.P.ell X.P.kh + 2) + 1 + splitRotCost X.P.kh) + 1 + (1 * (fieldCost X.TWd + 2) + 1)
      ≤ c3) :
    Step (RecoveryFocus.machine slSplitT splitTM) (splitTCost X.P.ell X.P.kh X.TWd) (fun _ => 0) (lay X T j) (fun _ => 0)
      (lay X { T with BT := overlay (frame (binary 8 j)) T.BT,
                      AL := overlay ((alphasOf X.P.ell j).flatMap frame ++ [false]) T.AL,
                      DG := overlay ((digsOf X.P.ell X.P.kh j).flatMap frame ++ [false]) T.DG,
                      DN := overlay (((digsOf X.P.ell X.P.kh j).tail ++ [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++
                        [false]) T.DN,
                      TW := overlay (frame (binary X.TWd (tOf X j))) T.TW } j) := by
  have hC' : binary (wT X + 1) j = binary 8 j ++ (alphasOf X.P.ell j).flatten ++ ((digsOf X.P.ell X.P.kh j).flatten ++
      (binary X.TWd (j / 2 ^ (8 + 8 * X.P.ell + 8 * X.P.kh)) ++
        binary 1 (j / 2 ^ (8 + 8 * X.P.ell + 8 * X.P.kh + X.TWd)))) := by
    exact counter_splitT _ _ _ _
  have h := splitT_run X.P.ell X.P.kh X.TWd j (binary (wT X + 1) j) _ T.BT T.AL T.DG T.DN T.TW c0 c1 c2 c3 hC' hℓ hl hk hT hl2 hk2 hr2
    hcM1 hcM2
  rw [← hR8, ← hRL, ← hRK, ← hR7, ← hL0, ← hL1, ← hL2, ← hL3] at h
  have hd := dockKeep h slSplitT slSplitT_inj (fun _ => 0) (lay X T j) (fun _ => rfl)
    (by intro i; fin_cases i <;> first | rfl | exact hR1)
  rw [install_slSplitT] at hd
  refine hd.congr rfl ?_
  funext i; fin_cases i <;> first | rfl | exact hR1.symm

theorem stage_inc (X : JCtx) (T : JT) (j : ℕ) (hj : j < 2 ^ wT X) :
    Step (RecoveryFocus.machine slInc (Rewind.machine BinaryIncrement.machine)) (2 * (wT X + 1) + 2) (fun _ => 0)
      (lay X T j) (fun _ => 0) (lay X T (j + 1)) := by
  have h := EnumBody.increment_step (wT X) j hj
  have hd := dockKeep h slInc slInc_inj (fun _ => 0) (lay X T j) (fun _ => rfl) (by intro i; fin_cases i <;> rfl)
  rw [install_slInc] at hd
  refine hd.congr rfl ?_
  funext i; fin_cases i <;> rfl

end SplitT

end NearCubicWires.WireExponent3_5.SeedFix
