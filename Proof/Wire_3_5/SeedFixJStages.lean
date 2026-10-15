import Proof.Wire_3_5.SeedFixJBank

/-! # C4.Sb, machine part 17: the blocks docked on the enumeration cell's bank

Each block runs from and to "every head at cell 0" and is docked on the bank by its slot map (`dockJ`). The stage lemmas
state each block's effect as an update of the bank's record. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open NearCubicWires.WireExponent3_5.JoinElimination NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)
open Split Cells Valid Cons FetchAll FetchCells Emit JBank

namespace JStages

theorem dockJ {k s n : ℕ} {M : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin k → Fin 60) (hi : Function.Injective slots)
    (T T' : JT) (hA : ∀ j, T.vec (slots j) = tin j) (hT : RecoveryRootRound.install slots T.vec tout = T'.vec) :
    Step (RecoveryFocus.machine slots M) n (fun _ => 0) T.vec (fun _ => 0) T'.vec := by
  have h1 := dockKeep h slots hi (fun _ => 0) T.vec (fun _ => rfl) hA
  rwa [hT] at h1

theorem install_eq {k u : ℕ} (slots : Fin k → Fin u) (hi : Function.Injective slots) (A B : Fin u → List Bool)
    (v : Fin k → List Bool) (h1 : ∀ j, B (slots j) = v j) (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) :
    RecoveryRootRound.install slots A v = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [RecoveryRootRound.install_slot slots hi]
    exact (h1 j).symm
  · have h' : ∀ j, slots j ≠ i := fun j hj => h ⟨j, hj⟩
    rw [RecoveryRootRound.install_other slots A v i h']
    exact (h2 i h').symm

/-! ## The split, heads rewound -/

def s13 : Fin 12 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem install_s13 (A : Fin 13 → List Bool) (v : Fin 12 → List Bool) :
    RecoveryRootRound.install s13 A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, A 12] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 10
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 11
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s13 (H : Fin 13 → ℕ) (v : Fin 12 → ℕ) :
    dockH s13 H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, H 12] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_slot _ (by decide) _ _ 8
    | exact dockH_slot _ (by decide) _ _ 9
    | exact dockH_slot _ (by decide) _ _ 10
    | exact dockH_slot _ (by decide) _ _ 11
    | exact dockH_other _ _ _ _ (by decide)

def slSplit2 : Fin 14 → Fin 60 := ![58, 0, 1, 2, 3, 23, 24, 25, 26, 27, 50, 51, 52, 53]

theorem slSplit2_inj : Function.Injective slSplit2 := by decide

theorem install_slSplit2 (A : Fin 60 → List Bool) (v : Fin 14 → List Bool) :
    RecoveryRootRound.install slSplit2 A v =
      ![v 1, v 2, v 3, v 4, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, v 5, v 6, v 7, v 8, v 9, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 10, v 11, v 12, v 13, A 54, A 55, A 56, A 57, v 0, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 1
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 2
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 3
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 4
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 5
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 6
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 7
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 8
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 9
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 10
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 11
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 12
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 13
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)
  · exact RecoveryRootRound.install_slot slSplit2 slSplit2_inj A v 0
  · exact RecoveryRootRound.install_other slSplit2 A v _ (by decide)

def selDG : Fin 12 → Bool := ![false, false, false, true, false, false, false, false, false, false, false, false]
def selOut : Fin 13 → Bool := ![true, true, true, true, true, false, false, false, true, false, false, false, false]

/-- The fields with the digit stream's head rewound, then the rotated stream; every head rewound. -/
noncomputable def splitM := MaskedReset.machine
  (Composition.machine (MaskedReset.machine splitFieldsM selDG) (RecoveryFocus.machine s13 splitRotM)) selOut

def splitCost (ℓ kh : ℕ) : ℕ := 2 * ((2 * splitFieldsCost ℓ kh + 2) + 1 + splitRotCost kh) + 2

theorem split_run (ℓ kh j : ℕ) (BTo ALo DGo DNo : List Bool) (cL cL2 cM1 cM2 : ℕ)
    (hℓ : 8 * (2 + 2) + 1 ≤ cL) (hl : ℓ * (2 + 2) + 1 ≤ cL) (hk : kh * (2 + 2) + 1 ≤ cL)
    (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ cL2) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ cL2)
    (hr2 : 2 * kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ cL2)
    (hcM1 : splitFieldsCost ℓ kh ≤ cM1) (hcM2 : (2 * splitFieldsCost ℓ kh + 2) + 1 + splitRotCost kh ≤ cM2) :
    Step splitM (splitCost ℓ kh) (fun _ => 0)
      ![binary (8 + 8 * ℓ + 8 * kh + 1) j, BTo, ALo, DGo, DNo, List.replicate 8 true ++ [false],
        List.replicate ℓ true ++ [false], List.replicate kh true ++ [false], List.replicate 1 true ++ [false],
        List.replicate 7 true ++ [false], List.replicate cL false, List.replicate cL2 false, List.replicate cM1 false,
        List.replicate cM2 false]
      (fun _ => 0)
      ![binary (8 + 8 * ℓ + 8 * kh + 1) j, overlay (frame (binary 8 j)) BTo,
        overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo, overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo,
        overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) DNo,
        List.replicate 8 true ++ [false], List.replicate ℓ true ++ [false], List.replicate kh true ++ [false],
        List.replicate 1 true ++ [false], List.replicate 7 true ++ [false], List.replicate cL false,
        List.replicate cL2 false, List.replicate cM1 false, List.replicate cM2 false] := by
  set C := binary (8 + 8 * ℓ + 8 * kh + 1) j
  set R8 := List.replicate 8 true ++ [false]
  set RL := List.replicate ℓ true ++ [false]
  set RK := List.replicate kh true ++ [false]
  set R1 := List.replicate 1 true ++ [false]
  set R7 := List.replicate 7 true ++ [false]
  set BT1 := overlay (frame (binary 8 j)) BTo
  set AL1 := overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo
  set DG1 := overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo
  set DN1 := overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) DNo
  set h1v := (frame (binary 8 j)).length
  set h2v := ((alphasOf ℓ j).flatMap frame).length + 1
  have h1 := split_fields ℓ kh j [] [] [] [] [] BTo ALo DGo DNo cL cL2 hℓ hl hk hl2 hk2
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
  have hall := (hm1'.congr (hout' := ![8 + 8 * ℓ + 8 * kh, h1v, h2v, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) (tout' :=
      ![C, BT1, AL1, DG1, DNo, R8, RL, RK, R1, R7, List.replicate cL false, List.replicate cL2 false,
        List.replicate cM1 false]) rfl rfl).seq s2
  have hm := hall.mask (cap := cM2) selOut (by intro i _; fin_cases i <;> rfl) hcM2
  unfold splitCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

/-! ## The stages on the bank -/

theorem stage_split (T : JT) (ℓ kh j c0 c1 c2 c3 : ℕ) (hC : T.C = binary (8 + 8 * ℓ + 8 * kh + 1) j)
    (hR8 : T.R8 = List.replicate 8 true ++ [false]) (hRL : T.RL = List.replicate ℓ true ++ [false])
    (hRK : T.RK = List.replicate kh true ++ [false]) (hR1 : T.R1 = List.replicate 1 true ++ [false])
    (hR7 : T.R7 = List.replicate 7 true ++ [false]) (hL0 : T.L0 = List.replicate c0 false)
    (hL1 : T.L1 = List.replicate c1 false) (hL2 : T.L2 = List.replicate c2 false) (hL3 : T.L3 = List.replicate c3 false)
    (hℓ : 8 * (2 + 2) + 1 ≤ c0) (hl : ℓ * (2 + 2) + 1 ≤ c0) (hk : kh * (2 + 2) + 1 ≤ c0)
    (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ c1) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ c1)
    (hr2 : 2 * kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ c1)
    (hcM1 : splitFieldsCost ℓ kh ≤ c2) (hcM2 : (2 * splitFieldsCost ℓ kh + 2) + 1 + splitRotCost kh ≤ c3) :
    Step (RecoveryFocus.machine slSplit2 splitM) (splitCost ℓ kh) (fun _ => 0) T.vec (fun _ => 0)
      { T with BT := overlay (frame (binary 8 j)) T.BT, AL := overlay ((alphasOf ℓ j).flatMap frame ++ [false]) T.AL,
               DG := overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) T.DG,
               DN := overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) T.DN }.vec := by
  have h := split_run ℓ kh j T.BT T.AL T.DG T.DN c0 c1 c2 c3 hℓ hl hk hl2 hk2 hr2 hcM1 hcM2
  rw [← hC, ← hR8, ← hRL, ← hRK, ← hR1, ← hR7, ← hL0, ← hL1, ← hL2, ← hL3] at h
  refine dockJ h slSplit2 slSplit2_inj T _ (by intro i; fin_cases i <;> rfl) ?_
  rw [install_slSplit2]; funext i; fin_cases i <;> rfl

theorem stage_cells (T : JT) (r c0 : ℕ) (g0 g1 g2 g3 g4 g5 g6 g7 tG tN : List Bool)
    (hDG : T.DG = [g0, g1, g2, g3, g4, g5, g6, g7].flatMap frame ++ tG)
    (hDN : T.DN = [g1, g2, g3, g4, g5, g6, g7, g0].flatMap frame ++ tN) (hL0 : T.L0 = List.replicate c0 false)
    (h0 : g0.length = r) (h1 : g1.length = r) (h2 : g2.length = r) (h3 : g3.length = r) (h4 : g4.length = r)
    (h5 : g5.length = r) (h6 : g6.length = r) (h7 : g7.length = r) (hcap : cellsInnerCost r ≤ c0) :
    Step (RecoveryFocus.machine slCells cellsM) (2 * cellsInnerCost r + 2) (fun _ => 0) T.vec (fun _ => 0)
      { T with CL := overlay (cellsOut g0 g1 g2 g3 g4 g5 g6 g7 ++ [false]) T.CL }.vec := by
  have h := cells_run r g0 g1 g2 g3 g4 g5 g6 g7 tG tN T.CL c0 h0 h1 h2 h3 h4 h5 h6 h7 hcap
  rw [← hDG, ← hDN, ← hL0] at h
  refine dockJ h slCells slCells_inj T _ (by intro i; fin_cases i <;> rfl) ?_
  rw [install_slCells]; funext i; fin_cases i <;> rfl

theorem stage_valid (T : JT) (r c0 c1 : ℕ) (x0 q tail : List Bool) (cc0 v0 : Bool) (as : List (List Bool))
    (hR8 : T.R8 = List.replicate as.length true ++ [false]) (hAL : T.AL = as.flatMap frame ++ tail)
    (hLAB : T.LAB = frame x0) (hQM : T.QM = frame q) (hCC : T.CC = [cc0]) (hV : T.V = [v0]) (hONE : T.ONE = [true])
    (hL0 : T.L0 = List.replicate c0 false) (hL1 : T.L1 = List.replicate c1 false)
    (has : ∀ a ∈ as, a.length = r) (hx : x0.length = r) (hq : q.length = r)
    (hcL : 2 * r + 1 + 1 + 1 ≤ c0) (hcL2 : validInnerCost as.length r ≤ c1) :
    Step (RecoveryFocus.machine slValid validM) (2 * validInnerCost as.length r + 2) (fun _ => 0) T.vec (fun _ => 0)
      { T with LAB := frame (labAt x0 as as.length), CC := [ccAt cc0 q as as.length], V := [as.all (cmpQ q)] }.vec := by
  have h := valid_run r [] T.AL x0 q tail cc0 v0 as c0 c1 hAL has hx hq hcL hcL2
  rw [← hLAB, ← hQM, ← hCC, ← hV, ← hONE, ← hL0, ← hL1, show List.replicate as.length true ++ [false] = T.R8 from hR8.symm]
    at h
  refine dockJ h slValid slValid_inj T _ (by intro i; fin_cases i <;> rfl) ?_
  rw [install_slValid]; funext i; fin_cases i <;> rfl

theorem stage_cons (T : JT) (ra rc c0 : ℕ) (bs tB tA tC : List Bool) (as cs : List (List Bool))
    (hBT : T.BT = frame bs ++ tB) (hAL : T.AL = as.flatMap frame ++ tA) (hCL : T.CL = cs.flatMap frame ++ tC)
    (hL0 : T.L0 = List.replicate c0 false)
    (has : ∀ a ∈ as, a.length = ra) (hcs : ∀ c ∈ cs, c.length = rc) (hla : as.length = bs.length)
    (hlc : cs.length = bs.length) (hcap : consInnerCost bs.length ra rc ≤ c0) :
    Step (RecoveryFocus.machine slCons consM) (2 * consInnerCost bs.length ra rc + 2) (fun _ => 0) T.vec (fun _ => 0)
      { T with CT := overlay (consOut bs as cs bs.length ++ [false]) T.CT }.vec := by
  have h := cons_run ra rc T.BT T.AL T.CL T.CT tB tA tC bs as cs c0 hBT hAL hCL has hcs hla hlc hcap
  rw [← hL0] at h
  refine dockJ h slCons slCons_inj T _ (by intro i; fin_cases i <;> rfl) ?_
  rw [install_slCons]; funext i; fin_cases i <;> rfl

open ElimX in
theorem stage_elim (T : JT) (p ℓ k plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC : ℕ) (R0 : Regs)
    (cons : List (ℕ × ℕ)) (stale : List Bool) (g0 : Bool)
    (hR8 : T.R8 = List.replicate 8 true ++ [false]) (hRL : T.RL = List.replicate ℓ true ++ [false])
    (hRA : T.RA = frame (binary ℓ R0.a)) (hRC : T.RC = frame (binary ℓ R0.c)) (hRT : T.RT = R0.T ++ List.replicate m false)
    (hPW : T.PW = frame (binary ℓ p)) (hFL : T.FL = R0.fl) (hRX : T.RX = frame (binary ℓ R0.x))
    (hRZ : T.RZ = frame (binary ℓ R0.z)) (hZ9 : T.Z9 = [false]) (hL0 : T.L0 = List.replicate cap false)
    (hL1 : T.L1 = List.replicate cap2 false) (hL2 : T.L2 = List.replicate cap3 false) (hL3 : T.L3 = List.replicate RV false)
    (hPFX : T.PFX = frame (binary plen pfx)) (hMC : T.MC = frame (binary ℓ R0.mc)) (hRR : T.RR = R0.r)
    (hRB : T.RB = [R0.b]) (hZ18 : T.Z18 = [false]) (hONEW : T.ONEW = frame (binary ℓ 1))
    (hL4 : T.L4 = List.replicate cap4 false) (hCT : T.CT = consTape ℓ k cons stale) (hL5 : T.L5 = List.replicate cL false)
    (hL6 : T.L6 = List.replicate cE false) (hK : T.K = pad cK [])
    (hCC2 : T.CC2 = pad cC (List.replicate (8 * ℓ - plen) true)) (hG : T.G = [g0])
    (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ)
    (h0 : R0.Ok ℓ 8) (hcons : ∀ con ∈ cons, con.1 < 2 ^ ℓ)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ 8 ≤ cap3) (hcap3' : passesCost ℓ plen (8 * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (8 * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ 8 * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL)
    (hcapG : 2 * (8 * ℓ - plen) + 13 ≤ cap)
    (hcapG' : cons.length * k * (Gauss.rowCost (8 * ℓ - plen) + 2) + 3 ≤ cap2)
    (hcapG'' : cons.length * k * (2 * (8 * ℓ - plen) + 1) + 1 ≤ cap2) (hcK : 8 * ℓ - plen ≤ cK)
    (hcE1 : loopCost ℓ 8 k plen cons.length + 1 + 1 ≤ cE)
    (hcE2 : Gauss.gaussCost (cons.length * k) (8 * ℓ - plen) ≤ cE) (hcE3 : Deficit.cost (8 * ℓ - plen) ≤ cE) :
    Step (RecoveryFocus.machine slElim elimM) (elimCost ℓ 8 k plen cons.length) (fun _ => 0) T.vec (fun _ => 0)
      { T with RA := frame (binary ℓ (regsAt p ℓ 8 k plen R0 cons cons.length).a),
               RC := frame (binary ℓ (regsAt p ℓ 8 k plen R0 cons cons.length).c),
               RT := (regsAt p ℓ 8 k plen R0 cons cons.length).T ++ List.replicate m false,
               FL := (regsAt p ℓ 8 k plen R0 cons cons.length).fl,
               RX := frame (binary ℓ (regsAt p ℓ 8 k plen R0 cons cons.length).x),
               RZ := frame (binary ℓ (regsAt p ℓ 8 k plen R0 cons cons.length).z),
               MC := frame (binary ℓ (regsAt p ℓ 8 k plen R0 cons cons.length).mc),
               RR := (regsAt p ℓ 8 k plen R0 cons cons.length).r,
               RB := [(regsAt p ℓ 8 k plen R0 cons cons.length).b],
               O := elimO p ℓ 8 k plen pfx cons T.O T.W T.P, W := elimW p ℓ 8 k plen pfx cons T.O T.W T.P,
               P := elimP p ℓ 8 k plen pfx cons T.O T.W T.P,
               G := [(gauss (8 * ℓ - plen) (system p ℓ 8 k plen pfx cons)).1],
               XE := overlay (List.replicate (8 * ℓ - plen - (gauss (8 * ℓ - plen) (system p ℓ 8 k plen pfx cons)).2) true
                 ++ [false]) T.XE }.vec := by
  have h := elimX_run p ℓ 8 k plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC R0 cons stale T.O T.W T.P T.XE g0 hp hℓ hkl
    h0 hcons hcap hcap2 hcap2' hcap2'' hcap3 hcap3' hcap4 hplen hm hRV hcL hcapG hcapG' hcapG'' hcK hcE1 hcE2 hcE3
  generalize regsAt p ℓ 8 k plen R0 cons cons.length = R1 at h ⊢
  generalize elimO p ℓ 8 k plen pfx cons T.O T.W T.P = oO at h ⊢
  generalize elimW p ℓ 8 k plen pfx cons T.O T.W T.P = oW at h ⊢
  generalize elimP p ℓ 8 k plen pfx cons T.O T.W T.P = oP at h ⊢
  generalize gauss (8 * ℓ - plen) (system p ℓ 8 k plen pfx cons) = gg at h ⊢
  have hA : ∀ i, T.vec (slElim i) = (bank31 p ℓ 8 plen pfx m cap cap2 cap3 cap4 RV cL cE R0 T.O (consTape ℓ k cons stale)
      T.W T.P (pad cK []) (pad cC (List.replicate (8 * ℓ - plen) true)) [g0] T.XE) i := by
    intro i; fin_cases i
    · exact hR8
    · exact hRL
    · exact hRA
    · exact hRC
    · exact hRT
    · exact hPW
    · exact hFL
    · exact hRX
    · exact hRZ
    · exact hZ9
    · exact hL0
    · exact hL1
    · exact hL2
    · exact hL3
    · exact hPFX
    · exact hMC
    · exact hRR
    · exact hRB
    · exact hZ18
    · rfl
    · exact hONEW
    · exact hL4
    · exact hCT
    · exact hL5
    · exact hL6
    · rfl
    · rfl
    · exact hK
    · exact hCC2
    · exact hG
    · rfl
  have hT : RecoveryRootRound.install slElim T.vec (bank31 p ℓ 8 plen pfx m cap cap2 cap3 cap4 RV cL cE
      (R1) (oO) (consTape ℓ k cons stale)
      (oW) (oP) (pad cK [])
      (pad cC (List.replicate (8 * ℓ - plen) true)) [(gg).1]
      (overlay (List.replicate (8 * ℓ - plen - (gg).2) true ++ [false])
        T.XE)) =
      { T with RA := frame (binary ℓ (R1).a),
               RC := frame (binary ℓ (R1).c),
               RT := (R1).T ++ List.replicate m false,
               FL := (R1).fl,
               RX := frame (binary ℓ (R1).x),
               RZ := frame (binary ℓ (R1).z),
               MC := frame (binary ℓ (R1).mc),
               RR := (R1).r,
               RB := [(R1).b],
               O := oO, W := oW,
               P := oP,
               G := [(gg).1],
               XE := overlay (List.replicate (8 * ℓ - plen - (gg).2) true
                 ++ [false]) T.XE }.vec := by
    refine install_eq slElim slElim_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · exact hR8
      · exact hRL
      · rfl
      · rfl
      · rfl
      · exact hPW
      · rfl
      · rfl
      · rfl
      · exact hZ9
      · exact hL0
      · exact hL1
      · exact hL2
      · exact hL3
      · exact hPFX
      · rfl
      · rfl
      · rfl
      · exact hZ18
      · rfl
      · exact hONEW
      · exact hL4
      · exact hCT
      · exact hL5
      · exact hL6
      · rfl
      · rfl
      · exact hK
      · exact hCC2
      · rfl
      · rfl
    · intro i hi; fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨22, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨0, by decide⟩)
      · exact absurd rfl (hi ⟨1, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨2, by decide⟩)
      · exact absurd rfl (hi ⟨3, by decide⟩)
      · exact absurd rfl (hi ⟨4, by decide⟩)
      · exact absurd rfl (hi ⟨5, by decide⟩)
      · exact absurd rfl (hi ⟨6, by decide⟩)
      · exact absurd rfl (hi ⟨7, by decide⟩)
      · exact absurd rfl (hi ⟨8, by decide⟩)
      · exact absurd rfl (hi ⟨9, by decide⟩)
      · exact absurd rfl (hi ⟨14, by decide⟩)
      · exact absurd rfl (hi ⟨15, by decide⟩)
      · exact absurd rfl (hi ⟨16, by decide⟩)
      · exact absurd rfl (hi ⟨17, by decide⟩)
      · exact absurd rfl (hi ⟨18, by decide⟩)
      · exact absurd rfl (hi ⟨19, by decide⟩)
      · exact absurd rfl (hi ⟨20, by decide⟩)
      · exact absurd rfl (hi ⟨25, by decide⟩)
      · exact absurd rfl (hi ⟨26, by decide⟩)
      · exact absurd rfl (hi ⟨27, by decide⟩)
      · exact absurd rfl (hi ⟨28, by decide⟩)
      · exact absurd rfl (hi ⟨29, by decide⟩)
      · exact absurd rfl (hi ⟨30, by decide⟩)
      · exact absurd rfl (hi ⟨10, by decide⟩)
      · exact absurd rfl (hi ⟨11, by decide⟩)
      · exact absurd rfl (hi ⟨12, by decide⟩)
      · exact absurd rfl (hi ⟨13, by decide⟩)
      · exact absurd rfl (hi ⟨21, by decide⟩)
      · exact absurd rfl (hi ⟨23, by decide⟩)
      · exact absurd rfl (hi ⟨24, by decide⟩)
      · rfl
      · rfl
      · rfl
  exact dockJ h slElim slElim_inj T _ hA hT

theorem stage_coef (T : JT) (bs : List Bool) (R2 : ℕ) (sg0 : Bool) (rus xs : List Bool) (e c0 c1 c2 : ℕ)
    (hBT : T.BT = frame bs) (hONES : T.ONES8 = frame (List.replicate bs.length true)) (hSG : T.SG = [sg0])
    (hRK2 : T.RK2 = List.replicate R2 true ++ false :: rus) (hXE : T.XE = List.replicate e true ++ false :: xs)
    (hL0 : T.L0 = List.replicate c0 false) (hL1 : T.L1 = List.replicate c1 false) (hL2 : T.L2 = List.replicate c2 false)
    (hcL : R2 * (2 + 2) + 1 ≤ c0) (hcF : 2 * bs.length + 1 ≤ c1) (hcM : coefCost bs R2 e ≤ 2 * c2 + 2) :
    Step (RecoveryFocus.machine slCoef coefM) (coefCost bs R2 e) (fun _ => 0) T.vec (fun _ => 0)
      { T with SG := [parity bs],
               ACC := overlay (exprWord [((if parity bs then -1 else 1) * 2 ^ (R2 * cnt bs bs.length + e), [])]) T.ACC }.vec := by
  have h := coef_run bs R2 sg0 rus xs T.ACC e c0 c1 c2 hcL hcF hcM
  refine dockJ h slCoef slCoef_inj T _ ?_ ?_
  · intro j; fin_cases j
    · exact hBT
    · exact hONES
    · exact hSG
    · exact hRK2
    · exact hXE
    · rfl
    · exact hL0
    · exact hL1
    · exact hL2
  · refine install_eq slCoef slCoef_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · exact hBT
      · exact hONES
      · rfl
      · exact hRK2
      · exact hXE
      · rfl
      · exact hL0
      · exact hL1
      · exact hL2
    · intro i hi; fin_cases i
      · exact absurd rfl (hi ⟨0, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨1, by decide⟩)
      · exact absurd rfl (hi ⟨2, by decide⟩)
      · exact absurd rfl (hi ⟨5, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨3, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨4, by decide⟩)
      · exact absurd rfl (hi ⟨6, by decide⟩)
      · exact absurd rfl (hi ⟨7, by decide⟩)
      · exact absurd rfl (hi ⟨8, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem stage_fetch (T : JT) (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool))
    (tailB tailC tw r8s : List Bool) (cI cT cA cC W e0 cE cF cG cH : ℕ) (f0 : Bool)
    (hBAT : T.BAT = blockWord ents ++ tailB) (hACC : T.ACC = s0.X) (hY : T.Y = s0.Y) (hROW : T.ROW = s0.ROW)
    (hAT : T.AT = s0.AT) (hL0 : T.L0 = List.replicate cI false) (hL1 : T.L1 = List.replicate cT false)
    (hL2 : T.L2 = List.replicate cA false) (hL3 : T.L3 = List.replicate cC false) (hCNT : T.CNT = frame (binary W 0))
    (hTGT : T.TGT = frame (binary W e0)) (hFLAG : T.FLAG = [f0]) (hONE : T.ONE = [true])
    (hL4 : T.L4 = List.replicate cE false) (hL5 : T.L5 = List.replicate cF false) (hTW : T.TW = frame tw)
    (hR8 : T.R8 = List.replicate es.length true ++ false :: r8s) (hL6 : T.L6 = List.replicate cG false)
    (hL7 : T.L7 = List.replicate cH false)
    (ok : FcOk s0 ents es cI cT cA cC W cE cF) (hCL : T.CL = cs.flatMap frame ++ tailC) (hlc : cs.length = es.length)
    (hcs : ∀ k (hk : k < es.length) (hk' : k < cs.length), binary W es[k] = cs[k] ++ tw)
    (hw : ∀ c ∈ cs, c.length + tw.length = W) (hcG : ∀ c ∈ cs, tgtInnerCost c.length tw.length ≤ cG)
    (hcH : ((List.range (es.length - 0)).map (fun i => fcCost s0 ents es cs tw W (0 + i) + 2)).sum + 1 ≤ cH) :
    Step (RecoveryFocus.machine slFetch fetchCellsM) (fetchCellsCost s0 ents es cs tw W) (fun _ => 0) T.vec (fun _ => 0)
      { T with ACC := (fcSt s0 ents es es.length).X, Y := (fcSt s0 ents es es.length).Y,
               ROW := (fcSt s0 ents es es.length).ROW, AT := (fcSt s0 ents es es.length).AT,
               TGT := frame (binary W (tgAt e0 es es.length)), FLAG := [flAt f0 ents.length es es.length] }.vec := by
  have h := fetchCells_run s0 ents es cs tailB T.CL tailC tw r8s cI cT cA cC W e0 cE cF cG cH f0 ok hCL hlc hcs hw hcG hcH
  generalize fcSt s0 ents es es.length = sf at h ⊢
  refine dockJ h slFetch slFetch_inj T _ ?_ ?_
  · intro j; fin_cases j
    · exact hBAT
    · exact hACC
    · exact hY
    · exact hROW
    · exact hAT
    · exact hL0
    · exact hL1
    · exact hL2
    · exact hL3
    · exact hCNT
    · exact hTGT
    · exact hFLAG
    · exact hONE
    · exact hL4
    · exact hL5
    · rfl
    · exact hTW
    · exact hR8
    · exact hL6
    · exact hL7
  · refine install_eq slFetch slFetch_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · exact hBAT
      · rfl
      · rfl
      · rfl
      · rfl
      · exact hL0
      · exact hL1
      · exact hL2
      · exact hL3
      · exact hCNT
      · rfl
      · rfl
      · exact hONE
      · exact hL4
      · exact hL5
      · rfl
      · exact hTW
      · exact hR8
      · exact hL6
      · exact hL7
    · intro i hi; fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨15, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨12, by decide⟩)
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨1, by decide⟩)
      · exact absurd rfl (hi ⟨2, by decide⟩)
      · exact absurd rfl (hi ⟨3, by decide⟩)
      · exact absurd rfl (hi ⟨4, by decide⟩)
      · exact absurd rfl (hi ⟨0, by decide⟩)
      · exact absurd rfl (hi ⟨9, by decide⟩)
      · exact absurd rfl (hi ⟨10, by decide⟩)
      · exact absurd rfl (hi ⟨11, by decide⟩)
      · exact absurd rfl (hi ⟨16, by decide⟩)
      · rfl
      · exact absurd rfl (hi ⟨17, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨5, by decide⟩)
      · exact absurd rfl (hi ⟨6, by decide⟩)
      · exact absurd rfl (hi ⟨7, by decide⟩)
      · exact absurd rfl (hi ⟨8, by decide⟩)
      · exact absurd rfl (hi ⟨13, by decide⟩)
      · exact absurd rfl (hi ⟨14, by decide⟩)
      · exact absurd rfl (hi ⟨18, by decide⟩)
      · exact absurd rfl (hi ⟨19, by decide⟩)
      · rfl
      · rfl

theorem stage_emit (T : JT) (V G : SExpr) (tX OB : List Bool) (c0 : ℕ) (hACC : T.ACC = exprWord G ++ tX)
    (hOUT : T.OUT = overlay (exprWord V) OB) (hL0 : T.L0 = List.replicate c0 false)
    (hcap : emitInnerCost (exprWord V).length (exprWord G).length ≤ c0) :
    Step (RecoveryFocus.machine slEmit emitM) (2 * emitInnerCost (exprWord V).length (exprWord G).length + 2)
      (fun _ => 0) T.vec (fun _ => 0) { T with OUT := overlay (exprWord (V ++ G)) OB }.vec := by
  have h := emit_run V G tX OB c0 hcap
  refine dockJ h slEmit slEmit_inj T _ ?_ ?_
  · intro j; fin_cases j
    · exact hACC
    · exact hOUT
    · exact hL0
  · refine install_eq slEmit slEmit_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · exact hACC
      · rfl
      · exact hL0
    · intro i hi; fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨0, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨1, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hi ⟨2, by decide⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

end JStages

end NearCubicWires.WireExponent3_5.SeedFix
