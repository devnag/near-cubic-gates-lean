import Proof.Wire_3_5.CompilerMachineEmitStack

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The stack stream of a list of pool children. -/
def stackStream (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    List Bool :=
  streamTape (stackRecs h side width L) []

theorem labRecs_width (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (fe : List Bool × ExactThresholdGate n) :
    ∀ r ∈ labRecs h side width fe, r.length = h :=
  denseRecs_width h side fe.1 width fe.2

theorem labRecs_length (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (fe : List Bool × ExactThresholdGate n) :
    (labRecs h side width fe).length = 2 * (width + width + 1) :=
  denseRecs_length h side fe.1 width fe.2

theorem stackRecs_length (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    (stackRecs h side width L).length = 2 * (width + width + 1) := by
  simp [stackRecs]

theorem stackRecs_width (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    ∀ r ∈ stackRecs h side width L, r.length = 1 + L.length * h := by
  intro r hr
  simp only [stackRecs, List.mem_map, List.mem_range] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  have hw : ∀ fe ∈ L, ((labRecs h side width fe).getD i []).length = h := by
    intro fe _
    rw [List.getD_eq_getElem _ _ (by rw [labRecs_length]; exact hi)]
    exact labRecs_width h side width fe _ (List.getElem_mem _)
  rw [List.length_cons, List.length_flatMap, List.map_congr_left hw, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem zip_stack (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n))
    (fe : List Bool × ExactThresholdGate n) :
    List.zipWith (· ++ ·) (stackRecs h side width L) (labRecs h side width fe) = stackRecs h side width (L ++ [fe]) := by
  rw [stackRecs_snoc]
  apply List.ext_getElem (by simp [stackRecs_length, labRecs_length])
  intro i h1 h2
  have hi : i < 2 * (width + width + 1) := by simpa using h2
  rw [List.getElem_zipWith, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ (by rw [stackRecs_length]; exact hi),
    List.getD_eq_getElem _ _ (by rw [labRecs_length]; exact hi)]

theorem pool_split {α : Type} (LR : α → List (List Bool)) (PC : List α) (j : ℕ) (hj : j < PC.length) (tl : List Bool) :
    (PC.flatMap LR).flatMap frame ++ tl =
      ((PC.take j).flatMap LR).flatMap frame ++ ((LR PC[j]).flatMap frame ++
        (((PC.drop (j + 1)).flatMap LR).flatMap frame ++ tl)) := by
  have e : PC = PC.take j ++ PC[j] :: PC.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  conv_lhs => rw [e]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem stream_len (rs : List (List Bool)) (L : ℕ) (hrs : ∀ r ∈ rs, r.length = L) :
    (streamTape rs []).length = rs.length * (2 * L + 1) + 1 := by
  simp only [streamTape, List.length_append, List.length_cons, List.length_nil, List.length_flatMap, frame_length]
  rw [List.map_congr_left (fun r hr => by rw [hrs r hr]), List.map_const', List.sum_replicate, smul_eq_mul]

def tMerge : Fin 4 → Fin 5 := ![0, 1, 2, 3]
def tCopy : Fin 3 → Fin 5 := ![0, 2, 4]

theorem tMerge_inj : Function.Injective tMerge := by decide

theorem install_tMerge (A : Fin 5 → List Bool) (v : Fin 4 → List Bool) :
    install tMerge A v = ![v 0, v 1, v 2, v 3, A 4] := by
  funext i
  fin_cases i
  · exact install_slot tMerge tMerge_inj A v 0
  · exact install_slot tMerge tMerge_inj A v 1
  · exact install_slot tMerge tMerge_inj A v 2
  · exact install_slot tMerge tMerge_inj A v 3
  · exact install_other tMerge A v 4 (by decide)

theorem dockH_tMerge (H : Fin 5 → ℕ) (v : Fin 4 → ℕ) :
    dockH tMerge H v = ![v 0, v 1, v 2, v 3, H 4] := by
  funext i
  fin_cases i
  · exact dockH_slot tMerge tMerge_inj H v 0
  · exact dockH_slot tMerge tMerge_inj H v 1
  · exact dockH_slot tMerge tMerge_inj H v 2
  · exact dockH_slot tMerge tMerge_inj H v 3
  · exact dockH_other tMerge H v 4 (by decide)

theorem tCopy_inj : Function.Injective tCopy := by decide

theorem install_tCopy (A : Fin 5 → List Bool) (v : Fin 3 → List Bool) :
    install tCopy A v = ![v 0, A 1, v 1, A 3, v 2] := by
  funext i
  fin_cases i
  · exact install_slot tCopy tCopy_inj A v 0
  · exact install_other tCopy A v 1 (by decide)
  · exact install_slot tCopy tCopy_inj A v 1
  · exact install_other tCopy A v 3 (by decide)
  · exact install_slot tCopy tCopy_inj A v 2

theorem dockH_tCopy (H : Fin 5 → ℕ) (v : Fin 3 → ℕ) :
    dockH tCopy H v = ![v 0, H 1, v 1, H 3, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot tCopy tCopy_inj H v 0
  · exact dockH_other tCopy H v 1 (by decide)
  · exact dockH_slot tCopy tCopy_inj H v 1
  · exact dockH_other tCopy H v 3 (by decide)
  · exact dockH_slot tCopy tCopy_inj H v 2

/-- The merge with the stack and scratch heads returned to cell `0`. -/
noncomputable def mergeAllMask := MaskedReset.machine mergeAllM ![true, false, true]
noncomputable def tMergeD := RecoveryFocus.machine tMerge mergeAllMask
noncomputable def tCopyD := RecoveryFocus.machine tCopy copyS
/-- **A label inside the mask** (tapes: 0 stack, 1 pool, 2 scratch, 3 merge log, 4 copy log). -/
noncomputable def trueArmM := Composition.machine tMergeD tCopyD
/-- **A label outside the mask** (tapes: 0 stack, 1 pool, 2 log). -/
noncomputable def falseArmM := MaskedReset.machine (StreamController.machine skipBodyM 0) ![true, false]

def mergeAllCost (R0 L1 h : ℕ) : ℕ := R0 * (mergeCost L1 h + 2) + 1 + 1 + 1
def copyCost (R0 W : ℕ) : ℕ := 1 + 1 + (1 + 1 + (2 * appendCost 0 R0 W + 2))
def trueCost (R0 L1 h : ℕ) : ℕ := (2 * mergeAllCost R0 L1 h + 2) + 1 + copyCost R0 (L1 + h)
def skipCost (R0 L1 h : ℕ) : ℕ := R0 * ((2 * L1 + 1) + 1 + (2 * h + 1) + 2) + 1
def falseCost (R0 L1 h : ℕ) : ℕ := 2 * skipCost R0 L1 h + 2

theorem zip_width (rs lr : List (List Bool)) (L1 h : ℕ) (hrs : ∀ r ∈ rs, r.length = L1)
    (hlr : ∀ r ∈ lr, r.length = h) : ∀ r ∈ List.zipWith (· ++ ·) rs lr, r.length = L1 + h := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  rw [List.getElem_zipWith, List.length_append, hrs _ (List.getElem_mem _), hlr _ (List.getElem_mem _)]

/-- **A label inside the mask**: the scratch and the stack both get the merged stack stream; heads of the stack and
scratch return to cell `0`, the pool head steps past the label's records. -/
theorem true_arm (rs lr : List (List Bool)) (R0 L1 h : ℕ) (hr : rs.length = R0) (hl : lr.length = R0)
    (hrs : ∀ r ∈ rs, r.length = L1) (hlr : ∀ r ∈ lr, r.length = h) (hL1 : 1 ≤ L1)
    (S1₀ pre0 rest S2c : List Bool) (capA capC : ℕ) (hA : mergeAllCost R0 L1 h ≤ capA)
    (hC : appendCost 0 R0 (L1 + h) ≤ capC) :
    Step trueArmM (trueCost R0 L1 h) ![0, pre0.length, 0, 0, 0]
      ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), S2c, List.replicate capA false,
        List.replicate capC false]
      ![0, pre0.length + (lr.flatMap frame).length, 0, 0, 0]
      ![overlay (streamTape (List.zipWith (· ++ ·) rs lr) []) (overlay (streamTape rs []) S1₀),
        pre0 ++ (lr.flatMap frame ++ rest), overlay (streamTape (List.zipWith (· ++ ·) rs lr) []) S2c,
        List.replicate capA false, List.replicate capC false] := by
  set M := List.zipWith (· ++ ·) rs lr
  have e1 : overlay (streamTape rs []) S1₀ = streamTape rs (S1₀.drop ((rs.flatMap frame).length + 1)) :=
    overlay_stream rs S1₀
  have m := mergeAll_step rs lr (by omega) L1 h hrs hlr hL1 (S1₀.drop ((rs.flatMap frame).length + 1)) pre0 rest S2c
  rw [← e1] at m
  have mm := m.mask ![true, false, true] (by intro i hi; fin_cases i <;> simp_all) (cap := capA)
    (by rw [hr]; exact hA)
  have mm' : Step mergeAllMask (2 * mergeAllCost R0 L1 h + 2) ![0, pre0.length, 0, 0]
      ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), S2c, List.replicate capA false]
      ![0, pre0.length + (lr.flatMap frame).length, 0, 0]
      ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), overlay (streamTape M []) S2c,
        List.replicate capA false] := by
    rw [hr] at mm
    refine (mm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      (try fin_cases j) <;> rfl
  have d1 := dockRun mm' tMerge tMerge_inj ![0, pre0.length, 0, 0, 0]
    ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), S2c, List.replicate capA false,
      List.replicate capC false] (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tMerge, dockH_tMerge] at d1
  have e2 : overlay (streamTape M []) S2c = streamTape M (S2c.drop ((M.flatMap frame).length + 1)) :=
    overlay_stream M S2c
  have c := copyS_step M (S2c.drop ((M.flatMap frame).length + 1)) (overlay (streamTape rs []) S1₀) (L1 + h) capC
    (zip_width rs lr L1 h hrs hlr) (by omega) (by
      have hM : M.length = R0 := by simp [M]; omega
      rw [hM]; exact hC)
  rw [← e2] at c
  have hM : M.length = R0 := by simp [M]; omega
  rw [hM] at c
  have d2 := dockRun c tCopy tCopy_inj ![0, pre0.length + (lr.flatMap frame).length, 0, 0, 0]
    ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), overlay (streamTape M []) S2c,
      List.replicate capA false, List.replicate capC false] (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_tCopy, dockH_tCopy] at d2
  have d1' := d1.congr (hout' := ![0, pre0.length + (lr.flatMap frame).length, 0, 0, 0])
    (tout' := ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), overlay (streamTape M []) S2c,
      List.replicate capA false, List.replicate capC false])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have d2' := d2.congr (hout' := ![0, pre0.length + (lr.flatMap frame).length, 0, 0, 0])
    (tout' := ![overlay (streamTape M []) (overlay (streamTape rs []) S1₀), pre0 ++ (lr.flatMap frame ++ rest),
      overlay (streamTape M []) S2c, List.replicate capA false, List.replicate capC false])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  exact d1'.seq d2'

/-- **A label outside the mask**: the stack's and the label's records are skipped; the stack head returns to `0`. -/
theorem false_arm (rs lr : List (List Bool)) (R0 L1 h : ℕ) (hr : rs.length = R0) (hl : lr.length = R0)
    (hrs : ∀ r ∈ rs, r.length = L1) (hlr : ∀ r ∈ lr, r.length = h) (hL1 : 1 ≤ L1)
    (S1₀ pre0 rest : List Bool) (capA : ℕ) (hA : skipCost R0 L1 h ≤ capA) :
    Step falseArmM (falseCost R0 L1 h) ![0, pre0.length, 0]
      ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), List.replicate capA false]
      ![0, pre0.length + (lr.flatMap frame).length, 0]
      ![overlay (streamTape rs []) S1₀, pre0 ++ (lr.flatMap frame ++ rest), List.replicate capA false] := by
  have e1 : overlay (streamTape rs []) S1₀ = streamTape rs (S1₀.drop ((rs.flatMap frame).length + 1)) :=
    overlay_stream rs S1₀
  have s := skip_loop2 rs lr (by omega) L1 h hrs hlr hL1 (S1₀.drop ((rs.flatMap frame).length + 1)) pre0 rest
  rw [← e1, hr] at s
  have ss := s.mask ![true, false] (by intro i hi; fin_cases i <;> simp_all) (cap := capA) hA
  refine (ss.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
