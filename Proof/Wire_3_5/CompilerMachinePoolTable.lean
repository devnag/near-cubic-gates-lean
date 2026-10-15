import Proof.Wire_3_5.CompilerMachinePoolShift

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

theorem overlay_frame_same (a b : List Bool) (h : a.length = b.length) : overlay (frame a) (frame b) = frame a := by
  have : (frame a).length = (frame b).length := by simp [h]
  simp [overlay, this]

def tEm : Fin 3 → Fin 12 := ![7, 10, 11]
def tSh : Fin 4 → Fin 12 := ![7, 8, 9, 11]
def tCp : Fin 3 → Fin 12 := ![9, 7, 11]
def tInc : Fin 3 → Fin 12 := ![4, 6, 11]
def tNeq : Fin 4 → Fin 12 := ![4, 2, 5, 11]
def tClr : Fin 3 → Fin 12 := ![3, 2, 11]
def tConv : Fin 4 → Fin 12 := ![0, 1, 2, 11]
def tJz : Fin 3 → Fin 12 := ![3, 4, 11]
def tPut : Fin 1 → Fin 12 := ![10]

theorem tEm_inj : Function.Injective tEm := by decide

theorem install_tEm (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install tEm A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 0, A 8, A 9, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_other tEm A v 0 (by decide)
  · exact install_other tEm A v 1 (by decide)
  · exact install_other tEm A v 2 (by decide)
  · exact install_other tEm A v 3 (by decide)
  · exact install_other tEm A v 4 (by decide)
  · exact install_other tEm A v 5 (by decide)
  · exact install_other tEm A v 6 (by decide)
  · exact install_slot tEm tEm_inj A v 0
  · exact install_other tEm A v 8 (by decide)
  · exact install_other tEm A v 9 (by decide)
  · exact install_slot tEm tEm_inj A v 1
  · exact install_slot tEm tEm_inj A v 2

theorem dockH_tEm (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH tEm H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 0, H 8, H 9, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other tEm H v 0 (by decide)
  · exact dockH_other tEm H v 1 (by decide)
  · exact dockH_other tEm H v 2 (by decide)
  · exact dockH_other tEm H v 3 (by decide)
  · exact dockH_other tEm H v 4 (by decide)
  · exact dockH_other tEm H v 5 (by decide)
  · exact dockH_other tEm H v 6 (by decide)
  · exact dockH_slot tEm tEm_inj H v 0
  · exact dockH_other tEm H v 8 (by decide)
  · exact dockH_other tEm H v 9 (by decide)
  · exact dockH_slot tEm tEm_inj H v 1
  · exact dockH_slot tEm tEm_inj H v 2

theorem tSh_inj : Function.Injective tSh := by decide

theorem install_tSh (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    install tSh A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 0, v 1, v 2, A 10, v 3] := by
  funext i
  fin_cases i
  · exact install_other tSh A v 0 (by decide)
  · exact install_other tSh A v 1 (by decide)
  · exact install_other tSh A v 2 (by decide)
  · exact install_other tSh A v 3 (by decide)
  · exact install_other tSh A v 4 (by decide)
  · exact install_other tSh A v 5 (by decide)
  · exact install_other tSh A v 6 (by decide)
  · exact install_slot tSh tSh_inj A v 0
  · exact install_slot tSh tSh_inj A v 1
  · exact install_slot tSh tSh_inj A v 2
  · exact install_other tSh A v 10 (by decide)
  · exact install_slot tSh tSh_inj A v 3

theorem dockH_tSh (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH tSh H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 0, v 1, v 2, H 10, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other tSh H v 0 (by decide)
  · exact dockH_other tSh H v 1 (by decide)
  · exact dockH_other tSh H v 2 (by decide)
  · exact dockH_other tSh H v 3 (by decide)
  · exact dockH_other tSh H v 4 (by decide)
  · exact dockH_other tSh H v 5 (by decide)
  · exact dockH_other tSh H v 6 (by decide)
  · exact dockH_slot tSh tSh_inj H v 0
  · exact dockH_slot tSh tSh_inj H v 1
  · exact dockH_slot tSh tSh_inj H v 2
  · exact dockH_other tSh H v 10 (by decide)
  · exact dockH_slot tSh tSh_inj H v 3

theorem tCp_inj : Function.Injective tCp := by decide

theorem install_tCp (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install tCp A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 1, A 8, v 0, A 10, v 2] := by
  funext i
  fin_cases i
  · exact install_other tCp A v 0 (by decide)
  · exact install_other tCp A v 1 (by decide)
  · exact install_other tCp A v 2 (by decide)
  · exact install_other tCp A v 3 (by decide)
  · exact install_other tCp A v 4 (by decide)
  · exact install_other tCp A v 5 (by decide)
  · exact install_other tCp A v 6 (by decide)
  · exact install_slot tCp tCp_inj A v 1
  · exact install_other tCp A v 8 (by decide)
  · exact install_slot tCp tCp_inj A v 0
  · exact install_other tCp A v 10 (by decide)
  · exact install_slot tCp tCp_inj A v 2

theorem dockH_tCp (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH tCp H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 1, H 8, v 0, H 10, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other tCp H v 0 (by decide)
  · exact dockH_other tCp H v 1 (by decide)
  · exact dockH_other tCp H v 2 (by decide)
  · exact dockH_other tCp H v 3 (by decide)
  · exact dockH_other tCp H v 4 (by decide)
  · exact dockH_other tCp H v 5 (by decide)
  · exact dockH_other tCp H v 6 (by decide)
  · exact dockH_slot tCp tCp_inj H v 1
  · exact dockH_other tCp H v 8 (by decide)
  · exact dockH_slot tCp tCp_inj H v 0
  · exact dockH_other tCp H v 10 (by decide)
  · exact dockH_slot tCp tCp_inj H v 2

theorem tInc_inj : Function.Injective tInc := by decide

theorem install_tInc (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install tInc A v = ![A 0, A 1, A 2, A 3, v 0, A 5, v 1, A 7, A 8, A 9, A 10, v 2] := by
  funext i
  fin_cases i
  · exact install_other tInc A v 0 (by decide)
  · exact install_other tInc A v 1 (by decide)
  · exact install_other tInc A v 2 (by decide)
  · exact install_other tInc A v 3 (by decide)
  · exact install_slot tInc tInc_inj A v 0
  · exact install_other tInc A v 5 (by decide)
  · exact install_slot tInc tInc_inj A v 1
  · exact install_other tInc A v 7 (by decide)
  · exact install_other tInc A v 8 (by decide)
  · exact install_other tInc A v 9 (by decide)
  · exact install_other tInc A v 10 (by decide)
  · exact install_slot tInc tInc_inj A v 2

theorem dockH_tInc (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH tInc H v = ![H 0, H 1, H 2, H 3, v 0, H 5, v 1, H 7, H 8, H 9, H 10, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other tInc H v 0 (by decide)
  · exact dockH_other tInc H v 1 (by decide)
  · exact dockH_other tInc H v 2 (by decide)
  · exact dockH_other tInc H v 3 (by decide)
  · exact dockH_slot tInc tInc_inj H v 0
  · exact dockH_other tInc H v 5 (by decide)
  · exact dockH_slot tInc tInc_inj H v 1
  · exact dockH_other tInc H v 7 (by decide)
  · exact dockH_other tInc H v 8 (by decide)
  · exact dockH_other tInc H v 9 (by decide)
  · exact dockH_other tInc H v 10 (by decide)
  · exact dockH_slot tInc tInc_inj H v 2

theorem tNeq_inj : Function.Injective tNeq := by decide

theorem install_tNeq (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    install tNeq A v = ![A 0, A 1, v 1, A 3, v 0, v 2, A 6, A 7, A 8, A 9, A 10, v 3] := by
  funext i
  fin_cases i
  · exact install_other tNeq A v 0 (by decide)
  · exact install_other tNeq A v 1 (by decide)
  · exact install_slot tNeq tNeq_inj A v 1
  · exact install_other tNeq A v 3 (by decide)
  · exact install_slot tNeq tNeq_inj A v 0
  · exact install_slot tNeq tNeq_inj A v 2
  · exact install_other tNeq A v 6 (by decide)
  · exact install_other tNeq A v 7 (by decide)
  · exact install_other tNeq A v 8 (by decide)
  · exact install_other tNeq A v 9 (by decide)
  · exact install_other tNeq A v 10 (by decide)
  · exact install_slot tNeq tNeq_inj A v 3

theorem dockH_tNeq (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH tNeq H v = ![H 0, H 1, v 1, H 3, v 0, v 2, H 6, H 7, H 8, H 9, H 10, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other tNeq H v 0 (by decide)
  · exact dockH_other tNeq H v 1 (by decide)
  · exact dockH_slot tNeq tNeq_inj H v 1
  · exact dockH_other tNeq H v 3 (by decide)
  · exact dockH_slot tNeq tNeq_inj H v 0
  · exact dockH_slot tNeq tNeq_inj H v 2
  · exact dockH_other tNeq H v 6 (by decide)
  · exact dockH_other tNeq H v 7 (by decide)
  · exact dockH_other tNeq H v 8 (by decide)
  · exact dockH_other tNeq H v 9 (by decide)
  · exact dockH_other tNeq H v 10 (by decide)
  · exact dockH_slot tNeq tNeq_inj H v 3

theorem tClr_inj : Function.Injective tClr := by decide

theorem install_tClr (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install tClr A v = ![A 0, A 1, v 1, v 0, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i
  fin_cases i
  · exact install_other tClr A v 0 (by decide)
  · exact install_other tClr A v 1 (by decide)
  · exact install_slot tClr tClr_inj A v 1
  · exact install_slot tClr tClr_inj A v 0
  · exact install_other tClr A v 4 (by decide)
  · exact install_other tClr A v 5 (by decide)
  · exact install_other tClr A v 6 (by decide)
  · exact install_other tClr A v 7 (by decide)
  · exact install_other tClr A v 8 (by decide)
  · exact install_other tClr A v 9 (by decide)
  · exact install_other tClr A v 10 (by decide)
  · exact install_slot tClr tClr_inj A v 2

theorem dockH_tClr (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH tClr H v = ![H 0, H 1, v 1, v 0, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other tClr H v 0 (by decide)
  · exact dockH_other tClr H v 1 (by decide)
  · exact dockH_slot tClr tClr_inj H v 1
  · exact dockH_slot tClr tClr_inj H v 0
  · exact dockH_other tClr H v 4 (by decide)
  · exact dockH_other tClr H v 5 (by decide)
  · exact dockH_other tClr H v 6 (by decide)
  · exact dockH_other tClr H v 7 (by decide)
  · exact dockH_other tClr H v 8 (by decide)
  · exact dockH_other tClr H v 9 (by decide)
  · exact dockH_other tClr H v 10 (by decide)
  · exact dockH_slot tClr tClr_inj H v 2

theorem tConv_inj : Function.Injective tConv := by decide

theorem install_tConv (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    install tConv A v = ![v 0, v 1, v 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 3] := by
  funext i
  fin_cases i
  · exact install_slot tConv tConv_inj A v 0
  · exact install_slot tConv tConv_inj A v 1
  · exact install_slot tConv tConv_inj A v 2
  · exact install_other tConv A v 3 (by decide)
  · exact install_other tConv A v 4 (by decide)
  · exact install_other tConv A v 5 (by decide)
  · exact install_other tConv A v 6 (by decide)
  · exact install_other tConv A v 7 (by decide)
  · exact install_other tConv A v 8 (by decide)
  · exact install_other tConv A v 9 (by decide)
  · exact install_other tConv A v 10 (by decide)
  · exact install_slot tConv tConv_inj A v 3

theorem dockH_tConv (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH tConv H v = ![v 0, v 1, v 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot tConv tConv_inj H v 0
  · exact dockH_slot tConv tConv_inj H v 1
  · exact dockH_slot tConv tConv_inj H v 2
  · exact dockH_other tConv H v 3 (by decide)
  · exact dockH_other tConv H v 4 (by decide)
  · exact dockH_other tConv H v 5 (by decide)
  · exact dockH_other tConv H v 6 (by decide)
  · exact dockH_other tConv H v 7 (by decide)
  · exact dockH_other tConv H v 8 (by decide)
  · exact dockH_other tConv H v 9 (by decide)
  · exact dockH_other tConv H v 10 (by decide)
  · exact dockH_slot tConv tConv_inj H v 3

theorem tJz_inj : Function.Injective tJz := by decide

theorem install_tJz (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install tJz A v = ![A 0, A 1, A 2, v 0, v 1, A 5, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i
  fin_cases i
  · exact install_other tJz A v 0 (by decide)
  · exact install_other tJz A v 1 (by decide)
  · exact install_other tJz A v 2 (by decide)
  · exact install_slot tJz tJz_inj A v 0
  · exact install_slot tJz tJz_inj A v 1
  · exact install_other tJz A v 5 (by decide)
  · exact install_other tJz A v 6 (by decide)
  · exact install_other tJz A v 7 (by decide)
  · exact install_other tJz A v 8 (by decide)
  · exact install_other tJz A v 9 (by decide)
  · exact install_other tJz A v 10 (by decide)
  · exact install_slot tJz tJz_inj A v 2

theorem dockH_tJz (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH tJz H v = ![H 0, H 1, H 2, v 0, v 1, H 5, H 6, H 7, H 8, H 9, H 10, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other tJz H v 0 (by decide)
  · exact dockH_other tJz H v 1 (by decide)
  · exact dockH_other tJz H v 2 (by decide)
  · exact dockH_slot tJz tJz_inj H v 0
  · exact dockH_slot tJz tJz_inj H v 1
  · exact dockH_other tJz H v 5 (by decide)
  · exact dockH_other tJz H v 6 (by decide)
  · exact dockH_other tJz H v 7 (by decide)
  · exact dockH_other tJz H v 8 (by decide)
  · exact dockH_other tJz H v 9 (by decide)
  · exact dockH_other tJz H v 10 (by decide)
  · exact dockH_slot tJz tJz_inj H v 2

theorem tPut_inj : Function.Injective tPut := by decide

theorem install_tPut (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install tPut A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 0, A 11] := by
  funext i
  fin_cases i
  · exact install_other tPut A v 0 (by decide)
  · exact install_other tPut A v 1 (by decide)
  · exact install_other tPut A v 2 (by decide)
  · exact install_other tPut A v 3 (by decide)
  · exact install_other tPut A v 4 (by decide)
  · exact install_other tPut A v 5 (by decide)
  · exact install_other tPut A v 6 (by decide)
  · exact install_other tPut A v 7 (by decide)
  · exact install_other tPut A v 8 (by decide)
  · exact install_other tPut A v 9 (by decide)
  · exact install_slot tPut tPut_inj A v 0
  · exact install_other tPut A v 11 (by decide)

theorem dockH_tPut (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH tPut H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 0, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other tPut H v 0 (by decide)
  · exact dockH_other tPut H v 1 (by decide)
  · exact dockH_other tPut H v 2 (by decide)
  · exact dockH_other tPut H v 3 (by decide)
  · exact dockH_other tPut H v 4 (by decide)
  · exact dockH_other tPut H v 5 (by decide)
  · exact dockH_other tPut H v 6 (by decide)
  · exact dockH_other tPut H v 7 (by decide)
  · exact dockH_other tPut H v 8 (by decide)
  · exact dockH_other tPut H v 9 (by decide)
  · exact dockH_slot tPut tPut_inj H v 0
  · exact dockH_other tPut H v 11 (by decide)

/-- The table machine's heads: the counts cursor and the table cursor. -/
def tH (a o : ℕ) : Fin 12 → ℕ := ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0]

/-- The table machine's tapes. -/
def tA (CN K CV ZW J CL ON OH MK TM TB LG : List Bool) : Fin 12 → List Bool := ![CN, K, CV, ZW, J, CL, ON, OH, MK, TM, TB, LG]

/-- One label: emit its entry, shift the entry register to the next label, count, compare. -/
noncomputable def labBody := Composition.machine (RecoveryFocus.machine tEm emitM)
  (Composition.machine (RecoveryFocus.machine tSh (zipM shOut shNxt false))
    (Composition.machine (RecoveryFocus.machine tCp regCopyM)
      (Composition.machine (RecoveryFocus.machine tInc incM) (RecoveryFocus.machine tNeq neqM))))

def labCost (L Wc : ℕ) : ℕ := (2 * (2 * L + 1) + 2) + 1 + ((2 * (2 * L + 1) + 2) + 1 + ((2 * (2 * L + 1) + 2) + 1 +
  ((2 * (2 * Wc + 2) + 2) + 1 + (2 * (2 * Wc + 1) + 2))))

/-- The entry of label `c`. -/
def entC (Q W c : ℕ) : List Bool := entryWord Q W 0 (2 ^ c)

theorem entC_length (Q W c : ℕ) : (entC Q W c).length = Q + W + 1 := entryWord_length Q W 0 _ (by omega)

theorem binary_ne_iff (Wc x y : ℕ) (hx : x < 2 ^ Wc) (hy : y < 2 ^ Wc) : (!decide (binary Wc x = binary Wc y)) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : binary Wc x ≠ binary Wc y := by
      intro he
      have := congrArg RadixSemantics.value he
      rw [binary_value Wc x hx, binary_value Wc y hy] at this
      exact hxy this
    simp [this, hxy]

/-- **One label's entry** emitted and the registers advanced to the next label. -/
theorem lab_step (Q W Wc c0 v j : ℕ) (CN K ZW TMx out BW : List Bool) (a cap : ℕ) (hj : j < v) (hv : v < 2 ^ Wc)
    (hc1 : 2 * (Q + W + 1) + 1 ≤ cap) (hc2 : 2 * Wc + 2 ≤ cap) (hTM : TMx.length = (frame (entC Q W 0)).length) :
    Step labBody (labCost (Q + W + 1) Wc) (tH a out.length)
      (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc j)) [true] [true] (frame (entC Q W (c0 + j)))
        (frame (shiftMask Q W)) TMx (overlay out BW) (List.replicate cap false))
      (tH a (out ++ frame (entC Q W (c0 + j))).length)
      (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc (j + 1))) [decide (j + 1 ≠ v)] [true]
        (frame (entC Q W (c0 + j + 1))) (frame (shiftMask Q W)) (frame (entC Q W (c0 + j + 1)))
        (overlay (out ++ frame (entC Q W (c0 + j))) BW) (List.replicate cap false)) := by
  set lg := List.replicate cap false
  have hlen : ∀ c, (entC Q W c).length = Q + W + 1 := entC_length Q W
  have em := emitT (entC Q W (c0 + j)) [] out BW cap (by rw [hlen]; omega)
  simp only [List.append_nil] at em
  have e1 := dockRun em tEm tEm_inj (tH a out.length)
    (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc j)) [true] [true] (frame (entC Q W (c0 + j)))
      (frame (shiftMask Q W)) TMx (overlay out BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tEm, dockH_tEm] at e1
  have hsh : ZipMap.map shOut shNxt (entC Q W (c0 + j)) (shiftMask Q W) false = entC Q W (c0 + j + 1) := by
    unfold entC; rw [shift_entry, pow_succ, Nat.mul_comm]
  have hml : (entC Q W (c0 + j)).length = (shiftMask Q W).length := by rw [hlen]; simp [shiftMask]; omega
  have z := zipT shOut shNxt false (entC Q W (c0 + j)) (shiftMask Q W) [] [] TMx hml cap (by rw [hlen]; omega)
  rw [hsh, List.append_nil, List.append_nil] at z
  have hTM' : overlay (frame (entC Q W (c0 + j + 1))) TMx = frame (entC Q W (c0 + j + 1)) := by
    unfold overlay; rw [List.drop_eq_nil_of_le (by rw [hTM]; simp [hlen])]; simp
  rw [hTM'] at z
  have e2 := dockRun z tSh tSh_inj (tH a (out ++ frame (entC Q W (c0 + j))).length)
    (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc j)) [true] [true] (frame (entC Q W (c0 + j)))
      (frame (shiftMask Q W)) TMx (overlay (out ++ frame (entC Q W (c0 + j))) BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tSh, dockH_tSh] at e2
  have cpy := regCopyStep (entC Q W (c0 + j + 1)) [] (frame (entC Q W (c0 + j))) cap (by rw [hlen]; omega)
  rw [List.append_nil, overlay_frame_same _ _ (by rw [hlen, hlen])] at cpy
  have e3 := dockRun cpy tCp tCp_inj (tH a (out ++ frame (entC Q W (c0 + j))).length)
    (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc j)) [true] [true] (frame (entC Q W (c0 + j)))
      (frame (shiftMask Q W)) (frame (entC Q W (c0 + j + 1))) (overlay (out ++ frame (entC Q W (c0 + j))) BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tCp, dockH_tCp] at e3
  have inc := incStep Wc j true cap hc2
  simp only [Bool.toNat_true] at inc
  have e4 := dockRun inc tInc tInc_inj (tH a (out ++ frame (entC Q W (c0 + j))).length)
    (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc j)) [true] [true] (frame (entC Q W (c0 + j + 1)))
      (frame (shiftMask Q W)) (frame (entC Q W (c0 + j + 1))) (overlay (out ++ frame (entC Q W (c0 + j))) BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tInc, dockH_tInc] at e4
  have nq := neqStep (binary Wc (j + 1)) (binary Wc v) true (by simp) cap (by simp; omega)
  rw [binary_ne_iff Wc (j + 1) v (by omega) hv] at nq
  have e5 := dockRun nq tNeq tNeq_inj (tH a (out ++ frame (entC Q W (c0 + j))).length)
    (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc (j + 1))) [true] [true] (frame (entC Q W (c0 + j + 1)))
      (frame (shiftMask Q W)) (frame (entC Q W (c0 + j + 1))) (overlay (out ++ frame (entC Q W (c0 + j))) BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tNeq, dockH_tNeq] at e5
  have j5 := (e1.congr (by funext i; fin_cases i <;> simp [tH]) (by funext i; fin_cases i <;> rfl)).seq
    ((e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      ((e3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
        ((e4.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
          (e5.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)))))
  refine (j5.congr ?_ ?_).enlarge (le_of_eq (by simp [labCost, hlen]))
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- **A uniform body while a cell says `j ≠ v`**: the cell holds `[decide (j ≠ v)]` before pass `j`. -/
theorem cellRun {t s : ℕ} (body : Machine t s) (src : Fin t) (v : ℕ) (bH : ℕ → Fin t → ℕ) (bA : ℕ → Fin t → List Bool)
    (hsrcA : ∀ j, bA j src = [decide (j ≠ v)]) (hsrcH : ∀ j, bH j src = 0) (c : ℕ)
    (hstep : ∀ j, j < v → Step body c (bH j) (bA j) (bH (j + 1)) (bA (j + 1))) :
    Step (StreamController.machine body src) (v * (c + 2) + 1) (bH 0) (bA 0) (bH v) (bA v) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := v
      H := bH
      A := bA
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA j src) (bH j src) = true
        rw [hsrcA, hsrcH]
        simp [readTapeBit]; omega
      halt := by
        show readTapeBit (bA v src) (bH v src) = false
        rw [hsrcA, hsrcH]
        simp [readTapeBit] }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  exact hW

/-- The loop over one atom's labels (the loop cell is tape 5). -/
noncomputable def labsM := StreamController.machine labBody 5

/-- The scratch register after `j` labels. -/
def tmpAt (Q W c0 : ℕ) (TMx : List Bool) (j : ℕ) : List Bool := if j = 0 then TMx else frame (entC Q W (c0 + j))

/-- The entries of labels `c0, …, c0+j−1`, framed. -/
def entsOf (Q W c0 j : ℕ) : List Bool := ((List.range' c0 j).map (entC Q W)).flatMap frame

theorem entsOf_succ (Q W c0 j : ℕ) : entsOf Q W c0 (j + 1) = entsOf Q W c0 j ++ frame (entC Q W (c0 + j)) := by
  simp [entsOf, List.range'_concat, List.flatMap_append]

/-- **All labels of one atom**: `v` entries emitted, the registers advanced `v` labels. -/
theorem labs_run (Q W Wc c0 v : ℕ) (CN K ZW TMx out BW : List Bool) (a cap : ℕ) (hv : v < 2 ^ Wc)
    (hc1 : 2 * (Q + W + 1) + 1 ≤ cap) (hc2 : 2 * Wc + 2 ≤ cap) (hTM : TMx.length = (frame (entC Q W 0)).length) :
    Step labsM (v * (labCost (Q + W + 1) Wc + 2) + 1) (tH a out.length)
      (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc 0)) [decide (0 ≠ v)] [true] (frame (entC Q W c0))
        (frame (shiftMask Q W)) TMx (overlay out BW) (List.replicate cap false))
      (tH a (out ++ entsOf Q W c0 v).length)
      (tA CN K (frame (binary Wc v)) ZW (frame (binary Wc v)) [decide (v ≠ v)] [true] (frame (entC Q W (c0 + v)))
        (frame (shiftMask Q W)) (tmpAt Q W c0 TMx v) (overlay (out ++ entsOf Q W c0 v) BW)
        (List.replicate cap false)) := by
  have hr := cellRun labBody 5 v (fun j => tH a (out ++ entsOf Q W c0 j).length)
    (fun j => tA CN K (frame (binary Wc v)) ZW (frame (binary Wc j)) [decide (j ≠ v)] [true] (frame (entC Q W (c0 + j)))
      (frame (shiftMask Q W)) (tmpAt Q W c0 TMx j) (overlay (out ++ entsOf Q W c0 j) BW) (List.replicate cap false))
    (fun j => rfl) (fun j => rfl) (labCost (Q + W + 1) Wc) (by
      intro j hj
      have hT : (tmpAt Q W c0 TMx j).length = (frame (entC Q W 0)).length := by
        unfold tmpAt; split_ifs
        · exact hTM
        · simp [entC_length]
      have hd : decide (j ≠ v) = true := by simp; omega
      have b := lab_step Q W Wc c0 v j CN K ZW (tmpAt Q W c0 TMx j) (out ++ entsOf Q W c0 j) BW a cap hj hv hc1 hc2 hT
      rw [hd]
      have ht : tmpAt Q W c0 TMx (j + 1) = frame (entC Q W (c0 + j + 1)) := by simp [tmpAt, Nat.add_assoc]
      rw [ht, entsOf_succ, ← List.append_assoc, show c0 + (j + 1) = c0 + j + 1 by omega]
      exact b)
  have e0 : entsOf Q W c0 0 = [] := rfl
  have t0 : tmpAt Q W c0 TMx 0 = TMx := by simp [tmpAt]
  rw [e0, List.append_nil, t0] at hr
  exact hr

/-- One atom: clear and read its count, zero the loop counter, compare, emit its labels, close its stream. -/
noncomputable def atomM := Composition.machine (RecoveryFocus.machine tClr regCopyM)
  (Composition.machine (RecoveryFocus.machine tConv convR) (Composition.machine (RecoveryFocus.machine tJz regCopyM)
    (Composition.machine (RecoveryFocus.machine tNeq neqM) (Composition.machine labsM
      (RecoveryFocus.machine tPut (putM false))))))

/-- A uniform bound on one atom's cost, for counts at most `V`. -/
def atomCost (Q W Wc V : ℕ) : ℕ := (2 * (2 * Wc + 1) + 2) + 1 + ((2 * (3 * Wc + 2) + 2) + 1 + ((2 * (2 * Wc + 1) + 2) + 1 +
  ((2 * (2 * Wc + 1) + 2) + 1 + ((V * (labCost (Q + W + 1) Wc + 2) + 1) + 1 + 1))))

/-- **One atom's stream of the children table**: the entries of labels `c0, …, c0+v−1`, closed by `false`. -/
theorem atom_run (Q W Wc c0 v V x y : ℕ) (e : Bool) (pre post out BW : List Bool) (capK cap : ℕ) (h1 : 1 ≤ Wc)
    (hv : v < 2 ^ Wc) (hV : v ≤ V) (hK : natBitLength v ≤ capK) (hc1 : 2 * (Q + W + 1) + 1 ≤ cap)
    (hc2 : 2 * Wc + 2 ≤ cap) (hc3 : 3 * Wc + 2 ≤ cap) :
    Step atomM (atomCost Q W Wc V) (tH pre.length out.length)
      (tA (pre ++ natWord v ++ post) (false :: List.replicate capK true) (frame (binary Wc x)) (frame (binary Wc 0))
        (frame (binary Wc y)) [e] [true] (frame (entC Q W c0)) (frame (shiftMask Q W)) (frame (entC Q W c0))
        (overlay out BW) (List.replicate cap false))
      (tH (pre ++ natWord v).length (out ++ atomStream ((List.range' c0 v).map (entC Q W))).length)
      (tA (pre ++ natWord v ++ post) (false :: List.replicate capK true) (frame (binary Wc v)) (frame (binary Wc 0))
        (frame (binary Wc v)) [false] [true] (frame (entC Q W (c0 + v))) (frame (shiftMask Q W))
        (frame (entC Q W (c0 + v))) (overlay (out ++ atomStream ((List.range' c0 v).map (entC Q W))) BW)
        (List.replicate cap false)) := by
  set CN := pre ++ natWord v ++ post
  set K := false :: List.replicate capK true
  set lg := List.replicate cap false
  have hbl : ∀ z, (binary Wc z).length = Wc := fun z => binary_length Wc z
  have c1 := regCopyStep (binary Wc 0) [] (frame (binary Wc x)) cap (by rw [hbl]; omega)
  rw [List.append_nil, overlay_frame_same _ _ (by simp)] at c1
  have e1 := dockRun c1 tClr tClr_inj (tH pre.length out.length)
    (tA CN K (frame (binary Wc x)) (frame (binary Wc 0)) (frame (binary Wc y)) [e] [true] (frame (entC Q W c0))
      (frame (shiftMask Q W)) (frame (entC Q W c0)) (overlay out BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tClr, dockH_tClr] at e1
  have hcv : convCost v ≤ cap := by
    have := natBitLength_le v Wc h1 hv; unfold convCost; omega
  have c2 := convR_run Wc v h1 hv pre post (frame (binary Wc 0)) capK cap hK hcv
  rw [overlay_frame_same _ _ (by simp), overlay_frame_same _ _ (by simp)] at c2
  have e2 := dockRun c2 tConv tConv_inj (tH pre.length out.length)
    (tA CN K (frame (binary Wc 0)) (frame (binary Wc 0)) (frame (binary Wc y)) [e] [true] (frame (entC Q W c0))
      (frame (shiftMask Q W)) (frame (entC Q W c0)) (overlay out BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tConv, dockH_tConv] at e2
  have c3 := regCopyStep (binary Wc 0) [] (frame (binary Wc y)) cap (by rw [hbl]; omega)
  rw [List.append_nil, overlay_frame_same _ _ (by simp)] at c3
  have e3 := dockRun c3 tJz tJz_inj (tH (pre.length + (natWord v).length) out.length)
    (tA CN K (frame (binary Wc v)) (frame (binary Wc 0)) (frame (binary Wc y)) [e] [true] (frame (entC Q W c0))
      (frame (shiftMask Q W)) (frame (entC Q W c0)) (overlay out BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tJz, dockH_tJz] at e3
  have c4 := neqStep (binary Wc 0) (binary Wc v) e (by simp) cap (by rw [hbl]; omega)
  rw [binary_ne_iff Wc 0 v (Nat.two_pow_pos Wc) hv] at c4
  have e4 := dockRun c4 tNeq tNeq_inj (tH (pre.length + (natWord v).length) out.length)
    (tA CN K (frame (binary Wc v)) (frame (binary Wc 0)) (frame (binary Wc 0)) [e] [true] (frame (entC Q W c0))
      (frame (shiftMask Q W)) (frame (entC Q W c0)) (overlay out BW) lg)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_tNeq, dockH_tNeq] at e4
  have c5 := labs_run Q W Wc c0 v CN K (frame (binary Wc 0)) (frame (entC Q W c0)) out BW
    (pre.length + (natWord v).length) cap hv hc1 hc2 (by simp [entC_length])
  have ht : tmpAt Q W c0 (frame (entC Q W c0)) v = frame (entC Q W (c0 + v)) := by
    unfold tmpAt; split_ifs with hv0
    · subst hv0; rfl
    · rfl
  rw [ht] at c5
  have p0 := putStep false (overlay (out ++ entsOf Q W c0 v) BW) (out ++ entsOf Q W c0 v).length
  rw [overlay_write] at p0
  have e6 := dockRun p0 tPut tPut_inj (tH (pre.length + (natWord v).length) (out ++ entsOf Q W c0 v).length)
    (tA CN K (frame (binary Wc v)) (frame (binary Wc 0)) (frame (binary Wc v)) [decide (v ≠ v)] [true]
      (frame (entC Q W (c0 + v))) (frame (shiftMask Q W)) (frame (entC Q W (c0 + v)))
      (overlay (out ++ entsOf Q W c0 v) BW) lg)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_tPut, dockH_tPut] at e6
  have j := (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    ((e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      ((e3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
        ((e4.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
          (c5.seq (e6.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))))))
  have hst : out ++ entsOf Q W c0 v ++ [false] = out ++ atomStream ((List.range' c0 v).map (entC Q W)) := by
    simp [entsOf, atomStream, List.append_assoc]
  have hcs : (pre ++ natWord v).length = pre.length + (natWord v).length := by simp
  refine (j.congr ?_ ?_).enlarge ?_
  · rw [hcs, ← hst]; funext i; fin_cases i <;> simp [tH, Nat.add_assoc]
  · rw [← hst]; funext i; fin_cases i <;> simp [tA]
  · have := natBitLength_le v Wc h1 hv
    have hl : v * (labCost (Q + W + 1) Wc + 2) ≤ V * (labCost (Q + W + 1) Wc + 2) := Nat.mul_le_mul_right _ hV
    simp only [atomCost, hbl, convCost]
    omega

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
