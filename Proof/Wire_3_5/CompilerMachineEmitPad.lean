import Proof.Wire_3_5.CompilerMachineEmitLabels

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length write_boundary)

theorem binary_value_self : ∀ w : List Bool, binary w.length (value w) = w
  | [] => rfl
  | b :: w => by
    simp only [List.length_cons, binary, value]
    have h1 : (b.toNat + 2 * value w) % 2 = b.toNat := by cases b <;> simp [Bool.toNat]
    have h2 : (b.toNat + 2 * value w) / 2 = value w := by cases b <;> simp [Bool.toNat]; omega
    rw [h1, h2, binary_value_self w]
    cases b <;> rfl

theorem binary_pad_value (bits : List Bool) (W : ℕ) (hL : bits.length ≤ W) :
    binary W (value bits) = bits ++ List.replicate (W - bits.length) false := by
  have e := binary_append' bits.length (W - bits.length) (value bits)
  rw [show bits.length + (W - bits.length) = W by omega, binary_value_self,
    Nat.div_eq_of_lt (value_lt bits), binary_zero'] at e
  exact e

/-- **Writing the marker over the copied terminator** leaves the padded register. -/
theorem pad_write (bits Y : List Bool) (W : ℕ) (hL : bits.length < W) :
    writeTapeBit (overlay (frame bits) (overlay (frame (List.replicate W false)) Y)) (2 * bits.length) true =
      overlay (frame (binary W (value bits))) Y := by
  set L := bits.length
  set k := W - L - 1
  have eW : List.replicate W false = List.replicate L false ++ (false :: List.replicate k false) := by
    rw [← List.replicate_succ, ← List.replicate_add]
    congr 1
    omega
  have hfW : (frame (List.replicate W false)).length = 2 * W + 1 := by simp
  have hX : overlay (frame (List.replicate W false)) Y =
      fpre (List.replicate L false) ++ (true :: false :: (frame (List.replicate k false) ++ Y.drop (2 * W + 1))) := by
    unfold overlay
    rw [hfW, eW, frame_append']
    simp [frame, List.append_assoc]
  have hfl : (fpre (List.replicate L false)).length = 2 * L := by simp [fpre_length]
  have hdrop : (fpre (List.replicate L false) ++ (true :: false :: (frame (List.replicate k false) ++
      Y.drop (2 * W + 1)))).drop (2 * L + 1) = false :: (frame (List.replicate k false) ++ Y.drop (2 * W + 1)) := by
    rw [show 2 * L + 1 = (fpre (List.replicate L false)).length + 1 by omega, ← List.drop_drop,
      List.drop_append_length]
    rfl
  have hov : overlay (frame bits) (overlay (frame (List.replicate W false)) Y) =
      fpre bits ++ (false :: false :: (frame (List.replicate k false) ++ Y.drop (2 * W + 1))) := by
    rw [hX]
    unfold overlay
    rw [frame_length, hdrop, frame_fpre, List.append_assoc]
    rfl
  have hfb : (fpre bits).length = 2 * L := by simp [fpre_length, L]
  rw [hov, ← hfb, write_boundary]
  have hb : binary W (value bits) = bits ++ (false :: List.replicate k false) := by
    rw [binary_pad_value bits W hL.le]
    congr 1
    rw [← List.replicate_succ]
    congr 1
    omega
  unfold overlay
  rw [hb, frame_length, List.length_append, List.length_cons, List.length_replicate, frame_append']
  simp only [List.drop_one, List.tail_cons, List.append_assoc]
  have hk : 2 * (L + (k + 1)) + 1 = 2 * W + 1 := by omega
  rw [hk]
  rfl

def pZ : Fin 3 → Fin 4 := ![1, 2, 3]
def pMv : Fin 1 → Fin 4 := ![0]
def pInner : Fin 3 → Fin 4 := ![0, 2, 3]
def qCp : Fin 2 → Fin 2 := ![0, 1]
def qL : Fin 1 → Fin 2 := ![1]
def qPut : Fin 1 → Fin 2 := ![1]

theorem pZ_inj : Function.Injective pZ := by decide

theorem install_pZ (A : Fin 4 → List Bool) (v : Fin 3 → List Bool) :
    install pZ A v = ![A 0, v 0, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_other pZ A v 0 (by decide)
  · exact install_slot pZ pZ_inj A v 0
  · exact install_slot pZ pZ_inj A v 1
  · exact install_slot pZ pZ_inj A v 2

theorem dockH_pZ (H : Fin 4 → ℕ) (v : Fin 3 → ℕ) :
    dockH pZ H v = ![H 0, v 0, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other pZ H v 0 (by decide)
  · exact dockH_slot pZ pZ_inj H v 0
  · exact dockH_slot pZ pZ_inj H v 1
  · exact dockH_slot pZ pZ_inj H v 2

theorem pMv_inj : Function.Injective pMv := by decide

theorem install_pMv (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    install pMv A v = ![v 0, A 1, A 2, A 3] := by
  funext i
  fin_cases i
  · exact install_slot pMv pMv_inj A v 0
  · exact install_other pMv A v 1 (by decide)
  · exact install_other pMv A v 2 (by decide)
  · exact install_other pMv A v 3 (by decide)

theorem dockH_pMv (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) :
    dockH pMv H v = ![v 0, H 1, H 2, H 3] := by
  funext i
  fin_cases i
  · exact dockH_slot pMv pMv_inj H v 0
  · exact dockH_other pMv H v 1 (by decide)
  · exact dockH_other pMv H v 2 (by decide)
  · exact dockH_other pMv H v 3 (by decide)

theorem pInner_inj : Function.Injective pInner := by decide

theorem install_pInner (A : Fin 4 → List Bool) (v : Fin 3 → List Bool) :
    install pInner A v = ![v 0, A 1, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_slot pInner pInner_inj A v 0
  · exact install_other pInner A v 1 (by decide)
  · exact install_slot pInner pInner_inj A v 1
  · exact install_slot pInner pInner_inj A v 2

theorem dockH_pInner (H : Fin 4 → ℕ) (v : Fin 3 → ℕ) :
    dockH pInner H v = ![v 0, H 1, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot pInner pInner_inj H v 0
  · exact dockH_other pInner H v 1 (by decide)
  · exact dockH_slot pInner pInner_inj H v 1
  · exact dockH_slot pInner pInner_inj H v 2

theorem qCp_inj : Function.Injective qCp := by decide

theorem install_qCp (A : Fin 2 → List Bool) (v : Fin 2 → List Bool) :
    install qCp A v = ![v 0, v 1] := by
  funext i
  fin_cases i
  · exact install_slot qCp qCp_inj A v 0
  · exact install_slot qCp qCp_inj A v 1

theorem dockH_qCp (H : Fin 2 → ℕ) (v : Fin 2 → ℕ) :
    dockH qCp H v = ![v 0, v 1] := by
  funext i
  fin_cases i
  · exact dockH_slot qCp qCp_inj H v 0
  · exact dockH_slot qCp qCp_inj H v 1

theorem qL_inj : Function.Injective qL := by decide

theorem install_qL (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install qL A v = ![A 0, v 0] := by
  funext i
  fin_cases i
  · exact install_other qL A v 0 (by decide)
  · exact install_slot qL qL_inj A v 0

theorem dockH_qL (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH qL H v = ![H 0, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other qL H v 0 (by decide)
  · exact dockH_slot qL qL_inj H v 0

theorem qPut_inj : Function.Injective qPut := by decide

theorem install_qPut (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install qPut A v = ![A 0, v 0] := by
  funext i
  fin_cases i
  · exact install_other qPut A v 0 (by decide)
  · exact install_slot qPut qPut_inj A v 0

theorem dockH_qPut (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH qPut H v = ![H 0, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other qPut H v 0 (by decide)
  · exact dockH_slot qPut qPut_inj H v 0

noncomputable def qCpD := RecoveryFocus.machine qCp CopyO.machine
noncomputable def qLD := RecoveryFocus.machine qL moveLM
noncomputable def qPutD := RecoveryFocus.machine qPut (putM true)
/-- Copy the record's bits over the register's front, step back, restore the marker (tapes: 0 source, 1 register). -/
noncomputable def padInnerRaw := Composition.machine qCpD (Composition.machine qLD qPutD)
/-- The same with the register head returned to cell `0` (log on tape 2). -/
noncomputable def padInnerM := MaskedReset.machine padInnerRaw ![false, true]

theorem pad_inner (pre bits tail X : List Bool) (cap : ℕ) (hcap : 2 * bits.length + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step padInnerM (2 * (2 * bits.length + 1 + 1 + (1 + 1 + 1)) + 2) ![pre.length, 0, 0]
      ![pre ++ frame bits ++ tail, X, List.replicate cap false] ![pre.length + 2 * bits.length, 0, 0]
      ![pre ++ frame bits ++ tail, writeTapeBit (overlay (frame bits) X) (2 * bits.length) true,
        List.replicate cap false] := by
  have c := copyStep pre bits tail [] X
  have hX : overlay [] X = X := by simp [overlay]
  simp only [List.nil_append, List.length_nil, Nat.zero_add, hX] at c
  have d1 := dockRun c qCp qCp_inj ![pre.length, 0] ![pre ++ frame bits ++ tail, X] (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_qCp, dockH_qCp] at d1
  have d2 := dockRun (moveLStep (overlay (frame bits) X) (2 * bits.length)) qL qL_inj
    ![pre.length + 2 * bits.length, 2 * bits.length + 1] ![pre ++ frame bits ++ tail, overlay (frame bits) X]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qL, dockH_qL] at d2
  have d3 := dockRun (putStep true (overlay (frame bits) X) (2 * bits.length)) qPut qPut_inj
    ![pre.length + 2 * bits.length, 2 * bits.length] ![pre ++ frame bits ++ tail, overlay (frame bits) X]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qPut, dockH_qPut] at d3
  have d1' := d1.congr (hout' := ![pre.length + 2 * bits.length, 2 * bits.length + 1])
    (tout' := ![pre ++ frame bits ++ tail, overlay (frame bits) X]) (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)
  have d2' := d2.congr (hout' := ![pre.length + 2 * bits.length, 2 * bits.length])
    (tout' := ![pre ++ frame bits ++ tail, overlay (frame bits) X]) (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)
  have d3' := d3.congr (hout' := ![pre.length + 2 * bits.length, 2 * bits.length + 1])
    (tout' := ![pre ++ frame bits ++ tail, writeTapeBit (overlay (frame bits) X) (2 * bits.length) true])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have j := d1'.seq (d2'.seq d3')
  have hm := j.mask ![false, true] (by intro i hi; fin_cases i <;> simp_all) (cap := cap) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

noncomputable def pZD := RecoveryFocus.machine pZ regCopyM
noncomputable def pMvD := RecoveryFocus.machine pMv moveM
noncomputable def pInnerD := RecoveryFocus.machine pInner padInnerM
/-- **Load a stacked record at width `W`** (tapes: 0 stack, 1 template, 2 register, 3 log). -/
noncomputable def padLoadM :=
  Composition.machine pZD (Composition.machine pMvD (Composition.machine pMvD (Composition.machine pInnerD pMvD)))

/-- The cost of one padded load. -/
def padCost (W L : ℕ) : ℕ :=
  (2 * (2 * W + 1) + 2) + 1 + (1 + 1 + (1 + 1 + ((2 * (2 * L + 1 + 1 + (1 + 1 + 1)) + 2) + 1 + 1)))

/-- **A stacked record as a `W`-bit register**: from the record `true :: bits` (`|bits| < W`) the register becomes
`overlay (frame (binary W (value bits))) Y`; the stack head steps to the next record. -/
theorem pad_load (W : ℕ) (pre bits tail tz Y : List Bool) (cap : ℕ) (hL : bits.length < W)
    (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * bits.length + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step padLoadM (padCost W bits.length) ![pre.length, 0, 0, 0]
      ![pre ++ frame (true :: bits) ++ tail, frame (List.replicate W false) ++ tz, Y, List.replicate cap false]
      ![pre.length + (2 * (bits.length + 1) + 1), 0, 0, 0]
      ![pre ++ frame (true :: bits) ++ tail, frame (List.replicate W false) ++ tz, overlay (frame (binary W (value bits))) Y,
        List.replicate cap false] := by
  set SRC := pre ++ frame (true :: bits) ++ tail
  set TZ := frame (List.replicate W false) ++ tz
  have a := dockRun (regCopyStep (List.replicate W false) tz Y cap (by simpa using hcap1)) pZ pZ_inj
    ![pre.length, 0, 0, 0] ![SRC, TZ, Y, List.replicate cap false] (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_pZ, dockH_pZ, List.length_replicate] at a
  set R1 := overlay (frame (List.replicate W false)) Y
  have a' : Step pZD (2 * (2 * W + 1) + 2) ![pre.length, 0, 0, 0] ![SRC, TZ, Y, List.replicate cap false]
      ![pre.length, 0, 0, 0] ![SRC, TZ, R1, List.replicate cap false] :=
    a.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have mv : ∀ s : ℕ, Step pMvD 1 ![s, 0, 0, 0] ![SRC, TZ, R1, List.replicate cap false] ![s + 1, 0, 0, 0]
      ![SRC, TZ, R1, List.replicate cap false] := by
    intro s
    have e := dockRun (moveStep SRC s) pMv pMv_inj ![s, 0, 0, 0] ![SRC, TZ, R1, List.replicate cap false]
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [install_pMv, dockH_pMv] at e
    exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have hS : SRC = (pre ++ [true, true]) ++ frame bits ++ tail := by simp [SRC, frame, List.append_assoc]
  have ip := pad_inner (pre ++ [true, true]) bits tail R1 cap hcap2
  rw [← hS] at ip
  have di := dockRun ip pInner pInner_inj ![pre.length + 1 + 1, 0, 0, 0] ![SRC, TZ, R1, List.replicate cap false]
    (by intro k; fin_cases k <;> simp [pInner]) (by intro k; fin_cases k <;> rfl)
  rw [install_pInner, dockH_pInner, pad_write bits Y W hL] at di
  set R2 := overlay (frame (binary W (value bits))) Y
  have di' : Step pInnerD (2 * (2 * bits.length + 1 + 1 + (1 + 1 + 1)) + 2) ![pre.length + 1 + 1, 0, 0, 0]
      ![SRC, TZ, R1, List.replicate cap false] ![pre.length + 2 + 2 * bits.length, 0, 0, 0]
      ![SRC, TZ, R2, List.replicate cap false] :=
    di.congr (by funext i; fin_cases i <;> simp) (by funext i; fin_cases i <;> rfl)
  have mv2 := dockRun (moveStep SRC (pre.length + 2 + 2 * bits.length)) pMv pMv_inj
    ![pre.length + 2 + 2 * bits.length, 0, 0, 0] ![SRC, TZ, R2, List.replicate cap false]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_pMv, dockH_pMv] at mv2
  have mv2' : Step pMvD 1 ![pre.length + 2 + 2 * bits.length, 0, 0, 0] ![SRC, TZ, R2, List.replicate cap false]
      ![pre.length + (2 * (bits.length + 1) + 1), 0, 0, 0] ![SRC, TZ, R2, List.replicate cap false] :=
    mv2.congr (by funext i; fin_cases i <;> simp; omega) (by funext i; fin_cases i <;> rfl)
  have j := a'.seq ((mv pre.length).seq ((mv (pre.length + 1)).seq (di'.seq mv2')))
  unfold padCost
  exact j

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
