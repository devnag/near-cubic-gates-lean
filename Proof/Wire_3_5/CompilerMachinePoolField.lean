import Proof.Wire_3_5.CompilerMachinePoolConv

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Primitive steps -/

/-- One move to the right. -/
def moveM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem moveStep (T : List Bool) (h : ℕ) : Step moveM 1 ![h] ![T] ![h + 1] ![T] := by
  have hs : step moveM ⟨moveM.start, ![h], ![T]⟩ = some ⟨1, ![h + 1], ![T]⟩ := by
    simp [step, moveM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := moveM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-- Copy one register into another, both heads back at cell `0` (log on tape 2). -/
noncomputable def regCopyM := MaskedReset.machine CopyO.machine ![true, true]

theorem regCopyStep (w tail Y : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step regCopyM (2 * (2 * w.length + 1) + 2) ![0, 0, 0] ![frame w ++ tail, Y, List.replicate cap false]
      ![0, 0, 0] ![frame w ++ tail, overlay (frame w) Y, List.replicate cap false] := by
  have h0 := copyStep [] w tail [] Y
  have hY : overlay [] Y = Y := by simp [overlay]
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h0
  rw [hY] at h0
  have hm := h0.mask ![true, true] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- Emit a register with a stale suffix onto a stream cursor (register head back at `0`; log on tape 2). -/
theorem emitT (w tail out BW : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step emitM (2 * (2 * w.length + 1) + 2) ![0, out.length, 0]
      ![frame w ++ tail, overlay out BW, List.replicate cap false] ![0, out.length + (2 * w.length + 1), 0]
      ![frame w ++ tail, overlay (out ++ frame w) BW, List.replicate cap false] := by
  have h0 := copyStep [] w tail out BW
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h0
  have hm := h0.mask ![true, false] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

theorem overlay_frame (w Y : List Bool) : overlay (frame w) Y = frame w ++ Y.drop (frame w).length := rfl

/-! ## The field machine (tapes: 0 source, 1 counter, 2 magnitude, 3 zero, 4 output, 5 log) -/

def fMove : Fin 1 → Fin 6 := ![0]
def fClear : Fin 3 → Fin 6 := ![3, 2, 5]
def fConv : Fin 4 → Fin 6 := ![0, 1, 2, 5]
def fEmitM : Fin 3 → Fin 6 := ![2, 4, 5]
def fEmitZ : Fin 3 → Fin 6 := ![3, 4, 5]

theorem fMove_inj : Function.Injective fMove := by decide

theorem install_fMove (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    install fMove A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i
  fin_cases i
  · exact install_slot fMove fMove_inj A v 0
  · exact install_other fMove A v 1 (by decide)
  · exact install_other fMove A v 2 (by decide)
  · exact install_other fMove A v 3 (by decide)
  · exact install_other fMove A v 4 (by decide)
  · exact install_other fMove A v 5 (by decide)

theorem dockH_fMove (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH fMove H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i
  fin_cases i
  · exact dockH_slot fMove fMove_inj H v 0
  · exact dockH_other fMove H v 1 (by decide)
  · exact dockH_other fMove H v 2 (by decide)
  · exact dockH_other fMove H v 3 (by decide)
  · exact dockH_other fMove H v 4 (by decide)
  · exact dockH_other fMove H v 5 (by decide)

theorem fClear_inj : Function.Injective fClear := by decide

theorem install_fClear (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    install fClear A v = ![A 0, A 1, v 1, v 0, A 4, v 2] := by
  funext i
  fin_cases i
  · exact install_other fClear A v 0 (by decide)
  · exact install_other fClear A v 1 (by decide)
  · exact install_slot fClear fClear_inj A v 1
  · exact install_slot fClear fClear_inj A v 0
  · exact install_other fClear A v 4 (by decide)
  · exact install_slot fClear fClear_inj A v 2

theorem dockH_fClear (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH fClear H v = ![H 0, H 1, v 1, v 0, H 4, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other fClear H v 0 (by decide)
  · exact dockH_other fClear H v 1 (by decide)
  · exact dockH_slot fClear fClear_inj H v 1
  · exact dockH_slot fClear fClear_inj H v 0
  · exact dockH_other fClear H v 4 (by decide)
  · exact dockH_slot fClear fClear_inj H v 2

theorem fConv_inj : Function.Injective fConv := by decide

theorem install_fConv (A : Fin 6 → List Bool) (v : Fin 4 → List Bool) :
    install fConv A v = ![v 0, v 1, v 2, A 3, A 4, v 3] := by
  funext i
  fin_cases i
  · exact install_slot fConv fConv_inj A v 0
  · exact install_slot fConv fConv_inj A v 1
  · exact install_slot fConv fConv_inj A v 2
  · exact install_other fConv A v 3 (by decide)
  · exact install_other fConv A v 4 (by decide)
  · exact install_slot fConv fConv_inj A v 3

theorem dockH_fConv (H : Fin 6 → ℕ) (v : Fin 4 → ℕ) :
    dockH fConv H v = ![v 0, v 1, v 2, H 3, H 4, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot fConv fConv_inj H v 0
  · exact dockH_slot fConv fConv_inj H v 1
  · exact dockH_slot fConv fConv_inj H v 2
  · exact dockH_other fConv H v 3 (by decide)
  · exact dockH_other fConv H v 4 (by decide)
  · exact dockH_slot fConv fConv_inj H v 3

theorem fEmitM_inj : Function.Injective fEmitM := by decide

theorem install_fEmitM (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    install fEmitM A v = ![A 0, A 1, v 0, A 3, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_other fEmitM A v 0 (by decide)
  · exact install_other fEmitM A v 1 (by decide)
  · exact install_slot fEmitM fEmitM_inj A v 0
  · exact install_other fEmitM A v 3 (by decide)
  · exact install_slot fEmitM fEmitM_inj A v 1
  · exact install_slot fEmitM fEmitM_inj A v 2

theorem dockH_fEmitM (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH fEmitM H v = ![H 0, H 1, v 0, H 3, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other fEmitM H v 0 (by decide)
  · exact dockH_other fEmitM H v 1 (by decide)
  · exact dockH_slot fEmitM fEmitM_inj H v 0
  · exact dockH_other fEmitM H v 3 (by decide)
  · exact dockH_slot fEmitM fEmitM_inj H v 1
  · exact dockH_slot fEmitM fEmitM_inj H v 2

theorem fEmitZ_inj : Function.Injective fEmitZ := by decide

theorem install_fEmitZ (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    install fEmitZ A v = ![A 0, A 1, A 2, v 0, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_other fEmitZ A v 0 (by decide)
  · exact install_other fEmitZ A v 1 (by decide)
  · exact install_other fEmitZ A v 2 (by decide)
  · exact install_slot fEmitZ fEmitZ_inj A v 0
  · exact install_slot fEmitZ fEmitZ_inj A v 1
  · exact install_slot fEmitZ fEmitZ_inj A v 2

theorem dockH_fEmitZ (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH fEmitZ H v = ![H 0, H 1, H 2, v 0, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other fEmitZ H v 0 (by decide)
  · exact dockH_other fEmitZ H v 1 (by decide)
  · exact dockH_other fEmitZ H v 2 (by decide)
  · exact dockH_slot fEmitZ fEmitZ_inj H v 0
  · exact dockH_slot fEmitZ fEmitZ_inj H v 1
  · exact dockH_slot fEmitZ fEmitZ_inj H v 2

noncomputable def fMoveD := RecoveryFocus.machine fMove moveM
noncomputable def fClearD := RecoveryFocus.machine fClear regCopyM
noncomputable def fConvD := RecoveryFocus.machine fConv convR
noncomputable def fEmitMD := RecoveryFocus.machine fEmitM emitM
noncomputable def fEmitZD := RecoveryFocus.machine fEmitZ emitM
/-- Step over the sign, clear the magnitude register, convert the magnitude. -/
noncomputable def fieldPre := Composition.machine fMoveD (Composition.machine fClearD fConvD)
noncomputable def fieldPos := Composition.machine fieldPre (Composition.machine fEmitMD fEmitZD)
noncomputable def fieldNeg := Composition.machine fieldPre (Composition.machine fEmitZD fEmitMD)
/-- **One native field as a P/N pair**: negative coefficients emit the zero register first. -/
noncomputable def fieldM := branchM 0 fieldNeg fieldPos

/-- The field machine's heads. -/
def fH (s o : ℕ) : Fin 6 → ℕ := ![s, 0, 0, 0, o, 0]

/-- The field machine's tapes. -/
def fA (S K M Z O LG : List Bool) : Fin 6 → List Bool := ![S, K, M, Z, O, LG]

theorem fs_move (s o : ℕ) (S K M Z O LG : List Bool) :
    Step fMoveD 1 (fH s o) (fA S K M Z O LG) (fH (s + 1) o) (fA S K M Z O LG) := by
  have e := dockRun (moveStep S s) fMove fMove_inj (fH s o) (fA S K M Z O LG) (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; rfl)
  rw [install_fMove, dockH_fMove] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem fs_clear (s o : ℕ) (S K M w t O : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step fClearD (2 * (2 * w.length + 1) + 2) (fH s o) (fA S K M (frame w ++ t) O (List.replicate cap false))
      (fH s o) (fA S K (overlay (frame w) M) (frame w ++ t) O (List.replicate cap false)) := by
  have e := dockRun (regCopyStep w t M cap hcap) fClear fClear_inj (fH s o)
    (fA S K M (frame w ++ t) O (List.replicate cap false)) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_fClear, dockH_fClear] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem fs_conv (h v : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) (pre post Y Z O : List Bool) (o capK cap : ℕ)
    (hK : natBitLength v ≤ capK) (hc : convCost v ≤ cap) :
    Step fConvD (2 * convCost v + 2) (fH pre.length o)
      (fA (pre ++ natWord v ++ post) (false :: List.replicate capK true) (overlay (frame (binary h 0)) Y) Z O
        (List.replicate cap false))
      (fH (pre.length + (natWord v).length) o)
      (fA (pre ++ natWord v ++ post) (false :: List.replicate capK true) (overlay (frame (binary h v)) Y) Z O
        (List.replicate cap false)) := by
  have e := dockRun (convR_run h v h1 hv pre post Y capK cap hK hc) fConv fConv_inj (fH pre.length o)
    (fA (pre ++ natWord v ++ post) (false :: List.replicate capK true) (overlay (frame (binary h 0)) Y) Z O
      (List.replicate cap false)) (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_fConv, dockH_fConv] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem fs_emitM (s : ℕ) (S K w t Z out BW : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step fEmitMD (2 * (2 * w.length + 1) + 2) (fH s out.length)
      (fA S K (frame w ++ t) Z (overlay out BW) (List.replicate cap false))
      (fH s (out ++ frame w).length) (fA S K (frame w ++ t) Z (overlay (out ++ frame w) BW) (List.replicate cap false)) := by
  have e := dockRun (emitT w t out BW cap hcap) fEmitM fEmitM_inj (fH s out.length)
    (fA S K (frame w ++ t) Z (overlay out BW) (List.replicate cap false)) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_fEmitM, dockH_fEmitM] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [fH]

theorem fs_emitZ (s : ℕ) (S K M w t out BW : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step fEmitZD (2 * (2 * w.length + 1) + 2) (fH s out.length)
      (fA S K M (frame w ++ t) (overlay out BW) (List.replicate cap false))
      (fH s (out ++ frame w).length) (fA S K M (frame w ++ t) (overlay (out ++ frame w) BW) (List.replicate cap false)) := by
  have e := dockRun (emitT w t out BW cap hcap) fEmitZ fEmitZ_inj (fH s out.length)
    (fA S K M (frame w ++ t) (overlay out BW) (List.replicate cap false)) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_fEmitZ, dockH_fEmitZ] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [fH]

def preCost (h v : ℕ) : ℕ := 1 + 1 + ((2 * (2 * h + 1) + 2) + 1 + (2 * convCost v + 2))
def emitPairCost (h : ℕ) : ℕ := (2 * (2 * h + 1) + 2) + 1 + (2 * (2 * h + 1) + 2)

/-- The cost of one field. -/
def fieldCost (h v : ℕ) : ℕ := preCost h v + 1 + emitPairCost h + 2

theorem field_pre (h v : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) (pre post Y O : List Bool) (s : Bool) (o capK cap : ℕ)
    (hK : natBitLength v ≤ capK) (hc1 : 2 * h + 1 ≤ cap) (hc2 : convCost v ≤ cap) :
    Step fieldPre (preCost h v) (fH pre.length o)
      (fA (pre ++ s :: (natWord v ++ post)) (false :: List.replicate capK true) Y (frame (binary h 0) ++ []) O
        (List.replicate cap false))
      (fH (pre.length + 1 + (natWord v).length) o)
      (fA (pre ++ s :: (natWord v ++ post)) (false :: List.replicate capK true) (overlay (frame (binary h v)) Y)
        (frame (binary h 0) ++ []) O (List.replicate cap false)) := by
  have e1 := fs_move pre.length o (pre ++ s :: (natWord v ++ post)) (false :: List.replicate capK true) Y
    (frame (binary h 0) ++ []) O (List.replicate cap false)
  have e2 := fs_clear (pre.length + 1) o (pre ++ s :: (natWord v ++ post)) (false :: List.replicate capK true) Y
    (binary h 0) [] O cap (by simp; omega)
  have hS : pre ++ s :: (natWord v ++ post) = (pre ++ [s]) ++ natWord v ++ post := by simp
  have e3 := fs_conv h v h1 hv (pre ++ [s]) post Y (frame (binary h 0) ++ []) O o capK cap hK hc2
  rw [← hS, show (pre ++ [s]).length = pre.length + 1 by simp] at e3
  rw [binary_length] at e2
  have j := e1.seq (e2.seq e3)
  exact j

theorem field_run (h : ℕ) (z : ℤ) (h1 : 1 ≤ h) (hz : z.natAbs < 2 ^ h) (pre post Y out BW : List Bool)
    (capK cap : ℕ) (hK : natBitLength z.natAbs ≤ capK) (hc1 : 2 * h + 1 ≤ cap) (hc2 : convCost z.natAbs ≤ cap) :
    Step fieldM (fieldCost h z.natAbs) (fH pre.length out.length)
      (fA (pre ++ intWord z ++ post) (false :: List.replicate capK true) Y (frame (binary h 0) ++ [])
        (overlay out BW) (List.replicate cap false))
      (fH (pre.length + (intWord z).length) (out ++ pairEnc h (pn z)).length)
      (fA (pre ++ intWord z ++ post) (false :: List.replicate capK true) (overlay (frame (binary h z.natAbs)) Y)
        (frame (binary h 0) ++ []) (overlay (out ++ pairEnc h (pn z)) BW) (List.replicate cap false)) := by
  have hS : pre ++ intWord z ++ post = pre ++ decide (z < 0) :: (natWord z.natAbs ++ post) := by
    simp [intWord]
  have hlen : (intWord z).length = 1 + (natWord z.natAbs).length := by simp [intWord]; omega
  have p := field_pre h z.natAbs h1 hz pre post Y (overlay out BW) (decide (z < 0)) out.length capK cap hK hc1 hc2
  have hM : overlay (frame (binary h z.natAbs)) Y = frame (binary h z.natAbs) ++ Y.drop (frame (binary h z.natAbs)).length :=
    rfl
  by_cases hneg : z < 0
  · have ep := fs_emitZ (pre.length + 1 + (natWord z.natAbs).length) (pre ++ decide (z < 0) :: (natWord z.natAbs ++ post))
      (false :: List.replicate capK true) (overlay (frame (binary h z.natAbs)) Y) (binary h 0) [] out BW cap
      (by simp; omega)
    have eq := fs_emitM (pre.length + 1 + (natWord z.natAbs).length) (pre ++ decide (z < 0) :: (natWord z.natAbs ++ post))
      (false :: List.replicate capK true) (binary h z.natAbs) (Y.drop (frame (binary h z.natAbs)).length)
      (frame (binary h 0) ++ []) (out ++ frame (binary h 0)) BW cap (by simp; omega)
    rw [← hM] at eq
    rw [binary_length] at ep eq
    have j := p.seq (ep.seq eq)
    have hp : pairEnc h (pn z) = frame (binary h 0) ++ frame (binary h z.natAbs) := by
      simp only [pairEnc, pn]
      rw [show z.toNat = 0 by omega, show (-z).toNat = z.natAbs by omega]
    have hb : readTapeBit (fA (pre ++ decide (z < 0) :: (natWord z.natAbs ++ post)) (false :: List.replicate capK true) Y
        (frame (binary h 0) ++ []) (overlay out BW) (List.replicate cap false) 0) (fH pre.length out.length 0) = true := by
      have := read_suffix pre (decide (z < 0) :: (natWord z.natAbs ++ post)) 0
      simp only [Nat.add_zero] at this
      simp only [fA, fH, Matrix.cons_val_zero, this]
      simp [readTapeBit, hneg]
    have := branch_true 0 fieldPos j hb
    unfold fieldCost emitPairCost
    rw [hS]
    refine this.congr ?_ ?_
    · rw [hlen, hp]; funext i; fin_cases i <;> simp [fH, Nat.add_assoc]
    · rw [hp, List.append_assoc]
  · have ep := fs_emitM (pre.length + 1 + (natWord z.natAbs).length) (pre ++ decide (z < 0) :: (natWord z.natAbs ++ post))
      (false :: List.replicate capK true) (binary h z.natAbs) (Y.drop (frame (binary h z.natAbs)).length)
      (frame (binary h 0) ++ []) out BW cap (by simp; omega)
    rw [← hM] at ep
    have eq := fs_emitZ (pre.length + 1 + (natWord z.natAbs).length) (pre ++ decide (z < 0) :: (natWord z.natAbs ++ post))
      (false :: List.replicate capK true) (overlay (frame (binary h z.natAbs)) Y) (binary h 0) []
      (out ++ frame (binary h z.natAbs)) BW cap (by simp; omega)
    rw [binary_length] at ep eq
    have j := p.seq (ep.seq eq)
    have hp : pairEnc h (pn z) = frame (binary h z.natAbs) ++ frame (binary h 0) := by
      simp only [pairEnc, pn]
      rw [show z.toNat = z.natAbs by omega, show (-z).toNat = 0 by omega]
    have hb : readTapeBit (fA (pre ++ decide (z < 0) :: (natWord z.natAbs ++ post)) (false :: List.replicate capK true) Y
        (frame (binary h 0) ++ []) (overlay out BW) (List.replicate cap false) 0) (fH pre.length out.length 0) = false := by
      have := read_suffix pre (decide (z < 0) :: (natWord z.natAbs ++ post)) 0
      simp only [Nat.add_zero] at this
      simp only [fA, fH, Matrix.cons_val_zero, this]
      simp [readTapeBit, hneg]
    have := branch_false 0 fieldNeg j hb
    unfold fieldCost emitPairCost
    rw [hS]
    refine this.congr ?_ ?_
    · rw [hlen, hp]; funext i; fin_cases i <;> simp [fH, Nat.add_assoc]
    · rw [hp, List.append_assoc]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
