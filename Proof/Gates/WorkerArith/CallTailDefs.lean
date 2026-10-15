import Proof.Gates.WorkerArith.CtrCall
import Proof.Gates.WorkerArith.VerdictVal
import Proof.Gates.Codec.PairFrame

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord)

variable {ns nr : ℕ}

/-! ## Blanking a framed word -/

/-- Blank `X = frame u` (head `0`) with the guard `G` (registers `K T RG R` scratch). -/
def clearFrameP (X G : Fin (ns + 1)) (K T RG R : Fin nr) : WMX ns nr :=
  .seq (guardP X G K T RG) (.seq (.wm (WM.rewind G RG)) (.seq (clearOne X G R) (clearSelfP G R)))

/-- **STATEMENT `clearFrame_ideal`.** -/
def ClearFrameIdeal (cap : ℕ) (X G : Fin (ns + 1)) (K T RG R : Fin nr) (u : List Bool) (σ : WState ns nr) : Prop :=
  X ≠ G → [K, T, RG, R].Nodup →
  σ.st X = frame u → σ.sh X = 0 → Worker.Blank (σ.st G) → σ.sh G = 0 →
  σ.val K = 0 → σ.val T = 0 → σ.val RG = 0 → σ.val R = 0 → 2 * u.length + 2 ≤ cap →
  ∃ τ, WXExec cap (clearFrameP X G K T RG R) σ τ (150 * (u.length + 1)) ∧ SimW ((σ.sets X []).sets G []) τ

/-! ## The call tail -/

/-- Append `marks (bitWord [F ≠ 0])`. -/
def flipW (o : Fin (ns + 1)) (OP F : Fin nr) : WMX ns nr :=
  .ifr F (.wm (Codec.emitMarks o OP (bitWord true))) (.wm (Codec.emitMarks o OP (bitWord false)))

/-- The six natWords of an interval word. -/
def outN (v : ℚ × ℚ) : List ℕ := ratN v.1 ++ ratN v.2

def tailFrontW (S1 S2 S3 WT : Fin (ns + 1)) (P : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (Codec.fieldFrameW WT S2 (P 2) (P 7))
  (.seq (Codec.dupR (P 2) (P 4) (P 6))
  (.seq (WM.rewind S2 (P 4))
  (.seq (Codec.dupR (P 2) (P 4) (P 6))
  (.seq (Codec.dupR (P 1) (P 3) (P 6))
  (.seq (Codec.pairFrame S1 S2 S3 (P 5) (P 1) (P 2))
  (.seq (WM.rewind S3 (P 5))
  (.seq (WM.rewind S1 (P 3)) (WM.rewind S2 (P 4)))))))))

/-- **The call tail.** Registers: `Rg` = `ctrCallP`'s file (`Rg 7` = the I-stream's output position); `P 0` the
flip (kept), `P 1` = `|frame (callWord c)|` (consumed), `P 2 … P 7` scratch. -/
noncomputable def callTailP {B1 B2 : ℕ} (ctr : Counter B1 B2) (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1))
    (S1 S2 TL G L VI WT : Fin (ns + 1)) (Rg P : Fin 8 ↪ Fin nr) : WMX ns nr :=
  .seq (.wm (tailFrontW S1 S2 (tmap (inTape ctr.program.program)) WT P))
  (.seq (flipW VI (Rg 7) (P 0))
  (.seq (ctrCallP ctr.program.program 6 tmap TL G L VI Rg)
  (.seq (clearFrameP S1 G (Rg 3) (Rg 4) (Rg 5) (Rg 0))
  (clearFrameP S2 G (Rg 3) (Rg 4) (Rg 5) (Rg 0)))))

open Classical in
/-- The ideal end state of the call tail. -/
noncomputable def tailIdeal {t : ℕ} (σ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (S1 S2 TL G VI WT : Fin (ns + 1))
    (OP KA : Fin nr) (hWT : ℕ) (entry : List Bool) : WState ns nr :=
  (appendO ⟨fun i => if (∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S1 ∨ i = S2 then 0 else
      if i = WT then hWT else σ.sh i,
    fun i => if (∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S1 ∨ i = S2 then [] else σ.st i, σ.val, σ.cell⟩
    VI OP (marks entry)).setv KA 0

/-- The cost class of one call tail. -/
def tailCost (t cw w b : ℕ) : ℕ := (300 * t + 6000) * (cw + w + b + 1)

def CallTailIdeal {B1 B2 : ℕ} (ctr : Counter B1 B2) (c : Call) (w : List Bool) (cap : ℕ)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) (S1 S2 TL G L VI WT : Fin (ns + 1))
    (Rg P : Fin 8 ↪ Fin nr) (pre rest : List Bool) (σ : WState ns nr) : Prop :=
  Function.Injective tmap → (∀ j, tmap j ≠ S1) → (∀ j, tmap j ≠ S2) → (∀ j, tmap j ≠ TL) → (∀ j, tmap j ≠ G) →
  (∀ j, tmap j ≠ L) → (∀ j, tmap j ≠ VI) → (∀ j, tmap j ≠ WT) → [S1, S2, TL, G, L, VI, WT].Nodup →
  (∀ i k, P i ≠ Rg k) →
  σ.st S1 = frame (callWord c) → σ.sh S1 = 0 → σ.val (P 1) = (frame (callWord c)).length →
  Worker.Blank (σ.st S2) → σ.sh S2 = 0 →
  (∀ j, Worker.Blank (σ.st (tmap j))) → (∀ j, σ.sh (tmap j) = 0) →
  Worker.Blank (σ.st TL) → σ.sh TL = 0 → Worker.Blank (σ.st G) → σ.sh G = 0 →
  Worker.Blank (σ.st L) → σ.sh L = 0 →
  σ.st WT = pre ++ (Worker.Format.countWord w.length ++ w) ++ rest → σ.sh WT = pre.length →
  σ.sh VI = (σ.st VI).length →
  (∀ i : Fin 8, i ≠ 7 → σ.val (Rg i) = 0) → (∀ i : Fin 8, 2 ≤ i.val → σ.val (P i) = 0) →
  σ.val (Rg 7) + 8 * ((callWord c).length + w.length + ctr.budget c w) + 60 ≤ cap →
  ∃ τ, WXExec cap (callTailP ctr tmap S1 S2 TL G L VI WT Rg P) σ τ
      (tailCost ctr.program.program.tapeCount (callWord c).length w.length (ctr.budget c w)) ∧
    SimW (tailIdeal σ tmap S1 S2 TL G VI WT (Rg 7) (P 1) (pre.length + w.length + 1 + w.length)
      (bitWord (decide (σ.val (P 0) ≠ 0)) ++ outputWord (ctr.value c w))) τ

end NearCubicGates.Close.WorkerArith
