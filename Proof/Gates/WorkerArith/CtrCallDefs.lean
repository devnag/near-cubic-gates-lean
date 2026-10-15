import Proof.Gates.Worker.CounterDock
import Proof.Gates.Codec.Emit

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.RepairSource.OrdinaryOracleCompose

variable {ns nr : ℕ}

/-- The input tape (index `0`) of a program. -/
def inTape (p : Program) : Fin p.tapeCount := ⟨0, by have := p.twoTapes; omega⟩

/-- Two ones on `G` (register `RG` counts). -/
def twoOnes (G : Fin (ns + 1)) (RG : Fin nr) : WMX ns nr :=
  .seq (WMX.wr G true) (.seq (WMX.fwd G) (.seq (WMX.wr G true) (.seq (WMX.fwd G) (.seq (WMX.inc RG) (WMX.inc RG)))))

/-- Step 1: `G := 1^{2|w| + 2}` from `frame w` on `X` (`K`, `T` width registers, `RG` the length of `G`). -/
def guardP (X G : Fin (ns + 1)) (K T RG : Fin nr) : WMX ns nr :=
  .seq (BinW.width X K T) (.seq (.whr K (.seq (WMX.dec K) (twoOnes G RG))) (twoOnes G RG))

/-- Step 3: copy `k` raw natWords from `O` to `VI` as marks. -/
def copyK (O VI : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (Codec.copyNat false O VI R) (copyK O VI R k)

/-- Step 4: append the tally `TL = 1^s` to `G`, then rewind both. -/
def tallyP (TL G : Fin (ns + 1)) (RG RT : Fin nr) : WMX ns nr :=
  .seq (.whs TL (.seq (WMX.wr G true) (.seq (WMX.fwd G) (.seq (WMX.inc RG) (.seq (WMX.fwd TL) (WMX.inc RT))))))
    (.seq (.wm (WM.rewind TL RT)) (.wm (WM.rewind G RG)))

/-- Step 5a: walk `O` back to `0` writing `false`, `|G|` times (`G = 1^m` drives; `R` counts). -/
def clearBackP (O G : Fin (ns + 1)) (R : Fin nr) : WMX ns nr :=
  .seq (.whs G (.seq (WMX.wr O false) (.seq (WMX.bwd O) (.seq (WMX.fwd G) (WMX.inc R)))))
    (.whr R (.seq (WMX.bwd G) (WMX.dec R)))

/-- Step 5b: `clearOne` on a list of streams. -/
def clearAll (G : Fin (ns + 1)) (R : Fin nr) : List (Fin (ns + 1)) → WMX ns nr
  | [] => WMX.skip
  | X :: l => .seq (clearOne X G R) (clearAll G R l)

/-- Step 5d: blank the guard itself. -/
def clearSelfP (G : Fin (ns + 1)) (R : Fin nr) : WMX ns nr :=
  .seq (.whs G (.seq (WMX.wr G false) (.seq (WMX.fwd G) (WMX.inc R)))) (.whr R (.seq (WMX.bwd G) (WMX.dec R)))

/-- **The clocked counter call.** Registers: `Rg 0` clear counter, `Rg 1`, `Rg 2` copy scratch, `Rg 3`, `Rg 4` width,
`Rg 5` the guard length, `Rg 6` the tally length, `Rg 7` the output position of `VI`. -/
noncomputable def ctrCallP (p : Program) (k : ℕ) (tmap : Fin p.tapeCount → Fin (ns + 1)) (TL G L VI : Fin (ns + 1))
    (Rg : Fin 8 ↪ Fin nr) : WMX ns nr :=
  .seq (guardP (tmap (inTape p)) G (Rg 3) (Rg 4) (Rg 5))
    (.seq (WMX.machZ (clockMachine p.machine) (Fin.addCases (motive := fun _ => Fin (ns + 1)) tmap
      (fun _ : Fin 1 => TL)) L)
    (.seq (.wm (copyK (tmap p.outputTape) VI Rg k))
    (.seq (tallyP TL G (Rg 5) (Rg 6))
    (.seq (clearBackP (tmap p.outputTape) G (Rg 0))
    (.seq (clearAll G (Rg 0) ((List.finRange p.tapeCount).map tmap))
    (.seq (clearOne TL G (Rg 0)) (clearSelfP G (Rg 0))))))))

open Classical in
/-- The ideal state after the call: `VI` gained `marks out`; the counter's streams, `TL` and `G` are empty at head
`0`; everything else (registers but the output position, the cell, the log) as before. -/
noncomputable def ctrIdeal {t : ℕ} (σ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (TL G VI : Fin (ns + 1))
    (OP : Fin nr) (out : List Bool) : WState ns nr :=
  appendO ⟨fun i => if (∃ j, tmap j = i) ∨ i = TL ∨ i = G then 0 else σ.sh i,
    fun i => if (∃ j, tmap j = i) ∨ i = TL ∨ i = G then [] else σ.st i, σ.val, σ.cell⟩ VI OP (marks out)

/-- The cost class of one call (`t` tapes). -/
def ctrCost (t inLen budget outLen : ℕ) : ℕ := (60 * t + 600) * (inLen + budget + outLen + 1)

def CtrCallIdeal {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (outN : List ℕ) (cap : ℕ)
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (TL G L VI : Fin (ns + 1)) (Rg : Fin 8 ↪ Fin nr)
    (σ : WState ns nr) : Prop :=
  output req = outN.flatMap natWord →
  Function.Injective tmap → (∀ j, tmap j ≠ TL) → (∀ j, tmap j ≠ G) → (∀ j, tmap j ≠ L) → (∀ j, tmap j ≠ VI) →
  [TL, G, L, VI].Nodup →
  σ.st (tmap (inTape f.program)) = RepairOrdinary.frame (input req) →
  (∀ j, j ≠ inTape f.program → Worker.Blank (σ.st (tmap j))) → (∀ j, σ.sh (tmap j) = 0) →
  Worker.Blank (σ.st TL) → σ.sh TL = 0 → Worker.Blank (σ.st G) → σ.sh G = 0 →
  Worker.Blank (σ.st L) → σ.sh L = 0 → σ.sh VI = (σ.st VI).length →
  (∀ i : Fin 8, i ≠ 7 → σ.val (Rg i) = 0) →
  σ.val (Rg 7) + 2 * (output req).length + 4 * (input req).length + budget req + 20 ≤ cap →
  ∃ τ, WXExec cap (ctrCallP f.program outN.length tmap TL G L VI Rg) σ τ
      (ctrCost f.program.tapeCount (input req).length (budget req) (output req).length) ∧
    SimW (ctrIdeal σ tmap TL G VI (Rg 7) (output req)) τ

end NearCubicGates.Close.WorkerArith
