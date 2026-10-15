import Proof.Wire_3_5.PrimAsmShellXRun
import Proof.Wire_3_5.PrimAsmThrDataIface

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Shell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm

/-- **The THR data stage's size hypotheses at width `V`** (`ThrData.ThrDataStage.run`'s, with `L = W = V`). -/
structure ThrDataOK {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (V : ℕ) : Prop where
  ha1 : 1 ≤ a'
  ha : a' ≤ 4
  hk : carriers.length ≤ 2
  hL : ∀ i, (Cs i).descriptionBits ≤ V
  hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ V
  h2 : 2 ≤ n + V
  hcN : natBitLength n + 1 ≤ 2 * V + 2
  hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2
  hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * V + 2
  hcx : ∀ y ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2
  hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2
  hcu : 2 * (Data.unaryList (ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * V + 2

/-! ## The machines -/

noncomputable def M8T (S : ThrData.ThrDataStage) (x D D1 D2 : ℕ) :=
  RecoveryFocus.machine (dataSlots x D D1 D2) S.M

/-- The boot and the THR data phase (`ShellD.preM` with `M8T`). -/
noncomputable def preMT (S : ThrData.ThrDataStage) (x D D1 D2 C1 C2 : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (bootM x D D1 D2 C1) (M6 x D D1 D2 C2))
    (M7 x D D1 D2)) (M8T S x D D1 D2)

/-- The THR pre-phase, docked on ShellX's layout (`ShellX.MX0` with `preMT`). -/
noncomputable def MX0T (S : ThrData.ThrDataStage) (x D D2 Dv DL C2 : ℕ) :=
  RecoveryFocus.machine (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) (preMT S x D 0 D2 0 C2)

/-- **The THR boot** (`ShellX.bootXM` with `MX0T`). -/
noncomputable def bootXMT (S : ThrData.ThrDataStage) (x D D2 Dv DL C2 Cv cr CL : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (MX0T S x D D2 Dv DL C2) (MX1 x D D2 Dv DL Cv)) (MX2 x D D2 Dv DL cr)) (MX3 x D D2 Dv DL))
    (MX4 x D D2 Dv DL CL)) (MX5 x D D2 Dv DL)) (act6 x D D2 Dv DL).compile

/-- **The loop body for any unit machine** `U` on the cell layout: the copy-in, then `U` (`CellLoopD.bodyD` with `U`
in place of `unitM W decW`). -/
noncomputable def bodyU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (e : ℕ) :=
  Composition.machine (cpM x e) (TapeEmbedding.machine e (TapeEmbedding.machine 1 U))

/-- The unit loop with the data tape on ShellX's layout (`ShellX.loopEX` with `bodyU`). -/
noncomputable def loopEU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (D D2 Dv DL : ℕ) :=
  TapeEmbedding.machine (EX x D D2 Dv DL) (TapeEmbedding.machine (E1 0 + E2 D2 + E3)
    (CloseoutRowsDegreeLoop.machine (Scrub.machine (bodyU x U (Scrub.wk D)) (scrResetD x (Scrub.wk D))
      (scrSD x (Scrub.wk D)))))

/-- The THR writer before its teardown. -/
noncomputable def innerMT (S : ThrData.ThrDataStage) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv cr DL CL : ℕ) :=
  Composition.machine (Composition.machine (bootXMT S x D D2 Dv DL C2 Cv cr CL) (entryEX x D D2 Dv DL C))
    (loopEU x U D D2 Dv DL)

/-- **The THR shell's machine**: the writer under one masked reset. One machine per data stage, unit machine and
`(D, C, D₂, C₂, Dv, Cv, c_r, DL, CL)`, independent of the request. -/
noncomputable def shellMT (S : ThrData.ThrDataStage) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv cr DL CL : ℕ) :=
  MaskedReset.machine (innerMT S x U D C D2 C2 Dv Cv cr DL CL) (fun _ => true)

/-- **The THR shell as a `WriterStage`** (ShellX's ports). -/
noncomputable def shellStageT (S : ThrData.ThrDataStage) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv cr DL CL : ℕ) : WriterIface.WriterStage :=
  ⟨STx x D D2 Dv DL + 1, _, shellMT S x U D C D2 C2 Dv Cv cr DL CL, shellInX x D D2 Dv DL, shellOutX x D D2 Dv DL,
    shellInX_ne_out⟩

/-! ## The per-unit hypothesis and the run type -/

/-- **One unit of the loop** (`cap` the cell encoding's capacity, `u` the data tape's counts): from the unit's entry
`blankCellD x w out j u` (request `frame w` on stream `0`, head `0`; `out ++ [false]` on stream `1`, head `|out|`;
`1^j` on stream `2`, head `0`; `u` on stream `113`, head `0`; every other stream empty, every register `0`), the unit
machine `U` halts at a cell state with the request kept on stream `0`, `out ++ emit j ++ [false]` on stream `1` with
its head at `|out ++ emit j|`, and `1^(j+1)` on stream `2`, in `mU` steps with `cpCost |u| + 1 + mU ≤ nU`. -/
def UnitOK (cap x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (nU : ℕ) (w u : List Bool) (emit : ℕ → List Bool) (j : ℕ)
    (out : List Bool) : Prop :=
  ∃ (σE : WState (LNS x) LNR) (mU : ℕ),
    Step U mU (wenc cap (blankCellD x w out j u)).H (wenc cap (blankCellD x w out j u)).A (wenc cap σE).H
      (wenc cap σE).A ∧
    σE.st (sk x 0) = frame w ∧ σE.st (sk x 1) = out ++ emit j ++ [false] ∧ σE.sh (sk x 1) = (out ++ emit j).length ∧
    σE.st (sk x 2) = List.replicate (j + 1) true ∧ cpCost u.length + 1 + mU ≤ nU

/-- **The THR shell's run TYPE** (`WriterIfaceJ.WriterRun`): from `inBank (frame w)`, `w` a THR request word
`Data.reqW n true (thrCodes Cs) (carrier codes) tl`, the output tape `(List.range b).flatMap emit ++ [false]`,
`b = CL(n'+1)^DL`, `n' = 2^(mOf P)`, within `Bud`, every head back at `0`, the request kept, residues within `Bud`; for
any unit machine meeting `UnitOK` at every unit `j < b` with the data tape's counts `ThrData.thrCounts Cs carriers`,
scrub capacity `R = C(n'+1)^D`. The data stage's cost enters ShellX's cost formula as its core cost `cc`. -/
def ThrShellRun (S : ThrData.ThrDataStage) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (D C D2 C2 Dv Cv cr DL CL : ℕ) :
    Prop :=
  ∀ (cap nU Bud : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (tl w : List Bool) (emit : ℕ → List Bool) (P : Shared.StarParams),
    P.n = n → P.r = Ledger.rowBr cr P.n →
    w = Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl →
    ThrDataOK Cs carriers (UnaryCalc.value D2 C2 n) →
    2 * n + cr + 16 ≤ UnaryCalc.value Dv Cv n →
    cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P) →
    nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P) →
    bootCost w n 0 0 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P) →
    (∀ j < UnaryCalc.value DL CL (2 ^ NumsX.mOf P), ∀ out : List Bool,
      UnitOK cap x U nU w (Data.unaryList (ThrData.thrCounts Cs carriers)) emit j out) →
    2 * shellCostX w n D C D2 C2 (S.cost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv cr
      (UnaryCalc.value Dv Cv n) (NumsX.mOf P) DL CL nU + 2 ≤ Bud →
    WriterIfaceJ.WriterRun (shellMT S x U D C D2 C2 Dv Cv cr DL CL) Bud (shellInX x D D2 Dv DL)
      (shellOutX x D D2 Dv DL) w ((List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit ++ [false])

/-! ## PA's unit machine docks by `DecOK` -/

/-- **PA's `unitM W decW` meets `UnitOK`** wherever its decode meets `DecOK` (ShellX's `hdec` shape): the HASH writer's
FILTER-only units dock the THR shell unchanged. -/
theorem unitOK_of_dec (cap : ℕ) (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (nU : ℕ) (w u : List Bool)
    (emit : ℕ → List Bool) (j : ℕ) (out : List Bool)
    (h : ∃ σD m Bp, WExec cap decW (blankCellD W.x w out j u) σD m ∧ DecOK cap W σD out (emit j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      cpCost u.length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU) :
    UnitOK cap W.x (unitM W decW) nU w u emit j out := by
  obtain ⟨σD, m, Bp, hd, hok, hIN, hC, hCh, hn⟩ := h
  obtain ⟨σE, sU, e0, e1, e1h, e2⟩ :=
    unit_step cap W decW (blankCellD W.x w out j u) σD m j Bp out (emit j) w hd hok hIN hC hCh
  exact ⟨σE, _, sU, e0, e1, e1h, e2, hn⟩

end NearCubicWires.WireExponent3_5.PrimThrW.Shell
