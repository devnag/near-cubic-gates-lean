import Proof.Wire_3_5.UnionMachineRadSetupB3
import Proof.Wire_3_5.PrimAsmFiltSetupIface2
import Proof.Wire_3_5.PrimAsmCellLoopD
import Proof.Wire_3_5.PrimAsmSymDecBr
import Proof.Wire_3_5.PrimAsmWriterIface
import Proof.Wire_3_5.PrimAsmThrDataIface3

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

/-- The RADIX branch's marker register. -/
def rRadK : Fin LNR := ⟨398, by decide⟩

/-- The FILTER branch's marker register. -/
def rFltK : Fin LNR := ⟨399, by decide⟩

/-- The units per entry of the THR tape: `[true]`, per row `[true]`, the request, `[false]`, then `[false]`. -/
def thrEU (nc : ℕ) : ℕ := (nc + 1) * (0 + 3) + 2

/-- Unit `j` is a request unit (the middle unit of a row) of the first `TOT` units. -/
def IsReqU (TOT nc j : ℕ) : Prop :=
  j < TOT ∧ j % thrEU nc ≠ 0 ∧ j % thrEU nc < thrEU nc - 1 ∧ (j % thrEU nc - 1) % 3 = 1

/-- A request unit's row index `r` (`r < nc`: FILTER, `r = nc`: RADIX). -/
def rowOfU (nc j : ℕ) : ℕ := (j % thrEU nc - 1) / 3

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The star rows per state: `N² = (2^{kh})²`. -/
noncomputable def thrN2 : ℕ := (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2

/-- The call's units: `thrNT · N² · thrEU |carriers|`. -/
noncomputable def thrTOT : ℕ :=
  Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs * thrN2 l F kclk coef A a ha hs *
    thrEU carriers.length

/-- The THR call's request word on the unit's cell (the request, then the fixed hash's bits, framed). -/
noncomputable def thrCallW : List Bool :=
  (thrReq n a' ha' Cs carriers translation).word ++
    frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
      ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))

/-- The THR call's counts on stream `113`: the sixteen numbers, then the carriers' sizes and the tuple's count. -/
noncomputable def thrCallU : List Bool :=
  Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
    (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
      ThrData.thrCounts Cs carriers)

/-- The request unit `(e, r)`'s printed body: row `r` of the THR batch's entry `e = (t, row)`. -/
noncomputable def thrCallUnit (e r _s : ℕ) : List Bool :=
  ((WriterIface.thrGrp (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation
    (e / thrN2 l F kclk coef A a ha hs) (e % thrN2 l F kclk coef A a ha hs)).getD r []).flatMap SymFlat.unitBody

/-- Unit `j`'s state index `t` and star row. -/
noncomputable def stOfU (j : ℕ) : ℕ := j / thrEU carriers.length / thrN2 l F kclk coef A a ha hs
noncomputable def rowOfS (j : ℕ) : ℕ := j / thrEU carriers.length % thrN2 l F kclk coef A a ha hs

structure ThrDecOut (x : ℕ) (cap : ℕ) (σ : WState (LNS x) LNR) (out : List Bool) (j : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
  h0 : σ.sh (sk x 0) = 0
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  rad : ∀ ht : stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs,
    IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j → rowOfU carriers.length j = carriers.length →
    σ.val rRadK ≠ 0 ∧ σ.val rFltK = 0 ∧
    RsIn4 x σ (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (thrCallU l F kclk coef A a ha hs Cs carriers)
      (radVals l F kclk coef A a ha hs Cs carriers
        (Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.1).val
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.2.1.val
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.2.2.val
        (rowOfS l F kclk coef A a ha hs carriers j))
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A
        (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0
        (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a'
  filt : ∀ ht : stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs,
    IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j → rowOfU carriers.length j < carriers.length →
    σ.val rRadK = 0 ∧ σ.val rFltK ≠ 0 ∧
    FiltSetup.FsIn2 x σ (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (thrCallU l F kclk coef A a ha hs Cs carriers)
      ((callInputs l F kclk coef A a ha).filterParams .thr n).len ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp
      (Enum.gapSeedEquiv ((callInputs l F kclk coef A a ha).filterParams .thr n)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).1)
      (4 * rowOfS l F kclk coef A a ha hs carriers j)
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length
      (Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
        (rowOfU carriers.length j))
      ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD
        (rowOfU carriers.length j) []).length
  idle : ¬ IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j →
    σ.val rRadK = 0 ∧ σ.val rFltK = 0 ∧
    σ.st (sk x 150) = [] ∧ σ.sh (sk x 150) = 0 ∧ σ.st (sk x 151) = [] ∧ σ.sh (sk x 151) = 0 ∧
    σ.st (sk x 1) = out ++ SymDec.unitE (thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
      (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j ++ [false] ∧
    σ.sh (sk x 1) = (out ++ SymDec.unitE (thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
      (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j).length

end Call

structure ThrDecFront (x : ℕ) (l : Literals) (F : GateFree l) where
  s : ℕ
  M : Machine (LNS x + 2 + LNR) s
  need : ℕ → ℕ
  bound : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  Kn : ℕ
  need_q : ∀ n, QuasiBounded (need n) n Cn Dn Kn
  Cb : ℕ
  Db : ℕ
  Kb : ℕ
  bound_q : ∀ n, QuasiBounded (bound n) n Cb Db Kb
  run : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (out : List Bool) (j cap : ℕ), need n + j ≤ cap →
    ∃ (σD : WState (LNS x) LNR) (m : ℕ),
      Step M m (wenc cap (CellLoopD.blankCellD x (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (thrCallU l F kclk coef A a ha hs Cs carriers))).H
        (wenc cap (CellLoopD.blankCellD x (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (thrCallU l F kclk coef A a ha hs Cs carriers))).A
        (wenc cap σD).H (wenc cap σD).A ∧ m ≤ bound n ∧
      ThrDecOut l F kclk coef A a ha hs ha' Cs carriers translation x cap σD out j

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDec
