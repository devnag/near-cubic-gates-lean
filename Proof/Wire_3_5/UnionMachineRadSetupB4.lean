import Proof.Wire_3_5.UnionMachineRadSetupB3
import Proof.Wire_3_5.UnionMachineRadSpec
import Proof.Wire_3_5.FinalPassDigsIface

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- **The RADIX row's explicit capacity measure** at prime `pr` and star row `row`. -/
noncomputable def radMeas (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) (row : ℕ) : ℕ :=
  RadSpec.radX (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ((4 * row + 4) * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)
      (ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
      (FinalPass.ListEval.levelWord (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W
        (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
          (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)).length pr.val 2 +
    ((thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 1) ^ (2 * thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) +
    ((thrReq n a' ha' Cs carriers translation).word ++ frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))).length +
    thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers + thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers +
    FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val

end Call

/-- **The RADIX row setup, Route B, v4**: `RadSetupSpecB3`'s run with `need`, `bound`, `pipe` polynomial in the
row's explicit capacity measure `radMeas` (the cost in the capacity). -/
structure RadSetupSpecB4 (x : ℕ) (l : Literals) (F : GateFree l) where
  s : ℕ
  M : Machine (LNS x + 2 + LNR) s
  need : ℕ → ℕ
  bound : ℕ → ℕ
  pipe : ℕ → ℕ
  Kn : ℕ
  Dn : ℕ
  need_le : ∀ X, need X ≤ Kn * (X + 1) ^ Dn
  Kb : ℕ
  Db : ℕ
  bound_le : ∀ c, bound c ≤ Kb * (c + 1) ^ Db
  Kp : ℕ
  Dp : ℕ
  pipe_le : ∀ X, pipe X ≤ Kp * (X + 1) ^ Dp
  run : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
      (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (s : ZMod pr.val) (row : ℕ),
    row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 →
    ∀ (cap : ℕ) (out : List Bool) (j : ℕ) (u : List Bool) (σ : WState (LNS x) LNR),
    RsIn4 x σ ((thrReq n a' ha' Cs carriers translation).word ++ frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))) out j u
      (radVals l F kclk coef A a ha hs Cs carriers
        ((Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg g).val) pr.val s.val row)
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A
        (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0
        (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a' →
    need (radMeas l F kclk coef A a ha hs ha' Cs carriers translation pr row) ≤ cap →
    ∃ (σR : WState (LNS x) LNR) (m : ℕ) (q : RadReqB),
      Step M m (wenc cap σ).H (wenc cap σ).A (wenc cap σR).H (wenc cap σR).A ∧ m ≤ bound cap ∧
      q.r = radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row ∧
      q.bound ≤ pipe (radMeas l F kclk coef A a ha hs ha' Cs carriers translation pr row) ∧
      RadReadyB2 x σR ((thrReq n a' ha' Cs carriers translation).word ++ frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))) out j u q

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB4
