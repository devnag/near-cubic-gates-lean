import Proof.Wire_3_5.UnionMachineRadSetupB
import Proof.Wire_3_5.PrimThrWTopFront

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB

/-- Circuit `i`'s payload stream. -/
def sPayK (i : Fin 4) : Fin 161 := ⟨133 + i.val, by have := i.isLt; omega⟩

/-- The circuit count's register. -/
def rAK : Fin LNR := ⟨432, by decide⟩

/-- **The RADIX setup's entry bank, v3**: `RsIn2` plus the payloads `pays i` on `133 + i` (heads `0`) and `a'` in
`432`: the unit's streams as in `FsIn2`, W6's words on `130`, `131`, `132`, every other stream empty (head `0`); the
twenty values `v` in `410 … 429`, `ncar` in `430`, `cap_T` in `431`; every register outside `250 … 399` and
`410 … 432` zero; the cell `false`. -/
structure RsIn3 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (v : Fin 20 → ℕ)
    (prW winW modW : List Bool) (ncar capT : ℕ) (pays : Fin 4 → List Bool) (a' : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s113 : σ.st (sk x 113) = u
  h113 : σ.sh (sk x 113) = 0
  sPr : σ.st (sk x sPrK) = prW
  hPr : σ.sh (sk x sPrK) = 0
  sWin : σ.st (sk x sWinK) = winW
  hWin : σ.sh (sk x sWinK) = 0
  sMod : σ.st (sk x sModK) = modW
  hMod : σ.sh (sk x sModK) = 0
  sPay : ∀ i : Fin 4, σ.st (sk x (sPayK i)) = pays i
  hPay : ∀ i : Fin 4, σ.sh (sk x (sPayK i)) = 0
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → k.val ≠ 130 → k.val ≠ 131 →
    k.val ≠ 132 → (k.val < 133 ∨ 137 ≤ k.val) → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  vals : ∀ i : Fin 20, σ.val (rsReg i) = v i
  vNc : σ.val rNcK = ncar
  vCap : σ.val rCapK = capT
  vA : σ.val rAK = a'
  zero : ∀ r : Fin LNR, (r.val < 250 ∨ (400 ≤ r.val ∧ r.val < 410) ∨ 433 ≤ r.val) → σ.val r = 0
  cell : σ.cell = false

/-- **The RADIX row setup, Route B, entry v3**: `RadSetupB.RadSetupSpecB` from `RsIn3` with circuit `i`'s
payload `TopFront.payOf alg (Cs i)` (blank for `i ≥ a'`) and `a'`. -/
structure RadSetupSpecB2 (x : ℕ) (l : Literals) (F : GateFree l) where
  s : ℕ
  M : Machine (LNS x + 2 + LNR) s
  need : ℕ → ℕ
  bound : ℕ → ℕ
  pipe : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  Kn : ℕ
  need_q : ∀ n, QuasiBounded (need n) n Cn Dn Kn
  Cb : ℕ
  Db : ℕ
  Kb : ℕ
  bound_q : ∀ n, QuasiBounded (bound n) n Cb Db Kb
  Cp : ℕ
  Dp : ℕ
  Kp : ℕ
  pipe_q : ∀ n, QuasiBounded (pipe n) n Cp Dp Kp
  run : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
      (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (s : ZMod pr.val) (row : ℕ),
    row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 →
    ∀ (cap : ℕ) (out : List Bool) (j : ℕ) (u : List Bool) (σ : WState (LNS x) LNR),
    RsIn3 x σ ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
          ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
      out j u
      (radVals l F kclk coef A a ha hs Cs carriers
        ((Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg g).val) pr.val s.val
        row)
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A
        (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0
        (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a' →
    need n ≤ cap →
    ∃ (σR : WState (LNS x) LNR) (m : ℕ) (q : RadReqB),
      Step M m (wenc cap σ).H (wenc cap σ).A (wenc cap σR).H (wenc cap σR).A ∧ m ≤ bound n ∧
      q.r = radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row ∧ q.bound ≤ pipe n ∧
      RadReadyB x σR ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
          ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
        out j u q

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2
