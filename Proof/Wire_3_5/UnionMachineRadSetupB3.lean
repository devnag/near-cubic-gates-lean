import Proof.Wire_3_5.UnionMachineRadSetupB2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2

/-- **The RADIX setup's entry bank, v4** (addendum): `RadSetupB2.RsIn3` without `blankT` (the unit chain's
number and front-end ports leave residues on the producer's scratch tapes `sT`). -/
structure RsIn4 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (v : Fin 20 → ℕ)
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
  vals : ∀ i : Fin 20, σ.val (rsReg i) = v i
  vNc : σ.val rNcK = ncar
  vCap : σ.val rCapK = capT
  vA : σ.val rAK = a'
  zero : ∀ r : Fin LNR, (r.val < 250 ∨ (400 ≤ r.val ∧ r.val < 410) ∨ 433 ≤ r.val) → σ.val r = 0
  cell : σ.cell = false

/-- **A Route-B RADIX-ready cell state, v2**: `RadSetupB.RadReadyB` with the blank streams only below `130`
(outside the request `0`, the output `1`, the counter `2`, the record `3` and the data `113`), no `blankT`. -/
structure RadReadyB2 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (q : RadReqB) :
    Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s3 : σ.st (sk x 3) = frame q.record
  h3 : σ.sh (sk x 3) = 0
  s113 : σ.st (sk x 113) = u
  h113 : σ.sh (sk x 113) = 0
  s150 : σ.st (sk x 150) = [true]
  h150 : σ.sh (sk x 150) = 0
  blank : ∀ k : Fin 161, k.val < 130 → k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 3 → k.val ≠ 113 →
    σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  pre : q.r.Pre
  caps : q.Caps

/-- **The RADIX row setup, Route B, exit v2**: `RadSetupB2.RadSetupSpecB2` from `RsIn4` (the circuits'
payloads and `a'`, no `blankT`) ending in `RadReadyB2`. -/
structure RadSetupSpecB3 (x : ℕ) (l : Literals) (F : GateFree l) where
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
    RsIn4 x σ ((thrReq n a' ha' Cs carriers translation).word ++
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
      RadReadyB2 x σR ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
          ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
        out j u q

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3
