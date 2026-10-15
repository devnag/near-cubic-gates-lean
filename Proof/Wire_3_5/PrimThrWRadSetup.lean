import Proof.Wire_3_5.PrimThrWJoins
import Proof.Wire_3_5.PrimAsmWriterIfaceJ

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins

/-! ## The inputs on the cell layout -/

/-- The setup's twenty input registers `410 … 429`. -/
def rsReg (i : Fin 20) : Fin LNR := ⟨410 + i.val, by have := i.isLt; unfold LNR; omega⟩

theorem rsReg_inj : Function.Injective rsReg := by
  intro a b h
  have := congrArg Fin.val h
  simp only [rsReg] at this
  exact Fin.ext (by omega)

/-- The primes stream (W6's `sPr`), the level-records stream (`sWin`), the modulus-word stream (`sMod`). -/
def sPrK : Fin 161 := 130
def sWinK : Fin 161 := 131
def sModK : Fin 161 := 132

/-- **The RADIX setup's entry bank**: the unit's streams as in `FsIn2` (request `frame w`, head `0`; output
`out ++ [false]`, head `|out|`; counter `1^j`, head `0`; data `u` on `113`, head `0`), W6's words on `130`, `131`, `132`
(heads `0`), every other stream empty (head `0`); the twenty values `v` in `410 … 429`; every register outside
`250 … 399` (the decode's scratch) and `410 … 429` zero; the cell `false`. -/
structure RsIn (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (v : Fin 20 → ℕ)
    (prW winW modW : List Bool) : Prop where
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
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → k.val ≠ 130 → k.val ≠ 131 →
    k.val ≠ 132 → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  vals : ∀ i : Fin 20, σ.val (rsReg i) = v i
  zero : ∀ r : Fin LNR, (r.val < 250 ∨ (400 ≤ r.val ∧ r.val < 410) ∨ 430 ≤ r.val) → σ.val r = 0
  cell : σ.cell = false

/-- The paper's expansion bound `v ≤ C·(n+2)^D·2^{K·L²}`, `L = ⌈log₂(n+2)⌉`. -/
def QuasiBounded (v n C D K : ℕ) : Prop := v ≤ C * (n + 2) ^ D * 2 ^ (K * Nat.clog 2 (n + 2) ^ 2)

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The THR numbers at the call (`Dexp = D`, the call's carriers and THR filter cap). -/
noncomputable abbrev callNums : ThrNumVals :=
  thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap

/-- **The twenty register values** of the RADIX setup: `gi` (the selection's index), `p`, `s`, the star row, `|thrPool|`,
the occurrence offset `thrOff`, `n`, then W6's `|𝒢|, K, cut, #primes, Σp, τ₀, M, A, B_*, J, t, ℓ₀, p_mod`. -/
noncomputable def radVals (gi p s row : ℕ) : Fin 20 → ℕ :=
  ![gi, p, s, row, (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length,
    Records.thrOff ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers, n,
    (callNums l F kclk coef A a ha hs Cs carriers).nG, (callNums l F kclk coef A a ha hs Cs carriers).den,
    (callNums l F kclk coef A a ha hs Cs carriers).cut, (callNums l F kclk coef A a ha hs Cs carriers).nPr,
    (callNums l F kclk coef A a ha hs Cs carriers).pSum, (callNums l F kclk coef A a ha hs Cs carriers).dig,
    (callNums l F kclk coef A a ha hs Cs carriers).M, (callNums l F kclk coef A a ha hs Cs carriers).A,
    (callNums l F kclk coef A a ha hs Cs carriers).Bs, (callNums l F kclk coef A a ha hs Cs carriers).J,
    (callNums l F kclk coef A a ha hs Cs carriers).tt, (callNums l F kclk coef A a ha hs Cs carriers).ell0,
    (callNums l F kclk coef A a ha hs Cs carriers).pMod]

/-- **The RADIX row's C2 request** at selection `g`, prime `pr`, residue `s`, star row `row`. -/
noncomputable def radReqOf (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (s : ZMod pr.val) (row : ℕ) : ListMachine.Row.RadReq :=
  ⟨Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation,
    Records.thrDigs ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) g pr
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length row,
    pr.val, 2, s.val, n⟩

/-- The THR entry's RADIX row is `radReqOf`'s request (`Records.thrGroups`' last group). -/
theorem radRow_eq (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (s : ZMod pr.val) (row : ℕ) :
    Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) g pr s
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length row n =
      .rad (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row) := rfl

end Call

structure RadSetupSpec (x : ℕ) (l : Literals) (F : GateFree l) where
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
    ∀ (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
      (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (s : ZMod pr.val) (row : ℕ),
    row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 →
    ∀ (cap : ℕ) (out : List Bool) (j : ℕ) (u : List Bool) (σ : WState (LNS x) LNR),
    RsIn x σ ((thrReq n a' ha' Cs carriers translation).word ++
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
        (callNums l F kclk coef A a ha hs Cs carriers).pMod)) →
    need n ≤ cap →
    ∃ (σR : WState (LNS x) LNR) (m : ℕ),
      Step M m (wenc cap σ).H (wenc cap σ).A (wenc cap σR).H (wenc cap σR).A ∧ m ≤ bound n ∧
      RadReady x σR ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
          ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
        out j u (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row)

end NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
