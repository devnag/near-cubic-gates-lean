import Proof.Wire_3_5.FinalPassSeamsPt
import Proof.Wire_3_5.FinalPassDigsIface
import Proof.Wire_3_5.PrimThrWJoins
import Proof.Wire_3_5.FinalPassFiltTabBlock
import Proof.Wire_3_5.PrimTC4GeoV
import Proof.Wire_3_5.FinalPassListEvalBridge
import Proof.Wire_3_5.FinalPassMaskRef
import Proof.Wire_3_5.PrimAsmDataTabs

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## A per-point evaluator with fixed words -/

/-- **A per-point evaluator with its call words and numbers fixed in the type.** -/
structure PtEvalFix (K : Type) (P : K → StarParams)
    (val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ) (nw nn : ℕ)
    (words : K → Fin nw → List Bool) (nums : K → Fin nn → ℕ) where
  nsc : ℕ
  nrs : ℕ
  prog : ∀ {ns nr : ℕ}, (Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) → (Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ M, need M ≤ C * (M + 1) ^ D
  bound_le : ∀ M, bound M ≤ C * (M + 1) ^ D
  run : ∀ {ns nr : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr)
    (k : K) (c : BitInput (P k).n) (u v : (P k).Errors) (cap : ℕ) (σ : WState ns nr),
    PtIn S R c ((P k).errorVector (P k).leftBlock u) ((P k).errorVector (P k).rightBlock v) (words k) (nums k) σ →
    need ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i) ≤ cap →
    ∃ τ, WExec cap (prog S R) σ τ (bound ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i)) ∧
      PtOut S R σ τ (val k c u v)

/-- Forget that the words are fixed. -/
def PtEvalFix.toW {K : Type} {P : K → StarParams}
    {val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ} {nw nn : ℕ}
    {words : K → Fin nw → List Bool} {nums : K → Fin nn → ℕ} (X : PtEvalFix K P val nw nn words nums) :
    PtEvalW K P val :=
  ⟨nw, nn, X.nsc, X.nrs, words, nums, X.prog, X.need, X.bound, X.C, X.D, X.need_le, X.bound_le, X.run⟩

/-! ## S2: the THR per-point evaluator's words -/

/-- **S2's call words** (THR): 0 the tuple's gate table (ThrData's `tabS`), 1–4 the payloads (`DigsIn`'s `Pay`),
5 the primes up to the cutoff (W6's port 17), 6 stage 4's table at `L = |occs|`. -/
def thrWords (k : ThrCall) : Fin 7 → List Bool := fun i =>
  if i.val = 0 then
    (if k.a = 0 then [] else Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG k.Cs)) (PrimT.ThrTab.tupleG k.Cs))
  else if h : i.val - 1 < k.a ∧ i.val ≤ 4 then PrimThrW.TopFront.payOf k.alg (k.Cs ⟨i.val - 1, h.1⟩)
  else if i.val ≤ 4 then []
  else if i.val = 5 then PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (thrCutoff k.P k.Cs k.alg k.den))
  else ListEval.levelWord k.D.M k.D.J k.D.W (ListEval.rowsOf k.D (thrOccs k.P k.Cs).length)

/-- **S2's numbers** (THR): `a`, `|𝒢|`, `τ₀`, `|occs|`. -/
def thrNums (k : ThrCall) : Fin 4 → ℕ :=
  ![k.a, Fintype.card (ThrEq k.P k.Cs k.alg), thrDigits k.P k.Cs k.alg k.den, (thrOccs k.P k.Cs).length]

/-- **S2's program type**: the THR per-point evaluator of `Σ_{g,p} R̂_{g,p}` reading `thrWords`, `thrNums`. -/
abbrev ThrPtProg : Type :=
  PtEvalFix ThrCall (fun k => k.P)
    (fun k c u v => rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c u v) 7 4 thrWords thrNums

section Req
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm)

/-- **The THR call data at a request**: the fixed hash's lists at `thrCallDen`, `thrCallE/T/J`. -/
def thrCallOf {n : ℕ} (hs : I.StarAt n) {a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ) : ThrCall :=
  ⟨I.starParams n hs, a, ha, Cs, alg, thrCallDen alg I hs Cs,
    MajorantBits.dataBits
      (thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs)
        (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers))
      (thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
        (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers)
        (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers))⟩

/-- The SYM call data at a request. -/
def symCallOf {n : ℕ} (hs : I.StarAt n) {a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) : SymCall :=
  ⟨I.starParams n hs, a, ha, Cs, symListParams I n a Cs carriers⟩

end Req

/-! ## S4's own words -/

/-- **The sampled pairs as stage 0 reads them**: per pair, both indices framed in `s·(r/2)`-bit binary; then `false`. -/
def sampWord (P : StarParams) (smp : CallSample P) : List Bool :=
  (List.ofFn fun l : Fin smp.Q =>
    frame (binary (P.s * (P.r / 2)) (smp.S l).1) ++ frame (binary (P.s * (P.r / 2)) (smp.S l).2)).flatten ++ [false]

/-- **A carrier's mask table** (ThrData's `sCar k 3`): the doubled gates' table, blank past the carriers. -/
def carTab {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) : List Bool :=
  if h : k < carriers.length then
    Corner.gatesW (PrimT.tabH (carriers.get ⟨k, h⟩)) (Corner.maskGates (carriers.get ⟨k, h⟩))
  else []

/-- The mask gates' count of carrier `k` (the filter's point length). -/
def carLen {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) : ℕ :=
  if h : k < carriers.length then (Corner.maskGates (carriers.get ⟨k, h⟩)).length else 0

/-- The seed index width `160·(2⌊errExp/4⌋) + 2r`, `r = wOf·128` (X1's `seedIndex_cast`). -/
def seedWidth (FP : GapParams) : ℕ :=
  160 * (2 * (FP.errExp / 4)) + 2 * (Filt.wOf FP.fieldBits FP.labelBits * 128)

/-- **S4's small numbers**: the star flag `1` (off the star hypotheses the whole word is blank), `b, s, r/2, hL,
n−rb−hL, n−rb, dRow, dR, |mask gates X₀|, |mask gates X₁|, the seed width, |carriers|`. -/
def s4Small (P : StarParams) {n : ℕ} (carriers : List (Carrier n)) (FP : GapParams) : List ℕ :=
  [1, P.b, P.s, P.r / 2, PrimT.C4Geo.hL P, P.n - P.r * P.b - PrimT.C4Geo.hL P, P.n - P.r * P.b, PrimT.C4Geo.dRow P,
    PrimT.C4Geo.dR P, carLen carriers 0, carLen carriers 1, seedWidth FP, carriers.length]

/-- **S4's own words** at a star call: 0 X3's offset word, 1 the sampled pairs, 2–3 the carriers' mask tables,
4–5 stage 6's field words, 6 stage 7's threshold `1^{thr} 0`, 7 the small numbers (unary list). -/
def s4Core (P : StarParams) (σ : P.Translation) (smp : CallSample P) (carriers : List (Carrier P.n))
    (FP : GapParams) : Fin 8 → List Bool :=
  ![frameP (List.ofFn (PrimT.C4Geo.offset P σ)) ++ [false], sampWord P smp, carTab carriers 0, carTab carriers 1,
    Filt.tauWord FP, Filt.modWord FP, ListEval.unary (majorityThreshold FP.walkLen),
    PrimAsm.Data.unaryList (s4Small P carriers FP)]

section Req2
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (E3 : SymPtEval)

/-- **The front's words at a request** (S5 must leave exactly these): S4's 8 words; the THR evaluator's 7 words and
its numbers (unary list); the SYM evaluator's words and its numbers. The other mode's slots, and every slot off the
star hypotheses, are blank. -/
def frontWordsOf : PrimRequest → Fin (17 + E3.nw) → List Bool
  | ⟨n, .sym, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).symS Cs carriers translation hs) carriers (I.filterParams .sym n) ⟨i.val, h8⟩
        else if i.val < 16 then []
        else if h : i.val - 16 < E3.nw then E3.words (symCallOf I hs ha Cs carriers) ⟨i.val - 16, h⟩
        else PrimAsm.Data.unaryList (List.ofFn (E3.nums (symCallOf I hs ha Cs carriers)))
      else []
  | ⟨n, .thr, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs) carriers (I.filterParams .thr n) ⟨i.val, h8⟩
        else if h15 : i.val < 15 then thrWords (thrCallOf I alg hs ha Cs carriers translation) ⟨i.val - 8, by omega⟩
        else if i.val = 15 then
          PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf I alg hs ha Cs carriers translation)))
        else []
      else []

/-- **The largest per-point value** at a request: `|𝒢|·|𝒫|` (THR), the list seeds (SYM). -/
def vmaxOf : PrimRequest → ℕ
  | ⟨n, .sym, a, _, Cs, carriers, _⟩ =>
      if _hs : I.StarAt n then Fintype.card (symListParams I n a Cs carriers).FlatSeed else 0
  | ⟨n, .thr, _, _, Cs, _, _⟩ =>
      if hs : I.StarAt n then
        Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
          Fintype.card (PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
      else 0

end Req2

/-! ## S4's program type -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E3 : SymPtEval)

/-- The front's words at a request of the family. -/
noncomputable abbrev frontWords (r : FReq l F kclk coef A a ha) : Fin (17 + E3.nw) → List Bool :=
  frontWordsOf (callInputs l F kclk coef A a ha) (gate0 l F).alg E3 r.1

/-- The largest per-point value at a request of the family. -/
noncomputable abbrev vmax (r : FReq l F kclk coef A a ha) : ℕ :=
  vmaxOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

structure SeedsProg where
  t : ℕ
  wd : Fin (17 + E3.nw) → Fin t
  tN : Fin t
  tD : Fin t
  reg : Fin t → Bool
  Kc : ℕ
  Dc : ℕ
  s : ℕ
  M : Machine t s
  tab : FReq l F kclk coef A a ha → ℕ
  pt : FReq l F kclk coef A a ha → ℕ
  ov : FReq l F kclk coef A a ha → ℕ
  exitA : (FReq l F kclk coef A a ha → Fin t → List Bool) → (FReq l F kclk coef A a ha → ℕ) →
    FReq l F kclk coef A a ha → Fin t → List Bool
  run : ∀ (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (W : FReq l F kclk coef A a ha → ℕ),
    FrontOut l F kclk coef A a ha wd ![tN, tD] (frontWords l F kclk coef A a ha E3)
      (fun r => ![0, fpDen l F kclk coef A a ha r]) W
      (fun r j => if reg j then Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc + 1 else 0) H Ab →
    (∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r) →
    ∀ r, Step M (seedsShape (seedCount l F kclk coef A a ha r) (tab r) (ptCount l F kclk coef A a ha r) (pt r) (ov r))
        (H r) (Ab r) (fun _ => 0) (exitA Ab W r) ∧
      exitA Ab W r tN = frame (binary (W r) (fpNum l F kclk coef A a ha r)) ∧
      exitA Ab W r tD = frame (binary (W r) (fpDen l F kclk coef A a ha r)) ∧
      fpNum l F kclk coef A a ha r < 2 ^ W r

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
