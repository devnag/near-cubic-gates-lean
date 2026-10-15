import Proof.Wire_3_5.PrimAsmFiltSetupIface2
import Proof.Wire_3_5.PrimAsmWriterIface
import Proof.Wire_3_5.PrimAsmThrDataIface
import Proof.Wire_3_5.FinalPassHashBuild
import Proof.Wire_3_5.ListMachineRowRadixClass

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline

/-! ## (1) The THR numbers -/

/-- **The primes up to `c`, increasing** (the prime rows' order). -/
def primesList (c : ℕ) : List ℕ := (List.range (c + 1)).filter Nat.Prime

/-- The fourteen THR numbers of a call. -/
structure ThrNumVals where
  /-- `|𝒢|` -/
  nG : ℕ
  /-- `K = 8(|𝒢|+1)n^D` -/
  den : ℕ
  /-- the prime cutoff -/
  cut : ℕ
  /-- the number of primes `≤ cut` -/
  nPr : ℕ
  /-- `Σ_{p ≤ cut} p` -/
  pSum : ℕ
  /-- `τ₀ = ⌈log₂ cut⌉` -/
  dig : ℕ
  /-- `M = |occs|` -/
  M : ℕ
  /-- `A = |𝒢|·|primes|·τ₀·2` -/
  A : ℕ
  /-- `B_* = a·4096·cap_aux` -/
  Bs : ℕ
  /-- the list depth `J` -/
  J : ℕ
  /-- the moment order `t` -/
  tt : ℕ
  /-- the aux filter's error exponent `e` -/
  ee : ℕ
  /-- the field dimension `ℓ₀` -/
  ell0 : ℕ

  pMod : ℕ

/-- The values in register order `0 … 13`. -/
def ThrNumVals.get (v : ThrNumVals) : Fin 14 → ℕ :=
  ![v.nG, v.den, v.cut, v.nPr, v.pSum, v.dig, v.M, v.A, v.Bs, v.J, v.tt, v.ee, v.ell0, v.pMod]

/-- The fixed hash's majorant parameters from `M, A, B_*, K`. -/
def thrMP (M A Bs den : ℕ) : MajorantParams :=
  ⟨M, A, Bs, Primitive.listT A Bs den, Primitive.listJ A Bs den⟩

/-- **The THR numbers of a call** (`Dexp` the target exponent `D`, `ncar = |carriers|`, `capT` the THR filter cap). -/
def thrNumVals (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp ncar capT : ℕ) : ThrNumVals :=
  let nG := Fintype.card (Primitive.ThrEq P Cs alg)
  let den := 8 * (nG + 1) * P.n ^ Dexp
  let cut := Primitive.thrCutoff P Cs alg den
  let dig := Primitive.thrDigits P Cs alg den
  let nPr := (SupplierPrime.primesUpTo cut).card
  let M := (Primitive.thrOccs P Cs).length
  let A := nG * (nPr * (dig * 2))
  let Bs := a' * (4096 * ((ncar + 1) * (4096 * capT)))
  ⟨nG, den, cut, nPr, ThrQ.primeSum cut, dig, M, A, Bs, (thrMP M A Bs den).J, (thrMP M A Bs den).t,
    Primitive.listE A Bs M den, (thrMP M A Bs den).ell0, (thrMP M A Bs den).refMod⟩

/-- **The level records** of finalpass stage 4's input (`winWord M L J W` is `unary M ++ unary L ++ unary J ++ winRecs
++ [false]`). -/
def winRecs (MP : MajorantParams) : List Bool :=
  (FinalPass.ListEval.levels MP.J).flatMap (FinalPass.Hash4.winRec MP.J MP.W)

section Anchors
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}

theorem thrNumVals_den (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (ncar capT : ℕ) :
    (thrNumVals (I.starParams n hs) Cs alg I.D ncar capT).den = Primitive.thrCallDen alg I hs Cs := rfl

theorem thrNumVals_A (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (ncar capT : ℕ) :
    (thrNumVals (I.starParams n hs) Cs alg I.D ncar capT).A = Primitive.thrCallA alg I hs Cs := by
  unfold Primitive.thrCallA thrNumVals
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, SupplierPrime.PrimeIndex, Fintype.card_coe]
  rfl

theorem thrNumVals_MP (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (FP : GapParams) (alg : RepairRepresentation.DecompositionAlgorithm)
    (Dexp e : ℕ) :
    Primitive.thrMajorant P Cs carriers FP alg (thrNumVals P Cs alg Dexp carriers.length FP.cap).den e
        (thrNumVals P Cs alg Dexp carriers.length FP.cap).tt (thrNumVals P Cs alg Dexp carriers.length FP.cap).J =
      thrMP (thrNumVals P Cs alg Dexp carriers.length FP.cap).M (thrNumVals P Cs alg Dexp carriers.length FP.cap).A
        (thrNumVals P Cs alg Dexp carriers.length FP.cap).Bs (thrNumVals P Cs alg Dexp carriers.length FP.cap).den := by
  unfold Primitive.thrMajorant thrMP thrNumVals Primitive.thrAux
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, SupplierPrime.PrimeIndex, Fintype.card_coe]
  rfl

theorem primesList_sorted (c : ℕ) : primesList c = (SupplierPrime.primesUpTo c).sort := by
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≤ b)
  · exact (List.pairwise_lt_range.filter _).imp le_of_lt
  · exact Finset.pairwise_sort _ _
  · refine (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range) (Finset.sort_nodup _ _)).mpr ?_
    intro p
    simp [SupplierPrime.primesUpTo, Finset.mem_sort]

/-- **The prime of index `i`** is `primesList c`'s `i`-th entry (`Enum.primeEquiv`'s order). -/
theorem primesList_get (c : ℕ) (i : Fin (SupplierPrime.primesUpTo c).card) :
    ((Enum.primeEquiv c i) : ℕ) = (primesList c).getD i 0 := by
  have hl : (primesList c).length = (SupplierPrime.primesUpTo c).card := by
    rw [primesList_sorted, Finset.length_sort]
  show (((SupplierPrime.primesUpTo c).orderIsoOfFin rfl) i : ℕ) = _
  rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply,
    List.getD_eq_getElem _ _ (by rw [hl]; exact i.isLt)]
  simp only [primesList_sorted]
  rfl

/-- The THR state count in the numbers (`Enum.thrNT_eq`). -/
theorem thrNumVals_nT (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (ncar capT : ℕ) :
    Enum.thrNT alg I hs Cs = 2 ^ (I.filterParams .thr n).seedBits *
      ((thrNumVals (I.starParams n hs) Cs alg I.D ncar capT).nG *
        (thrNumVals (I.starParams n hs) Cs alg I.D ncar capT).pSum) :=
  Enum.thrNT_eq alg I hs Cs

end Anchors

/-- **The THR-numbers machine** (interface, W6): a machine on the encoded banks `wenc cap σ` of its own register layout
`WState ns nr` (a compiled word program, or word programs composed with docked machines such as the primitive-modulus
search), docked by each consumer. ENTRY: stream `0` holds the framed THR request word `Data.reqW n true (thrCodes Cs) codes tl`
with its head at `0`; every other stream empty, head `0`; register `rNc = |carriers|`, register `rCap =` the THR
filter's cap, every other register `0`; the cell `false`. EXIT (within `bound (n + cap_T)` steps at every capacity
`≥ need (n + cap_T)`): stream `0` unchanged, head `0`; register `out k` holds `(thrNumVals …).get k`; `rNc`, `rCap`
unchanged; every other register `0`; stream `sPr` holds `Data.unaryList (primesList cut)`, stream `sWin` holds
`winRecs (thrMP M A B_* K)`, stream `sMod` holds `frame (binary ℓ₀ p)` (finalpass stage 4's modulus word), heads
`0`; every other stream empty, head `0`; the cell `false`. -/
structure ThrNumsSpec (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) where
  ns : ℕ
  nr : ℕ
  s : ℕ
  M : Machine (ns + 2 + nr) s
  rNc : Fin nr
  rCap : Fin nr
  out : Fin 14 → Fin nr
  out_inj : Function.Injective out
  out_ne_nc : ∀ k, out k ≠ rNc
  out_ne_cap : ∀ k, out k ≠ rCap
  nc_ne_cap : rNc ≠ rCap
  sPr : Fin (ns + 1)
  sWin : Fin (ns + 1)
  sPr_ne : sPr ≠ 0
  sWin_ne : sWin ≠ 0
  sPr_ne_sWin : sPr ≠ sWin
  sMod : Fin (ns + 1)
  sMod_ne : sMod ≠ 0
  sMod_ne_sPr : sMod ≠ sPr
  sMod_ne_sWin : sMod ≠ sWin
  need : ℕ → ℕ
  bound : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  need_poly : ∀ m, ValidatorPolynomialDomination.PolyBounded (need m) m Cn Dn
  Cb : ℕ
  Db : ℕ
  bound_poly : ∀ m, ValidatorPolynomialDomination.PolyBounded (bound m) m Cb Db
  run : ∀ (cap : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (codes : List ℕ) (tl : List Bool) (ncar capT : ℕ) (σ : WState ns nr),
    1 ≤ a' → a' ≤ 4 → (∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) → ncar ≤ 2 → 1 ≤ capT →
    σ.st 0 = frame (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) → σ.sh 0 = 0 →
    (∀ i : Fin (ns + 1), i ≠ 0 → σ.st i = [] ∧ σ.sh i = 0) →
    σ.val rNc = ncar → σ.val rCap = capT → (∀ r, r ≠ rNc → r ≠ rCap → σ.val r = 0) → σ.cell = false →
    need (P.n + capT) ≤ cap →
    ∃ (τ : WState ns nr) (m : ℕ), Step M m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ bound (P.n + capT) ∧
      τ.st 0 = σ.st 0 ∧ τ.sh 0 = 0 ∧ τ.cell = false ∧ τ.val rNc = ncar ∧ τ.val rCap = capT ∧
      (∀ k, τ.val (out k) = (thrNumVals P Cs alg Dexp ncar capT).get k) ∧
      (∀ r, r ≠ rNc → r ≠ rCap → (∀ k, out k ≠ r) → τ.val r = 0) ∧
      τ.st sPr = Data.unaryList (primesList (thrNumVals P Cs alg Dexp ncar capT).cut) ∧ τ.sh sPr = 0 ∧
      τ.st sWin = winRecs (thrMP (thrNumVals P Cs alg Dexp ncar capT).M (thrNumVals P Cs alg Dexp ncar capT).A
        (thrNumVals P Cs alg Dexp ncar capT).Bs (thrNumVals P Cs alg Dexp ncar capT).den) ∧ τ.sh sWin = 0 ∧
      τ.st sMod = frame (SignedSortKey.binary (thrNumVals P Cs alg Dexp ncar capT).ell0
        (thrNumVals P Cs alg Dexp ncar capT).pMod) ∧ τ.sh sMod = 0 ∧
      (∀ i : Fin (ns + 1), i ≠ 0 → i ≠ sPr → i ≠ sWin → i ≠ sMod → τ.st i = [] ∧ τ.sh i = 0)

/-! ## (3) The RADIX row's entry on the cell layout -/

/-- **A RADIX-ready cell state** (the entry of the THR unit's RADIX pipe): request `frame w` on stream `0`, output
`out ++ [false]` on stream `1` (head `|out|`), counter `1^j` on stream `2`, the framed row record `frame r.record`
(C2's `radContract` input) on stream `3`, the data `u` on stream `113`, the RADIX flag `[true]` on stream `150`; heads at
`0` but the output's; every other stream empty; the request admissible (`RadReq.Pre`). -/
structure RadReady (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (r : ListMachine.Row.RadReq) : Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s3 : σ.st (sk x 3) = frame r.record
  h3 : σ.sh (sk x 3) = 0
  s113 : σ.st (sk x 113) = u
  h113 : σ.sh (sk x 113) = 0
  s150 : σ.st (sk x 150) = [true]
  h150 : σ.sh (sk x 150) = 0
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 3 → k.val ≠ 113 → k.val ≠ 150 →
    σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  pre : r.Pre

/-! ## (5) The THR FILTER rows dock `FiltSetupSpec2` -/

section Filt
variable (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Stars.Carrier P.n))

/-- **The eight FILTER-setup values** of the THR FILTER row `jr` of state `t` at star row `row` (`nG = |𝒢|`,
`pSum = Σp`): `FP.len, FP.cap, FP.errExp`, the seed index `t / (nG·pSum)`, `4·row`, `|thrPool|`, the slice's offset and
length. -/
def thrFiltVals (FP : GapParams) (nG pSum t row jr : ℕ) : Fin 8 → ℕ :=
  ![FP.len, FP.cap, FP.errExp, t / (nG * pSum), 4 * row, (Records.thrPool P Cs carriers).length,
    Records.sliceOff (Records.thrSlices P Cs carriers) jr, ((Records.thrSlices P Cs carriers).getD jr []).length]

/-- **The THR FILTER row's reference is what `filtPipe_ready` prints** from the eight values. -/
theorem thrFilt_emit (FP : GapParams) (e : GapSeed FP) (G row nw jr : ℕ) :
    WriterIface.refOf (Records.filtRow (Records.thrSlices P Cs carriers) FP e G row nw jr) =
      ListMachine.Row.filtRefC (FinalPass.Filt.filterTable FP e ((Records.thrSlices P Cs carriers).getD jr []).length)
        (SupplierWalk.majorityThreshold FP.walkLen) ((Records.thrSlices P Cs carriers).getD jr []).length true
        (Emit.sliceLabs (4 * row) G (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
          ((Records.thrSlices P Cs carriers).getD jr []).length) := by
  rw [← Emit.labs_eq]
  rfl

/-- The labels' length precondition of `FiltSetupSpec2.run`. -/
theorem thrFilt_labs (r4 G off L : ℕ) : (Emit.sliceLabs r4 G off L).length = 4 * L := by
  unfold Emit.sliceLabs Emit.gateLabs
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate, List.length_range',
    smul_eq_mul]
  ring

def ThrFiltDock (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (v : Fin 8 → ℕ) : Prop :=
  FiltSetup.FsIn2 x σ w out j u (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)

end Filt

end NearCubicWires.WireExponent3_5.PrimThrW.Joins
