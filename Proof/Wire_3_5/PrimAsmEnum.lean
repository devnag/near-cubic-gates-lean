import Proof.Wire_3_5.PrimAsmBatch
import Proof.Wire_3_5.PrimAsmThrQ

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Stars

/-- **The filter seeds, enumerated** by base's executable walk-sample enumeration. -/
def gapSeedEquiv (P : GapParams) : GapSeed P ≃ Fin (Fintype.card (GapSeed P)) :=
  SupplierWalkBridge.positiveWalkSampleFinEquiv P.baseSize (2 * (P.errExp / 4))

/-- **The list seeds, enumerated** by base's executable walk-sample enumeration. -/
def flatSeedEquiv (Pl : FlatListParams) : Pl.FlatSeed ≃ Fin (Fintype.card Pl.FlatSeed) :=
  SupplierWalkBridge.positiveWalkSampleFinEquiv Pl.side (2 * (Pl.errExp / 4))

/-- **The joint states, enumerated** in mixed radix `Π_j (m_j+1)²`. -/
def symStateEquiv {a : ℕ} (m : Fin a → ℕ) : Rows.SymState m ≃ Fin (∏ j, (m j + 1) * (m j + 1)) :=
  (Equiv.piCongrRight fun _ => finProdFinEquiv).trans finPiFinEquiv

theorem card_gapSeed_pos (P : GapParams) : 0 < Fintype.card (GapSeed P) := by
  rw [card_gapSeed]; positivity

theorem card_flatSeed_pos (Pl : FlatListParams) : 0 < Fintype.card Pl.FlatSeed := by
  rw [FlatListParams.card_flatSeed]
  have : 0 < Pl.side := Nat.pos_of_ne_zero (NeZero.ne _)
  positivity

theorem prodState_pos {a : ℕ} (m : Fin a → ℕ) : 0 < ∏ j, (m j + 1) * (m j + 1) :=
  Finset.prod_pos fun j _ => by positivity

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- The number of SYM states `|GapSeed|·|FlatSeed|·Π_j(m_j+1)²`. -/
def symNT : ℕ :=
  Fintype.card (GapSeed (I.filterParams .sym n)) * Fintype.card (symListParams I n a Cs carriers).FlatSeed *
    ∏ j, (symM (I.starParams n hs) Cs j + 1) * (symM (I.starParams n hs) Cs j + 1)

theorem symNT_pos : 0 < symNT I hs Cs carriers := by
  unfold symNT
  have h1 := card_gapSeed_pos (I.filterParams .sym n)
  have h2 := card_flatSeed_pos (symListParams I n a Cs carriers)
  have h3 := prodState_pos (symM (I.starParams n hs) Cs)
  positivity

/-- **The SYM states, enumerated**: seed pair major, joint state minor. -/
def symIndexEquiv : SeedFix.SymIndex I hs Cs carriers ≃ Fin (symNT I hs Cs carriers) :=
  (Equiv.prodCongr (((gapSeedEquiv _).prodCongr (flatSeedEquiv _)).trans finProdFinEquiv)
    (symStateEquiv _)).trans finProdFinEquiv

/-- The batch's enumeration of the SYM states (`t` taken below `symNT`). -/
def symEnum (t : ℕ) : SeedFix.SymIndex I hs Cs carriers :=
  (symIndexEquiv I hs Cs carriers).symm ⟨t % symNT I hs Cs carriers, Nat.mod_lt _ (symNT_pos I hs Cs carriers)⟩

theorem symEnum_fin (t : Fin (symNT I hs Cs carriers)) :
    symEnum I hs Cs carriers t = (symIndexEquiv I hs Cs carriers).symm t := by
  unfold symEnum
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt t.isLt)

/-- **The printed column value at the enumerated states is `sampElim` over the call's states** (samp:seed). -/
theorem symSampElim_enum (P : Sampler.SeedParams) (Dz : SeedFix.SymIndex I hs Cs carriers → Fin P.N × Fin P.N → Bool)
    (plen pre : ℕ) :
    SeedFix.sampElim P (fun t : Fin (symNT I hs Cs carriers) => Dz (symEnum I hs Cs carriers t)) plen pre =
      SeedFix.sampElim P Dz plen pre := by
  simp only [symEnum_fin]
  exact Batch.sampElim_reindex P _ (symIndexEquiv I hs Cs carriers).symm Dz plen pre

end Call

/-! ## The THR states -/

/-- **The child selections, enumerated** in mixed radix `Π_i |children_i|`. -/
def thrEqEquiv (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) :
    Primitive.ThrEq P Cs alg ≃
      Fin (∏ i : Fin (List.ofFn Cs).length, (RepairOrdinary.ThresholdRows.children alg ((List.ofFn Cs).get i)).length) :=
  finPiFinEquiv

/-- **The primes up to `c`, in increasing order.** -/
def primeEquiv (c : ℕ) : Fin (SupplierPrime.primesUpTo c).card ≃ SupplierPrime.PrimeIndex c :=
  ((SupplierPrime.primesUpTo c).orderIsoOfFin rfl).toEquiv

theorem primeEquiv_ne_zero (c : ℕ) (i : Fin (SupplierPrime.primesUpTo c).card) : ((primeEquiv c i) : ℕ) ≠ 0 :=
  (SupplierPrime.mem_primesUpTo.mp (primeEquiv c i).2).1.ne_zero

/-- **The prime rows `(p, s mod p)`, enumerated**: primes increasing, then the residue. -/
def primeRowEquiv (c : ℕ) :
    (Σ pr : SupplierPrime.PrimeIndex c, ZMod pr.val) ≃
      Fin (∑ i : Fin (SupplierPrime.primesUpTo c).card, ((primeEquiv c i) : ℕ)) :=
  (Equiv.sigmaCongrLeft (primeEquiv c)).symm.trans <|
    (Equiv.sigmaCongrRight fun i =>
      (@ZMod.finEquiv ((primeEquiv c i) : ℕ) ⟨primeEquiv_ne_zero c i⟩).symm.toEquiv).trans finSigmaFinEquiv

theorem primeRows_sum (c : ℕ) :
    ∑ i : Fin (SupplierPrime.primesUpTo c).card, ((primeEquiv c i) : ℕ) = ThrQ.primeSum c := by
  unfold ThrQ.primeSum
  rw [Fintype.sum_equiv (primeEquiv c) (fun i => ((primeEquiv c i) : ℕ)) (fun pr => (pr : ℕ)) (fun _ => rfl)]
  exact Finset.sum_coe_sort (SupplierPrime.primesUpTo c) id

section ThrCall
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n)

/-- The call's prime cutoff. -/
abbrev thrC : ℕ := thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)

/-- The number of THR states `|GapSeed|·Π_i|children_i|·Σ_{p ≤ cutoff} p`. -/
def thrNT : ℕ :=
  Fintype.card (GapSeed (I.filterParams .thr n)) *
    ((∏ i : Fin (List.ofFn Cs).length,
      (RepairOrdinary.ThresholdRows.children alg ((List.ofFn Cs).get i)).length) *
      ∑ i : Fin (SupplierPrime.primesUpTo (thrC alg I hs Cs)).card, ((primeEquiv (thrC alg I hs Cs) i) : ℕ))

/-- **The THR states, enumerated**: seed major, then the selection, then the prime row. -/
def thrIndexEquiv : SeedFix.ThrIndex alg I hs Cs ≃ Fin (thrNT alg I hs Cs) :=
  (Equiv.prodCongr (gapSeedEquiv _)
    ((Equiv.prodCongr (thrEqEquiv (I.starParams n hs) Cs alg) (primeRowEquiv _)).trans finProdFinEquiv)).trans
    finProdFinEquiv

theorem thrNT_eq_card : thrNT alg I hs Cs = Fintype.card (SeedFix.ThrIndex alg I hs Cs) :=
  (Fintype.card_fin _).symm.trans (Fintype.card_congr (thrIndexEquiv alg I hs Cs)).symm

/-- **The THR state count is the one in `thrCount`**: `2^seedBits·|𝒢|·Σ_{p ≤ cutoff} p` (`ThrQ.thrCount_eq`). -/
theorem thrNT_eq : thrNT alg I hs Cs = 2 ^ (I.filterParams .thr n).seedBits *
    (Fintype.card (ThrEq (I.starParams n hs) Cs alg) * ThrQ.primeSum (thrC alg I hs Cs)) := by
  unfold thrNT
  rw [card_gapSeed, primeRows_sum, ThrQ.card_thrEq]
  rfl

/-- **The printed column value at the enumerated THR states is `sampElim` over the call's states** (samp:seed). -/
theorem thrSampElim_enum (P : Sampler.SeedParams) (Dz : SeedFix.ThrIndex alg I hs Cs → Fin P.N × Fin P.N → Bool)
    (plen pre : ℕ) :
    SeedFix.sampElim P (fun t : Fin (thrNT alg I hs Cs) => Dz ((thrIndexEquiv alg I hs Cs).symm t)) plen pre =
      SeedFix.sampElim P Dz plen pre :=
  Batch.sampElim_reindex P _ (thrIndexEquiv alg I hs Cs).symm Dz plen pre

end ThrCall

end NearCubicWires.WireExponent3_5.PrimAsm.Enum
