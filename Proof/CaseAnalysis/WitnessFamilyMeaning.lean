import Proof.CaseAnalysis.CloseoutWitnessColdFamilyLayout
import Proof.CaseAnalysis.WitnessFamilyGuards

/-! The whole cold family keeps the exact original family output layout.
This predicate is merely its retained streams/store, not a supplied worker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open CompetitorSumFold CompetitorSumWidth RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def retained (sym : Bool) (P V C T core W L km : ℕ) (q : ℚ) (bits : List Bool)
    (cursor : Fin 3243→ℕ) (data : Fin 3243→List Bool) : Prop:=
  let arity:=SignedSortKey.binary (natBitLength core) core
  ∃ extra after,extra 174=List.replicate V true ∧
    cursor=FamilyPrepare.heads (FamilyWork.heads
      (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T core W L km q
        (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
        [] [] [] (FamilyMode.native sym core) V after) 1) ∧
    data=FamilyPrepare.tapes (natBitLength C) bits (FamilyWork.tapes (P+1) V
      (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T core W L km q
        (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
        [] [] [] (FamilyMode.native sym core) V after) extra) ∧
    Store (width T (natBitLength C)) zero [] after

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def scale (a : PointwisePCPPAlgorithm) (G D copies : ℕ) (delta : ℚ) (n : ℕ):=
  FamilyResources.sourceScale a source.coefficient source.degrees.queries G D delta copies n
def familyFlag (a : PointwisePCPPAlgorithm) (k CH Cpad D copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let cb:=(a.output r).clauseBits
  let W:=LegalPolicy.W e den r.arity
  FamilyCold.passed sym ((a.output r).systematicBits+(a.output r).auxiliaryBits)
    (FamilyResources.coefficientCap delta copies D r.arity cb) (FamilyResources.termCap delta copies D r.arity cb)
    r.arity W (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) W)
    (CloseoutSampledWitness.massCap delta copies) bits (SignedSortKey.binary (natBitLength r.arity) r.arity)
def passed (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw bits : List Bool) (hpad : k+3≤Cpad):=
  ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw &&
    (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).any
      (familyFlag source a k CH Cpad D copies e den delta code sym x bits hpad)
def tailBudget (a : PointwisePCPPAlgorithm) (k CH Cpad D G copies E K : ℕ) (delta : ℚ)
    (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  let P:=FamilyCapacity.value E K n
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  FamilyCapacity.budget E K n+1+FamilyCold.budget P (P+1)
    ((a.output r).systematicBits+(a.output r).auxiliaryBits) (FamilyResources.sumCost (scale source a G D copies delta n) P) bits
def budget (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw bits : List Bool) (hpad : k+3≤Cpad):=
  ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad+1+
    (if ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true then
      (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).elim 0
        (fun oracle=>tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle+1) else 0)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
