import Proof.Assembly.NativeSelected
import Proof.MachineModel.ClosureBinaryPool
import Proof.CaseAnalysis.FinalModeNativeStageFields
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierTouching
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierRadix
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open scoped BigOperators
namespace FixedLivePackets

namespace CyclicChoice

def window (q K start : Nat) : Finset (Fin q) :=
  Finset.univ.filter (fun x => (x.val + q - start % q) % q < K)

def incidenceScore {q m : Nat} (support : Fin m → Finset (Fin q))
    (K start : Nat) : Nat :=
  ∑ i, ∑ x ∈ support i, if x ∈ window q K start then 1 else 0

def firstMinimumStart {q m : Nat} (support : Fin m → Finset (Fin q)) (K : Nat) : Nat :=
  ((List.range q).foldl (fun best start =>
    let score := incidenceScore support K start
    if score < best.2 then (start, score) else best)
    (0, incidenceScore support K 0)).1

def selectedLive {q m : Nat} (support : Fin m → Finset (Fin q)) (K : Nat) : Finset (Fin q) :=
  window q K (firstMinimumStart support K)

def live {q : Nat} (occ : List (SupportedNormalizedGate q)) (L : Nat) : Finset (Fin q) :=
  selectedLive (occurrenceSupport occ) (normalizedLiveCount q L)

def mask {q : Nat} (occ : List (SupportedNormalizedGate q)) (L : Nat) : List Bool :=
  List.ofFn (fun x : Fin q => decide (x ∈ live occ L))

def Laws : Prop := ∀ {q m K : Nat} (support : Fin m → Finset (Fin q)), K ≤ q →
  (selectedLive support K).card = K ∧
  q * touchingCost support (selectedLive support K) ≤ K * supportIncidenceMass support
end CyclicChoice

namespace Ring
abbrev Poly (α : Type) := List (List α)
def canon {α : Type} [LinearOrder α] (m : List α) : List α :=
  (m.insertionSort (· ≤ ·)).dedup
def toggle {α : Type} [DecidableEq α] (m : List α) (P : Poly α) : Poly α :=
  if m ∈ P then P.erase m else m :: P
def norm {α : Type} [LinearOrder α] (P : Poly α) : Poly α :=
  P.foldl (fun acc m => toggle (canon m) acc) []
def add {α : Type} [DecidableEq α] (P Q : Poly α) : Poly α :=
  Q.foldl (fun acc m => toggle m acc) P
def mul {α : Type} [LinearOrder α] (P Q : Poly α) : Poly α :=
  P.foldl (fun acc m => Q.foldl (fun acc n => toggle (canon (m ++ n)) acc) acc) []
def Eval {α : Type} (a : α → Bool) (P : Poly α) : Bool :=
  exactPolynomialValue (fun i (_ : Unit) (_ : Unit) => a i) P () ()
def Normal {α : Type} [LinearOrder α] (P : Poly α) : Prop :=
  P.Nodup ∧ ∀ m ∈ P, m.Pairwise (· < ·)
def Degree {α : Type} (d : Nat) (P : Poly α) : Prop := ∀ m ∈ P, m.length ≤ d
end Ring

namespace Normalized
-- These constructors normalize at each addition/multiplication/substitution.
def structuralGF2Add (P Q : StructuralGF2Polynomial) : StructuralGF2Polynomial := Ring.add P Q
def structuralGF2Mul (P Q : StructuralGF2Polynomial) : StructuralGF2Polynomial := Ring.mul P Q
def structuralGF2Sum (ps : List StructuralGF2Polynomial) : StructuralGF2Polynomial :=
  ps.foldl structuralGF2Add structuralGF2Zero
def structuralGF2Not
    (polynomial : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Add structuralGF2One polynomial

def structuralGF2Or
    (left right : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Add (structuralGF2Add left right)
    (structuralGF2Mul left right)

def structuralGF2Product
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.foldr structuralGF2Mul structuralGF2One

def structuralGF2Disjunction
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.foldr structuralGF2Or structuralGF2Zero

def structuralGF2Substitute
    (atom : ℕ → StructuralGF2Polynomial) :
    StructuralGF2Polynomial → StructuralGF2Polynomial
  | [] => structuralGF2Zero
  | monomial :: polynomial =>
      structuralGF2Add
        (structuralGF2Product (monomial.map atom))
        (structuralGF2Substitute atom polynomial)

def structuralGF2FinParity :
    {arity : ℕ} →
      (Fin arity → StructuralGF2Polynomial) →
        StructuralGF2Polynomial
  | 0, _ => structuralGF2Zero
  | _ + 1, polynomials =>
      structuralGF2Add (polynomials 0)
        (structuralGF2FinParity fun index => polynomials index.succ)

def structuralGF2OneHotLookup
    {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot :
      Fin (populationBound + 1) → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun candidate =>
    if lookup candidate then oneHot candidate else structuralGF2Zero

def structuralGF2BooleanSelector
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (target : BitInput arity) :
    StructuralGF2Polynomial :=
  structuralGF2Product <|
    List.ofFn fun index =>
      if target index then bits index
      else structuralGF2Not (bits index)

def structuralGF2TruthTable
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (function : BitInput arity → Bool) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun code : Fin (2 ^ arity) =>
    if function (structuralTruthAssignment arity code) then
      structuralGF2BooleanSelector bits
        (structuralTruthAssignment arity code)
    else
      structuralGF2Zero

def structuralGF2BitMajority
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2TruthTable bits compiledBitMajority

def structuralGF2FiniteConjunction
    {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Product (List.ofFn values)

def structuralGF2FiniteDisjunction
    {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Disjunction (List.ofFn values)

def structuralGF2ElementarySymmetric (codes : List Nat) (degree : Nat) : StructuralGF2Polynomial :=
  Ring.norm (codes.sublistsLen degree)

def structuralGF2ShiftedElementarySymmetric
    (codes : List ℕ) (offset degree : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2Sum <|
    (List.Nat.antidiagonal degree).map fun indices =>
      structuralGF2Scale
        ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : ZMod 2)
        (structuralGF2ElementarySymmetric codes indices.1)

def structuralGF2ConsecutiveWindowIndicator
    (codes : List ℕ) (offset width target : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2Sum <|
    (List.range (width + 1)).map fun degree =>
      structuralGF2Scale
        (SupplierWindow.triangularCoefficient
          (SupplierWindow.windowDelta target) degree)
        (structuralGF2ShiftedElementarySymmetric
          codes offset degree)

def structuralTerminalWindowPolynomial
    (depth population terminalWindow target : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2ConsecutiveWindowIndicator
    (terminalLiteralVariableCodes depth population)
    0 terminalWindow target

def structuralDeltaWindowPolynomial
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    StructuralGF2Polynomial :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  structuralGF2ConsecutiveWindowIndicator
    (deltaLiteralVariableCodes (population := population) level)
    (childCard - window level) (2 * window level) target

def structuralDeltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    StructuralGF2Polynomial :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  match deltaTarget? childCard (window level)
      parent.val child.val with
  | none => structuralGF2Zero
  | some target =>
      structuralDeltaWindowPolynomial label seed window level target

def structuralTerminalPolynomialVector
    (depth population terminalWindow : ℕ) :
    StructuralListPolynomialVector population :=
  fun candidate =>
    structuralTerminalWindowPolynomial depth population
      terminalWindow candidate.val

def structuralCombineListLevel
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population) :
    StructuralListPolynomialVector population :=
  fun parent =>
    structuralGF2Sum <|
      List.ofFn fun child : Fin (population + 1) =>
        structuralGF2Mul (childPolynomials child)
          (structuralDeltaFactor label seed window level parent child)

def structuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ) :
    StructuralListPolynomialVector population :=
  if hlevel : level < depth then
    structuralCombineListLevel label seed window ⟨level, hlevel⟩
      (structuralListPolynomialVectorFrom label seed window
        terminalWindow (level + 1))
  else
    structuralTerminalPolynomialVector depth population terminalWindow
termination_by depth - level
decreasing_by omega

def structuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ) :
    StructuralListPolynomialVector population :=
  structuralListPolynomialVectorFrom label seed window terminalWindow 0

def structuralMaskedCoordinate
    {population : ℕ} (mask : Finset (Fin population))
    (coordinate : Fin population) : StructuralGF2Polynomial :=
  if coordinate ∈ mask then
    structuralGF2Variable coordinate.val
  else
    structuralGF2Zero

def structuralListLiteralAtom
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    StructuralGF2Polynomial :=
  match decodeListLiteralVariable depth population code with
  | none => structuralGF2Zero
  | some (.terminal coordinate) =>
      if toeplitzHash (label coordinate) seed ∈
          zeroPrefixCell rank depth then
        structuralMaskedCoordinate mask coordinate
      else
        structuralGF2Zero
  | some (.delta level slot) =>
      match decodeListLiteralSlot slot with
      | .inl coordinate =>
          if toeplitzHash (label coordinate) seed ∈
              siblingPrefixCell rank level.val then
            structuralMaskedCoordinate mask coordinate
          else
            structuralGF2Zero
      | .inr coordinate =>
          if toeplitzHash (label coordinate) seed ∈
              zeroPrefixCell rank (level.val + 1) then
            structuralGF2Not
              (structuralMaskedCoordinate mask coordinate)
          else
            structuralGF2Zero

def structuralMaskedListCoordinate
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
  StructuralGF2Polynomial :=
  structuralGF2Substitute
    (structuralListLiteralAtom (depth := depth) mask label seed)
    (structuralListPolynomialVector label seed window
      terminalWindow candidate)

def structuralMaskedWalkListCoordinate
    {rank depth population t : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    StructuralGF2Polynomial :=
  structuralGF2BitMajority fun time =>
    structuralMaskedListCoordinate mask label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate

def structuralGF2ModularRadixRow
    {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot :
      Fin digits → Fin (populationBound + 1) →
        StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun code :
      Fin ((populationBound + 1) ^ digits) =>
    let tuple :=
      (finFunctionFinEquiv :
        (Fin digits → Fin (populationBound + 1)) ≃
          Fin ((populationBound + 1) ^ digits)).symm code
    if modularTupleAccepts modulus offset base tuple then
      structuralGF2FiniteConjunction fun digit =>
        oneHot digit (tuple digit)
    else
      structuralGF2Zero

end Normalized
end FixedLivePackets
