import Proof.SourceAssembly.SourceRequestMonomialSpec
import Proof.CaseAnalysis.RowsEstimatorCoefficientsProductRead
import Proof.CaseAnalysis.WitnessBoundedFields

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermReader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.CanonicalBinary NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients

/-- One raw term code → `(coefficient, circuit code)`. -/
def termOf (t : Nat) : Option (ℚ × Nat) :=
  match decodeTaggedList t with
  | some [a, b] => (decodeCanonicalRational a).map fun coef => (coef, b)
  | _ => none

/-- One guessed sum's raw term list from its code: `(coefficient, circuit code)` per term, in the sum's order. -/
def rawSum (code : Nat) : Option (List (ℚ × Nat)) :=
  match decodeTaggedList code with
  | some [_, termsCode] => (decodeBalancedList termsCode).bind fun ts => ts.mapM termOf
  | _ => none

/-- **The `j`-th proof variable's raw term list**, read off the witness's family field. -/
noncomputable def rawTerms (bits : List Bool) (j : Nat) : Option (List (ℚ × Nat)) :=
  (decodeBalancedList (RadixSemantics.value (RepairOrdinary.CloseoutWitness.BoundedFields.family bits))).bind
    fun cs => cs[j]?.bind rawSum

/-- **The term reader at ONE fixed machine** (cost a function of the witness and the two indices). Ports: `wT` witness,
`jT` variable index, `iT` term index, `widT`/`cwT` the resident widths `1^cwid`/`1^cw` (all read, kept); `cntT`, `codeT`,
`coefT` outputs; `Scr` its scratch. -/
def ReaderRun {U s : Nat} (M : Machine U s) (cost : List Bool → Nat → Nat → Nat) (cwid cw : Nat)
    (wT jT iT widT cwT cntT codeT coefT : Fin U) (Scr : Fin U → Prop) : Prop :=
  ∀ (bits : List Bool) (j i Rw R : Nat) (ts : List (ℚ × Nat)) (H : Fin U → Nat) (A : Fin U → List Bool),
    rawTerms bits j = some ts → ∀ _hi : i < ts.length,
    A wT = ZeroPadding.pad Rw (RepairOrdinary.frame bits) → H wT = 0 →
    A jT = ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word j) → H jT = 0 →
    A iT = ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word i) → H iT = 0 →
    A widT = ZeroPadding.pad R (List.replicate cwid true) → H widT = 0 →
    A cwT = ZeroPadding.pad R (List.replicate cw true) → H cwT = 0 →
    (∀ x, (Scr x ∨ x = cntT ∨ x = codeT ∨ x = coefT) → A x = List.replicate R false ∧ H x = 0) →
    cost bits j i + 1 ≤ R →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step M (cost bits j i) H A H' A' ∧
      A' cntT = ZeroPadding.pad R (List.replicate ts.length true) ∧ H' cntT = 0 ∧
      A' codeT = ZeroPadding.pad R (RepairOrdinary.frame (SignedSortKey.binary cwid ts[i].2)) ∧ H' codeT = 0 ∧
      A' coefT = ZeroPadding.pad R (Product.record cw ts[i].1) ∧ H' coefT = 0 ∧
      (∀ x, ¬ Scr x → x ≠ cntT → x ≠ codeT → x ≠ coefT → A' x = A x ∧ H' x = H x) ∧
      (∀ x, Scr x → (A' x).length ≤ R)

end NearCubicWires.SourceRequest.TermReader
