import Proof.CaseAnalysis.FinalWireEnvelope
import Proof.Amplification.CaseOneRecoveryAssembly

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields (stageArity stageTarget
  stageEntryWidth)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (primeCutoff listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope (unionWires atomWires
  unionRequestOf stageSeedEnvelope SiteDenFits siteDenFits_of_wireEnvelope envelopeFloor
  hfloor_at_envelopeFloor)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters decompositionOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom symLimits thrLimits
  symFamilyOf thrFamilyOf oracleOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier (DecodeUnion atomToUnion
  rightRequest unionTarget)
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Weakening the predicate. -/
theorem FactorsSatisfy.mono {A : Type} {degree : ℕ}
    {polynomial : CircuitPolynomial A degree} {P Q : A → Prop}
    (h : polynomial.FactorsSatisfy P) (hPQ : ∀ atom, P atom → Q atom) :
    polynomial.FactorsSatisfy Q :=
  fun monomial hmonomial atom hatom => hPQ atom (h monomial hmonomial atom hatom)

/-- **`coordinatePenalty`** (`Proof/CaseAnalysis/FinalExactness.lean`): the
paper's `(Enc_s - T)^2` on a systematic coordinate and `T^2 (1-T)^2` on an
auxiliary one.  The systematic branch is the only one that charges the
systematic atom, hence the only one that needs `hsystematic`. -/
theorem coordinatePenalty_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).FactorsSatisfy predicate := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    rw [coordinatePenalty, Fin.addCases_left]
    exact CircuitPolynomial.weaken_factorsSatisfy _ _ predicate
      (systematicValidityPolynomial_factorsSatisfy _ _ predicate (hsystematic index)
        (hcoordinate _))
  · intro index
    rw [coordinatePenalty, Fin.addCases_right]
    exact auxiliaryValidityPolynomial_factorsSatisfy _ predicate (hcoordinate _)

/-- **`penaltySite`** (`Proof/CaseAnalysis/FinalExactness.lean`). -/
theorem penaltySite_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (penaltySite pcpp coordinate systematicAtom i).FactorsSatisfy predicate := by
  unfold penaltySite
  exact CircuitPolynomial.scale_factorsSatisfy _ _ predicate
    (CircuitPolynomial.add_factorsSatisfy _ _ predicate
      (coordinatePenalty_factorsSatisfy pcpp coordinate systematicAtom predicate hcoordinate
        hsystematic _)
      (coordinatePenalty_factorsSatisfy pcpp coordinate systematicAtom predicate hcoordinate
        hsystematic _))

/-- **`momentSite`** (`Proof/CaseAnalysis/FinalExactness.lean`). -/
theorem momentSite_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (momentSite pcpp coordinate i).FactorsSatisfy predicate := by
  unfold momentSite
  exact CircuitPolynomial.weaken_factorsSatisfy _ _ predicate
    (secondMomentPolynomial_factorsSatisfy _ predicate (hcoordinate _))

/-- **`clauseSite`** (`Proof/CaseAnalysis/FinalExactness.lean`). -/
theorem clauseSite_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (clauseSite pcpp coordinate i).FactorsSatisfy predicate := by
  unfold clauseSite
  exact CircuitPolynomial.weaken_factorsSatisfy _ _ predicate
    (clausePolynomial_factorsSatisfy _ _ _ _ predicate (hcoordinate _) (hcoordinate _))

/-- **`sitePolynomial`** (`Proof/CaseAnalysis/FinalExactness.lean`), all three
phases. -/
theorem sitePolynomial_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial phase pcpp coordinate systematicAtom i).FactorsSatisfy predicate := by
  cases phase with
  | penalty =>
      show (penaltySite pcpp coordinate systematicAtom i).FactorsSatisfy predicate
      exact penaltySite_factorsSatisfy pcpp coordinate systematicAtom predicate hcoordinate
        hsystematic i
  | moment =>
      show (momentSite pcpp coordinate i).FactorsSatisfy predicate
      exact momentSite_factorsSatisfy pcpp coordinate predicate hcoordinate i
  | clause =>
      show (clauseSite pcpp coordinate i).FactorsSatisfy predicate
      exact clauseSite_factorsSatisfy pcpp coordinate predicate hcoordinate i

/-- **`siteCalls`** (`Proof/CaseAnalysis/FinalSupplierCalls.lean`) -- the
polynomial whose monomials the machine actually prints at one clause address.
The uniform `1 / 2 ^ clauseBits` touches no atom. -/
theorem siteCalls_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (address : Fin (2 ^ pcpp.clauseBits)) :
    (siteCalls phase pcpp coordinate systematicAtom address).FactorsSatisfy predicate := by
  unfold siteCalls
  exact CircuitPolynomial.scale_factorsSatisfy _ _ predicate
    (sitePolynomial_factorsSatisfy phase pcpp coordinate systematicAtom predicate hcoordinate
      hsystematic address)

/-! ## §2 The atom relabelling, and the arity transport -/

/-- `mapPolynomial` (`Proof/CaseAnalysis/FinalSumFamilyTransport.lean`) is a
pure list relabelling, so a predicate on the TARGET atoms is exactly the pulled
back predicate on the SOURCE atoms. -/
theorem mapPolynomial_factorsSatisfy {Source Target : Type} {degree : ℕ}
    (F : Source → Target) (polynomial : CircuitPolynomial Source degree)
    (predicate : Target → Prop)
    (h : polynomial.FactorsSatisfy (fun atom => predicate (F atom))) :
    (mapPolynomial F polynomial).FactorsSatisfy predicate := by
  intro monomial hmonomial atom hatom
  rcases List.mem_map.mp hmonomial with ⟨source, hsource, rfl⟩
  rcases List.mem_map.mp hatom with ⟨original, horiginal, rfl⟩
  exact h source hsource original horiginal

/-- The arity transport of a legal term list
(`Proof/CaseAnalysis/FinalExactnessFamily.lean`) does not touch the circuits,
so it does not touch their wire counts. -/
theorem wires_le_of_mem_transportTerms {Circuit : CanonicalWitnessCodec.CircuitFamily}
    (wires : {q : ℕ} → Circuit q → ℕ) {source target : ℕ} (harity : source = target)
    (terms : List (LegalCircuitTerm Circuit source)) (cap : ℕ)
    (hterms : ∀ term ∈ terms, wires term.circuit ≤ cap)
    (term : LegalCircuitTerm Circuit target) (hterm : term ∈ transportTerms harity terms) :
    wires term.circuit ≤ cap := by
  subst harity
  exact hterms term hterm

/-- **`CheckedLegalCircuitSum.wires_le` (`Proof/Circuits/CanonicalWitnessCodec.lean`),
TRANSPORTED to the coordinate polynomial.**  `wires_le` is set by the decoder's
own `if hwires …` guard (`:1650`), which IS `paper.tex:4292-4302`'s rejection
rule in Lean; `familyCoordinate`
(`Proof/CaseAnalysis/FinalExactnessFamily.lean`) carries exactly the terms of
the accepted sum, so every atom of every coordinate monomial clears the cap. -/
theorem familyCoordinate_factorsSatisfy_wires {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ} {limits : LegalSumLimits}
    {variableCount target : ℕ} (harity : limits.expectedArity = target)
    (family : SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    (familyCoordinate harity family i).FactorsSatisfy
      (fun c => wires c ≤ limits.wireCap) := by
  unfold familyCoordinate
  refine linearPolynomial_factorsSatisfy _ _ ?_
  intro term hterm
  exact wires_le_of_mem_transportTerms wires _ (family.getSum i).value.terms limits.wireCap
    (family.getSum i).wires_le term hterm

/-! ## §3 `atomWires` on the two guessed constructors -/

/-- `atomWires` on a guessed symmetric atom is that circuit's own wire count:
`atomToUnion` sends it to `Sum.inl` untouched. -/
theorem atomWires_symmetric {N : ℕ} {circuit : BooleanCircuit N}
    {pcpp : PointwisePCPP circuit} (atom : NormalizedSymmetricThresholdCircuit N) :
    atomWires (Atom.symmetric atom : Atom pcpp) = atom.wireCount := rfl

/-- `atomWires` on a guessed threshold atom is that circuit's own wire count. -/
theorem atomWires_threshold {N : ℕ} {circuit : BooleanCircuit N}
    {pcpp : PointwisePCPP circuit} (atom : NormalizedThresholdThresholdCircuit N) :
    atomWires (Atom.threshold atom : Atom pcpp) = atom.wireCount := rfl

/-! ## §4 `atomWires` on the SYSTEMATIC constructor

`paper.tex:4303-4305` compiles the systematic parity deterministically into the
native parity circuit, so its envelope is not guessed and needs no decoder
guard: it is computed, and it is bounded by the arity outright. -/

/-- The one-bit gate reads exactly one coordinate, so it charges one wire. -/
theorem inputBitSupportedGate_wireCount {N : ℕ} (coordinate : Fin N) :
    (inputBitSupportedGate coordinate).wireCount = 1 := by
  unfold SupportedNormalizedGate.wireCount inputBitSupportedGate
  simp

/-- **The native parity circuit's wire count, exactly**: one identity bottom per
supported coordinate, each charged its own wire plus its edge into the top
table. -/
theorem normalizedParityCircuit_wireCount {N : ℕ} (support : Finset (Fin N)) :
    (normalizedParityCircuit support).wireCount = 2 * support.card := by
  unfold NormalizedSymmetricThresholdCircuit.wireCount normalizedParityCircuit
  simp only [inputBitSupportedGate_wireCount, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

/-- **The systematic atom clears the arity.**  `PointwisePCPP.systematicSupportBound`
(`Proof/Foundations/SourceInterfaces.lean`) caps each systematic support at
`N / 2`, and the parity circuit charges two wires per supported coordinate, so
the native parity atom never exceeds `N` wires.  No guessed description, and no
hypothesis. -/
theorem atomWires_systematic_le {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit) (index : Fin pcpp.systematicBits) :
    atomWires (Atom.systematic index : Atom pcpp) ≤ N := by
  have hcard : (pcpp.systematicSupport index).card ≤ N / 2 :=
    pcpp.systematicSupportBound index
  have hwires : atomWires (Atom.systematic index : Atom pcpp)
      = 2 * (pcpp.systematicSupport index).card :=
    normalizedParityCircuit_wireCount (pcpp.systematicSupport index)
  omega

/-! ## §5 The route's own cap, and the deliverable -/

noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- **The per-atom wire envelope the route already has.**  Nothing is chosen
here: the two guessed branches are capped by `C10TotalDecode.symLimits`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) and `thrLimits` (`:102`), which
are `paper.tex:800-807`'s own `n^3/L^5` and `n^3/L^9`; the systematic branch is
capped by the arity through `§4`.  Every summand depends on the input LENGTH
alone -- not on the input, not on the guessed witness, not on the oracle --
which is the witness-uniformity the consumer's `wireCap : ℕ → ℕ` demands. -/
def envelopeCap (n : ℕ) : ℕ :=
  max (stageArity sources k n)
    (max ⌊wireScale 1 5 ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)⌋₊
      ⌊wireScale 1 9 ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)⌋₊)

variable {n : ℕ} (x : BitInput n)
  (oracle : BooleanCircuit
    ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- The symmetric branch's wire cap is `paper.tex:800-802`'s `n^3/L^5`, on the
nose and at every input and oracle. -/
theorem symLimits_wireCap :
    (symLimits sources k (PolynomialClock.ordinaryClock k) p x oracle).wireCap =
      ⌊wireScale 1 5
        ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)⌋₊ := rfl

/-- The threshold branch's wire cap is `paper.tex:804-806`'s `n^3/L^9`. -/
theorem thrLimits_wireCap :
    (thrLimits sources k (PolynomialClock.ordinaryClock k) p x oracle).wireCap =
      ⌊wireScale 1 9
        ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)⌋₊ := rfl

/-- **The decoded coordinate obeys the envelope, on BOTH branches, with no
hypothesis.**  This is `wires_le` carried through `familyCoordinate` and the
decode relabelling -- the exact analogue of `polynomialFits_decodeCoordinate`
(`Proof/CaseAnalysis/FinalSumFamilyTransport.lean`) and
`decodeCoordinate_coefficientMass_le` (`:422`) for the third cap of
`paper.tex:4292-4302`. -/
theorem decodeCoordinate_factorsSatisfy_atomWires
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k
      (PolynomialClock.ordinaryClock k) x oracle)) :
    (decodeCoordinate sources k (PolynomialClock.ordinaryClock k) p x oracle bits j).FactorsSatisfy
      (fun atom => atomWires atom ≤ envelopeCap sources k n) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [decodeCoordinate_sym sources k (PolynomialClock.ordinaryClock k) p x oracle bits hs j]
    refine mapPolynomial_factorsSatisfy _ _ _ ?_
    refine FactorsSatisfy.mono (familyCoordinate_factorsSatisfy_wires rfl
      (symFamilyOf sources k (PolynomialClock.ordinaryClock k) p x oracle bits) j) ?_
    intro atom hatom
    have hcap : (symLimits sources k (PolynomialClock.ordinaryClock k) p x oracle).wireCap ≤
        envelopeCap sources k n := by
      unfold envelopeCap
      rw [symLimits_wireCap sources k p x oracle]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans hatom hcap
  · rw [decodeCoordinate_thr sources k (PolynomialClock.ordinaryClock k) p x oracle bits hs j]
    refine mapPolynomial_factorsSatisfy _ _ _ ?_
    refine FactorsSatisfy.mono (familyCoordinate_factorsSatisfy_wires rfl
      (thrFamilyOf sources k (PolynomialClock.ordinaryClock k) p x oracle bits) j) ?_
    intro atom hatom
    have hcap : (thrLimits sources k (PolynomialClock.ordinaryClock k) p x oracle).wireCap ≤
        envelopeCap sources k n := by
      unfold envelopeCap
      rw [thrLimits_wireCap sources k p x oracle]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact le_trans hatom hcap

/-- The systematic atom clears `envelopeCap` at the route's own atom type: its
arity IS `stageArity sources k n` (`Proof/CaseAnalysis/FinalStageFields.lean`),
and that is the first summand of the cap. -/
theorem atomWires_systematic_le_envelopeCap
    (index : Fin (pcppOf sources k p x bits).systematicBits) :
    atomWires (Atom.systematic index : Atoms sources k p x bits) ≤ envelopeCap sources k n :=
  le_trans (atomWires_systematic_le (pcppOf sources k p x bits) index) (le_max_left _ _)

/-- **HENV, DISCHARGED.**  The `henv` binder of `siteDenFits_of_wireEnvelope`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`), verbatim, at
`wireCap := envelopeCap sources k`: every atom the machine actually prints at
every phase, clause address and monomial respects the per-atom wire envelope.
The membership premise is the paper's rejection rule -- see the header. -/
theorem henv_at_envelopeCap :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase)
      (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
      ∀ atom ∈ monomial.factors, atomWires atom ≤ envelopeCap sources k n := by
  intro m y record ph address monomial hmonomial
  refine siteCalls_factorsSatisfy ph (pcppOf sources k p y record)
    (stageCoordinate sources k p m y record) Atom.systematic _ ?_ ?_ address monomial hmonomial
  · intro j
    exact decodeCoordinate_factorsSatisfy_atomWires sources k p y
      (oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree m record) record j
  · intro i
    exact atomWires_systematic_le_envelopeCap sources k p y record i

theorem envelopeCap_le_cube (m : ℕ) :
    envelopeCap sources k m ≤
      max (stageArity sources k m)
        ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth m ^ 3) := by
  have hsym : ⌊wireScale 1 5
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth m)⌋₊ ≤
      (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth m ^ 3 :=
    CaseOneRecoveryAssembly.wireScale_floor_le_cube (by norm_num) le_rfl 5 _
  have hthr : ⌊wireScale 1 9
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth m)⌋₊ ≤
      (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth m ^ 3 :=
    CaseOneRecoveryAssembly.wireScale_floor_le_cube (by norm_num) le_rfl 9 _
  unfold envelopeCap
  omega

/-- The same statement in the shape a width consumer wants: one bound covering
all three constructors. -/
theorem envelopeCap_le_sum (m : ℕ) :
    envelopeCap sources k m ≤
      stageArity sources k m +
        (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth m ^ 3 :=
  le_trans (envelopeCap_le_cube sources k m) (max_le (Nat.le_add_right _ _)
    (Nat.le_add_left _ _))

/-- **The membership-guarded `hden`, with the envelope DISCHARGED.** -/
theorem siteDenFits_of_envelopeCap (liveScale : ℕ)
    (coefficientFloor primeBits thrDenBound : ℕ → ℕ)
    (hfloor : ∀ m, stageArity sources k m +
      stageSeedEnvelope sources k p (envelopeCap sources k) primeBits thrDenBound m + 1 ≤
      stageEntryWidth sources k p coefficientFloor m)
    (hprime : ∀ (m : ℕ) (y : BitInput m) (record : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p y record) 4),
      (primesUpTo (primeCutoff (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p y record monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k m)))).card ≤
        2 ^ primeBits m)
    (hthrden : ∀ (m : ℕ) (y : BitInput m) (record : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p y record) 4),
      listDenominator (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p y record monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k m)) ≤ thrDenBound m) :
    SiteDenFits sources k p liveScale coefficientFloor :=
  siteDenFits_of_wireEnvelope sources k p liveScale coefficientFloor (envelopeCap sources k)
    primeBits thrDenBound hfloor (henv_at_envelopeCap sources k p) hprime hthrden

theorem siteDenFits_at_envelopeFloor (liveScale : ℕ) (primeBits thrDenBound : ℕ → ℕ)
    (hprime : ∀ (m : ℕ) (y : BitInput m) (record : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p y record) 4),
      (primesUpTo (primeCutoff (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p y record monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k m)))).card ≤
        2 ^ primeBits m)
    (hthrden : ∀ (m : ℕ) (y : BitInput m) (record : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p y record) 4),
      listDenominator (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p y record monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k m)) ≤ thrDenBound m) :
    SiteDenFits sources k p liveScale
      (envelopeFloor sources k p (envelopeCap sources k) primeBits thrDenBound) :=
  siteDenFits_of_envelopeCap sources k p liveScale
    (envelopeFloor sources k p (envelopeCap sources k) primeBits thrDenBound)
    primeBits thrDenBound
    (hfloor_at_envelopeFloor sources k p (envelopeCap sources k) primeBits thrDenBound)
    hprime hthrden

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
