import Proof.CaseAnalysis.FinalStageJoin

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy (rowDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (thresholdRows primeCutoff
  listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf decompositionOf
  expanderOf primeOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (seedExponent walkExponent
  rowCount_eq_two_pow card_walkSample)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo PrimeIndex)
open NearCubicWires.SupplierTouching (touchingCost touchIndicator)
open NearCubicWires.SupplierWalkBridge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The per-atom wire envelope, as a number

`paper.tex:4296` charges the envelope PER ATOM, so the Lean quantity is one
natural number per atom.  Both target classes already carry a `wireCount`
(`Proof/Foundations/SupplierPipeline.lean` and `:357`), and the systematic
constructor's envelope is the wire count of the native parity circuit
`atomToUnion` compiles it into (`paper.tex:4303`: "Systematic parities are
source-explicit and are compiled deterministically into the native parity
circuits"), so ONE definition covers all three constructors. -/

/-- The wire count of a decode-union circuit, either branch. -/
def unionWires {N : ℕ} : DecodeUnion N → ℕ
  | Sum.inl circuit => circuit.wireCount
  | Sum.inr circuit => circuit.wireCount

/-- **The per-atom wire envelope quantity of `paper.tex:4296`.**  Charged
through `atomToUnion` (`Proof/CaseAnalysis/FinalUnionSupplier.lean`) so the
systematic constructor is charged for the native parity circuit it compiles to
and nothing is charged twice. -/
def atomWires {N : ℕ} {circuit : BooleanCircuit N} {pcpp : PointwisePCPP circuit}
    (atom : Atom pcpp) : ℕ :=
  unionWires (atomToUnion atom)

/-! ## §2 Wires dominate the occurrence population, in both classes

This is the bridge the envelope has to cross: `seedExponent`'s first argument is
an occurrence-list LENGTH, and the envelope is a WIRE COUNT. -/

/-- Symmetric: the retained bottom occurrences number `bottomCount`, and every
bottom gate is charged at least one wire. -/
theorem symmetricCircuitOccurrences_length_le {q : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit q) :
    (symmetricCircuitOccurrences circuit).length ≤ circuit.wireCount := by
  unfold symmetricCircuitOccurrences NormalizedSymmetricThresholdCircuit.wireCount
  rw [List.length_ofFn]
  calc circuit.bottomCount = ∑ _index : Fin circuit.bottomCount, 1 := by simp
    _ ≤ ∑ index, ((circuit.bottom index).wireCount + 1) :=
        Finset.sum_le_sum (fun index _ => Nat.le_add_left 1 _)

/-- Threshold: the retained occurrences number `top.support.card`, and every
retained top occurrence is charged at least one wire. -/
theorem thresholdCircuitOccurrences_length_le {q : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit q) :
    (thresholdCircuitOccurrences circuit).length ≤ circuit.wireCount := by
  unfold thresholdCircuitOccurrences NormalizedThresholdThresholdCircuit.wireCount
  rw [List.length_ofFn]
  calc circuit.top.support.card = ∑ _index ∈ circuit.top.support, 1 := by simp
    _ ≤ ∑ index ∈ circuit.top.support, ((circuit.bottom index).wireCount + 1) :=
        Finset.sum_le_sum (fun index _ => Nat.le_add_left 1 _)

/-! ## §3 The two branch populations, from the envelope alone -/

theorem leftCircuits_length_le {N : ℕ} (us : List (DecodeUnion N)) :
    (leftCircuits us).length ≤ us.length := by
  induction us with
  | nil => simp [leftCircuits]
  | cons u rest ih =>
      cases u with
      | inl circuit => simpa [leftCircuits] using Nat.succ_le_succ ih
      | inr circuit => simpa [leftCircuits] using ih.trans (Nat.le_succ _)

theorem rightCircuits_length_le {N : ℕ} (us : List (DecodeUnion N)) :
    (rightCircuits us).length ≤ us.length := by
  induction us with
  | nil => simp [rightCircuits]
  | cons u rest ih =>
      cases u with
      | inl circuit => simpa [rightCircuits] using ih.trans (Nat.le_succ _)
      | inr circuit => simpa [rightCircuits] using Nat.succ_le_succ ih

/-- **The symmetric occurrence population is at most `#atoms * envelope`.** -/
theorem symPopulation_le {N : ℕ} (cap : ℕ) :
    ∀ us : List (DecodeUnion N), (∀ u ∈ us, unionWires u ≤ cap) →
      ((leftCircuits us).flatMap symmetricCircuitOccurrences).length ≤ us.length * cap := by
  intro us
  induction us with
  | nil => intro _; simp [leftCircuits]
  | cons u rest ih =>
      intro henv
      have hrest := ih (fun v hv => henv v (List.mem_cons_of_mem _ hv))
      have hhead := henv u (List.mem_cons_self ..)
      cases u with
      | inl circuit =>
          have hcircuit : (symmetricCircuitOccurrences circuit).length ≤ cap :=
            le_trans (symmetricCircuitOccurrences_length_le circuit) hhead
          have hstep : rest.length * cap + cap = (rest.length + 1) * cap := by ring
          simp only [leftCircuits, List.flatMap_cons, List.length_append, List.length_cons]
          omega
      | inr circuit =>
          have hstep : rest.length * cap ≤ (rest.length + 1) * cap :=
            Nat.mul_le_mul_right _ (Nat.le_succ _)
          simp only [leftCircuits, List.length_cons]
          omega

/-- **The threshold occurrence population is at most `#atoms * envelope`.** -/
theorem thrPopulation_le {N : ℕ} (cap : ℕ) :
    ∀ us : List (DecodeUnion N), (∀ u ∈ us, unionWires u ≤ cap) →
      ((rightCircuits us).flatMap thresholdCircuitOccurrences).length ≤ us.length * cap := by
  intro us
  induction us with
  | nil => intro _; simp [rightCircuits]
  | cons u rest ih =>
      intro henv
      have hrest := ih (fun v hv => henv v (List.mem_cons_of_mem _ hv))
      have hhead := henv u (List.mem_cons_self ..)
      cases u with
      | inl circuit =>
          have hstep : rest.length * cap ≤ (rest.length + 1) * cap :=
            Nat.mul_le_mul_right _ (Nat.le_succ _)
          simp only [rightCircuits, List.length_cons]
          omega
      | inr circuit =>
          have hcircuit : (thresholdCircuitOccurrences circuit).length ≤ cap :=
            le_trans (thresholdCircuitOccurrences_length_le circuit) hhead
          have hstep : rest.length * cap + cap = (rest.length + 1) * cap := by ring
          simp only [rightCircuits, List.flatMap_cons, List.length_append, List.length_cons]
          omega

/-- Monotone envelope for one canonical walk-seed exponent. -/
def seedEnvelope (popBound touchBound denBound : ℕ) : ℕ :=
  3 * max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) + 1 +
    320 * Nat.clog 2 (denBound + 1)

theorem canonicalGradedRank_mono {population activeBound popBound touchBound : ℕ}
    (hpop : population ≤ popBound) (htouch : activeBound ≤ touchBound) :
    canonicalGradedRank population activeBound ≤
      max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) := by
  unfold canonicalGradedRank canonicalGradedDepth
  exact max_le_max (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 256 htouch))
    (Nat.clog_mono_right 2 hpop)

/-- **The walk-seed exponent is `O(log)` of its three arguments.** -/
theorem walkExponent_le_seedEnvelope
    {population activeBound denominator popBound touchBound denBound : ℕ}
    (hpop : population ≤ popBound) (htouch : activeBound ≤ touchBound)
    (hden : denominator ≤ denBound) :
    walkExponent (toeplitzWalkSideBits (canonicalGradedRank population activeBound))
        denominator ≤ seedEnvelope popBound touchBound denBound := by
  unfold walkExponent seedEnvelope
  have hrank := canonicalGradedRank_mono hpop htouch
  have hside : 2 * toeplitzWalkSideBits (canonicalGradedRank population activeBound) ≤
      3 * canonicalGradedRank population activeBound + 1 :=
    le_trans (twice_toeplitzWalkSideBits_le _)
      (Nat.add_le_add_right (toeplitzSeedBits_le_three_mul _) 1)
  have hleft : 2 * toeplitzWalkSideBits (canonicalGradedRank population activeBound) ≤
      3 * max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) + 1 :=
    le_trans hside (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hrank) 1)
  have hdenLog : Nat.clog 2 (denominator + 1) ≤ Nat.clog 2 (denBound + 1) :=
    Nat.clog_mono_right 2 (Nat.add_le_add_right hden 1)
  omega

theorem seedEnvelope_mono {popBound touchBound denBound popLarger touchLarger denLarger : ℕ}
    (hpop : popBound ≤ popLarger) (htouch : touchBound ≤ touchLarger)
    (hden : denBound ≤ denLarger) :
    seedEnvelope popBound touchBound denBound ≤
      seedEnvelope popLarger touchLarger denLarger := by
  unfold seedEnvelope
  refine Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 3 ?_) 1)
    (Nat.mul_le_mul_left 320 (Nat.clog_mono_right 2 (Nat.add_le_add_right hden 1)))
  exact max_le_max (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 256 htouch))
    (Nat.clog_mono_right 2 hpop)

/-- The touching cost never exceeds the occurrence population: it is a sum of
indicators over the occurrence index type. -/
theorem touchingCost_le_length {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) :
    touchingCost (occurrenceSupport occurrences) selected ≤ occurrences.length := by
  unfold touchingCost touchIndicator
  calc (∑ gate : Fin occurrences.length,
        if Disjoint selected (occurrenceSupport occurrences gate) then 0 else 1) ≤
        ∑ _gate : Fin occurrences.length, 1 := by
        refine Finset.sum_le_sum ?_
        intro gate _hgate
        split <;> omega
    _ = occurrences.length := by simp

/-- **The envelope is linear in the bit lengths of its arguments.** -/
theorem seedEnvelope_le_of_bits {popBound touchBound denBound popBits touchBits denBits : ℕ}
    (hpop : popBound ≤ 2 ^ popBits) (htouch : touchBound ≤ 2 ^ touchBits)
    (hden : denBound + 1 ≤ 2 ^ denBits) :
    seedEnvelope popBound touchBound denBound ≤
      3 * (8 + touchBits + popBits) + 1 + 320 * denBits := by
  unfold seedEnvelope
  have hpopLog : Nat.clog 2 popBound ≤ popBits := by
    calc Nat.clog 2 popBound ≤ Nat.clog 2 (2 ^ popBits) := Nat.clog_mono_right 2 hpop
      _ = popBits := Nat.clog_pow 2 popBits (by norm_num)
  have htouchLog : Nat.clog 2 (256 * touchBound) ≤ 8 + touchBits := by
    calc Nat.clog 2 (256 * touchBound) ≤ Nat.clog 2 (2 ^ (8 + touchBits)) := by
          refine Nat.clog_mono_right 2 ?_
          calc 256 * touchBound ≤ 256 * 2 ^ touchBits := Nat.mul_le_mul_left 256 htouch
            _ = 2 ^ (8 + touchBits) := by rw [pow_add]; norm_num
      _ = 8 + touchBits := Nat.clog_pow 2 (8 + touchBits) (by norm_num)
  have hdenLog : Nat.clog 2 (denBound + 1) ≤ denBits := by
    calc Nat.clog 2 (denBound + 1) ≤ Nat.clog 2 (2 ^ denBits) := Nat.clog_mono_right 2 hden
      _ = denBits := Nat.clog_pow 2 denBits (by norm_num)
  have hmax : max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) ≤
      8 + touchBits + popBits := max_le (by omega) (by omega)
  omega

/-! ## §5 The two branch row counts

The SYM factor is a pure power of two; the THR factor is a prime window times a
power of two.  Both exponents are `seedEnvelope`s. -/

/-- **The SYM factor.** -/
theorem symRowCount_le (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) {q : ℕ} (us : List (DecodeUnion q)) (popBound denBound : ℕ)
    (hpop : ((leftCircuits us).flatMap symmetricCircuitOccurrences).length ≤ popBound)
    (hden : (leftCircuits us).length * (target q + 1) ≤ denBound) :
    (symmetricFourfoldRows spectrum liveScale target).rowCount
        (leftRequest (⟨q, us⟩ : FourfoldRequest DecodeUnion)) ≤
      2 ^ seedEnvelope popBound popBound denBound := by
  rw [rowCount_eq_two_pow]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  unfold seedExponent
  exact walkExponent_le_seedEnvelope hpop
    (le_trans (touchingCost_le_length _ _) hpop) hden

/-- The THR row count is the cardinality the preprocessor's own field names. -/
theorem thrRowCount_eq (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm) (liveScale : ℕ)
    (target : ℕ → ℕ) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (thresholdRows spectrum theta a liveScale target).rowCount r =
      Fintype.card (PrimeIndex (primeCutoff a r (target r.q)) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r (target r.q))) := by
  unfold thresholdRows
  rfl

/-- **The THR factor.**  One prime window on top of the same seed envelope.
`primesUpTo` is a filter of `Finset.range (cutoff + 1)`, so the window is
bounded by its cutoff; the bound is taken here in the dyadic form the width
ledger consumes. -/
theorem thrRowCount_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm) (liveScale : ℕ)
    (target : ℕ → ℕ) {q : ℕ} (us : List (DecodeUnion q))
    (popBound denBound primeBits : ℕ)
    (hpop : ((rightCircuits us).flatMap thresholdCircuitOccurrences).length ≤ popBound)
    (hprime : (primesUpTo (primeCutoff a
      (rightRequest (⟨q, us⟩ : FourfoldRequest DecodeUnion)) (target q))).card ≤
      2 ^ primeBits)
    (hden : listDenominator a (rightRequest (⟨q, us⟩ : FourfoldRequest DecodeUnion))
      (target q) ≤ denBound) :
    (thresholdRows spectrum theta a liveScale target).rowCount
        (rightRequest (⟨q, us⟩ : FourfoldRequest DecodeUnion)) ≤
      2 ^ (primeBits + seedEnvelope popBound popBound denBound) := by
  rw [thrRowCount_eq, Fintype.card_prod, Fintype.card_coe, card_walkSample, pow_add]
  refine Nat.mul_le_mul hprime (Nat.pow_le_pow_right (by norm_num) ?_)
  exact walkExponent_le_seedEnvelope hpop
    (le_trans (touchingCost_le_length _ _) hpop) hden

/-- **The primes-up-to window never exceeds its cutoff.**  Available to a caller
that prefers the cutoff form of `hprime` above. -/
theorem primesUpTo_card_le (cutoff : ℕ) : (primesUpTo cutoff).card ≤ cutoff + 1 := by
  unfold primesUpTo
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_range]

/-! ## §6 The union row count and `stageDen`, from the envelope

`unionAtomRows`' count is the PRODUCT (`unionAtomRows_rowCount`,
`Proof/CaseAnalysis/FinalUnionSupplier.lean`), so both §5 bounds are needed.
`stageDen` (`Proof/CaseAnalysis/FinalStageFields.lean`) is that count times
`2 ^ q` -- A.13.9's `|\mathcal E| 2^q` (`paper.tex:3161`). -/

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- The request the union rows are asked at, at one monomial. -/
def unionRequestOf {n : ℕ} (x : BitInput n) (bits : List Bool)
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4) :
    FourfoldRequest DecodeUnion :=
  ⟨stageArity sources k n, monomial.factors.map atomToUnion⟩

/-- **The external-row envelope of A.8, at the route's own union rows.**  Three
summands and no more: the symmetric walk seed, the threshold prime window, the
threshold walk seed.  `paper.tex:2253` calls the whole of it `h_D L_q`. -/
def stageSeedEnvelope (wireCap primeBits thrDenBound : ℕ → ℕ) (n : ℕ) : ℕ :=
  seedEnvelope (4 * wireCap n) (4 * wireCap n)
      (4 * (unionTarget (stageTarget sources p) (stageArity sources k n) + 1)) +
    (primeBits n + seedEnvelope (4 * wireCap n) (4 * wireCap n) (thrDenBound n))

/-- **The union row count, bounded by the per-atom wire envelope.**  Both
factors, as owed. -/
theorem unionAtomRows_rowCount_le_of_envelope (liveScale : ℕ)
    (wireCap primeBits thrDenBound : ℕ → ℕ) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (henv : ∀ atom ∈ monomial.factors, atomWires atom ≤ wireCap n)
    (hprime : (primesUpTo (primeCutoff (decompositionOf sources)
      (rightRequest (unionRequestOf sources k p x bits monomial))
      (unionTarget (stageTarget sources p) (stageArity sources k n)))).card ≤
      2 ^ primeBits n)
    (hthrden : listDenominator (decompositionOf sources)
      (rightRequest (unionRequestOf sources k p x bits monomial))
      (unionTarget (stageTarget sources p) (stageArity sources k n)) ≤ thrDenBound n) :
    (unionAtomRows sources liveScale (stageTarget sources p)).rowCount
        (unionRequestOf sources k p x bits monomial) ≤
      2 ^ stageSeedEnvelope sources k p wireCap primeBits thrDenBound n := by
  classical
  set us : List (DecodeUnion (stageArity sources k n)) := monomial.factors.map atomToUnion
    with hus
  have hlen : us.length ≤ 4 := by
    rw [hus, List.length_map]
    exact monomial.degree_le
  have hunion : ∀ u ∈ us, unionWires u ≤ wireCap n := by
    intro u hu
    rw [hus] at hu
    obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hu
    exact henv atom hatom
  have hsym : ((leftCircuits us).flatMap symmetricCircuitOccurrences).length ≤
      4 * wireCap n :=
    le_trans (symPopulation_le (wireCap n) us hunion)
      (Nat.mul_le_mul_right _ hlen)
  have hthr : ((rightCircuits us).flatMap thresholdCircuitOccurrences).length ≤
      4 * wireCap n :=
    le_trans (thrPopulation_le (wireCap n) us hunion)
      (Nat.mul_le_mul_right _ hlen)
  have hsymden : (leftCircuits us).length *
      (unionTarget (stageTarget sources p) (stageArity sources k n) + 1) ≤
      4 * (unionTarget (stageTarget sources p) (stageArity sources k n) + 1) :=
    Nat.mul_le_mul_right _ (le_trans (leftCircuits_length_le us) hlen)
  rw [unionAtomRows_rowCount, stageSeedEnvelope, pow_add]
  exact Nat.mul_le_mul
    (symRowCount_le (expanderOf sources) liveScale
      (unionTarget (stageTarget sources p)) us _ _ hsym hsymden)
    (thrRowCount_le (expanderOf sources) (primeOf sources) (decompositionOf sources)
      liveScale (unionTarget (stageTarget sources p)) us _ _ _ hthr hprime hthrden)

/-- **`ebound`'S ARITHMETIC, AT ONE MONOMIAL, FROM THE ENVELOPE.**  This is the
statement the route needs and the one thing the atom type cannot supply on its
own: `stageDen` -- A.13.9's `|\mathcal E| 2^q` -- fits the stage entry width for
every monomial whose atoms clear `paper.tex:4296`'s per-atom wire envelope.
The `hfloor` premise is EXACTFRAC's re-keyed Floor 3, at the external-row
exponent A.8:2253 budgets rather than at a constant. -/
theorem stageDen_lt_of_wireEnvelope (liveScale : ℕ)
    (coefficientFloor wireCap primeBits thrDenBound : ℕ → ℕ)
    (hfloor : ∀ n, stageArity sources k n +
      stageSeedEnvelope sources k p wireCap primeBits thrDenBound n + 1 ≤
      stageEntryWidth sources k p coefficientFloor n)
    {n : ℕ} (x : BitInput n) (bits : List Bool)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (henv : ∀ atom ∈ monomial.factors, atomWires atom ≤ wireCap n)
    (hprime : (primesUpTo (primeCutoff (decompositionOf sources)
      (rightRequest (unionRequestOf sources k p x bits monomial))
      (unionTarget (stageTarget sources p) (stageArity sources k n)))).card ≤
      2 ^ primeBits n)
    (hthrden : listDenominator (decompositionOf sources)
      (rightRequest (unionRequestOf sources k p x bits monomial))
      (unionTarget (stageTarget sources p) (stageArity sources k n)) ≤ thrDenBound n) :
    stageDen sources k p liveScale n x bits address monomial <
      2 ^ stageEntryWidth sources k p coefficientFloor n := by
  have hrow := unionAtomRows_rowCount_le_of_envelope sources k p liveScale wireCap primeBits
    thrDenBound x bits monomial henv hprime hthrden
  have hle : stageDen sources k p liveScale n x bits address monomial ≤
      2 ^ stageSeedEnvelope sources k p wireCap primeBits thrDenBound n *
        2 ^ stageArity sources k n :=
    Nat.mul_le_mul_right _ hrow
  have hmul : 2 ^ stageSeedEnvelope sources k p wireCap primeBits thrDenBound n *
      2 ^ stageArity sources k n =
      2 ^ (stageArity sources k n +
        stageSeedEnvelope sources k p wireCap primeBits thrDenBound n) := by
    rw [← Nat.pow_add, Nat.add_comm]
  have hstep : 2 ^ stageSeedEnvelope sources k p wireCap primeBits thrDenBound n *
      2 ^ stageArity sources k n <
      2 ^ stageEntryWidth sources k p coefficientFloor n := by
    rw [hmul]
    exact Nat.pow_lt_pow_right (by norm_num)
      (lt_of_lt_of_le (Nat.lt_succ_self _) (hfloor n))
  exact lt_of_le_of_lt hle hstep

/-- **RESOURCE VERDICT, at the route's own external-row exponent.**  One
residual cell: `stageSeedEnvelope` is bounded by a fixed linear function of the
bit lengths of the wire envelope, the requested accuracy denominator and the
threshold list denominator, plus the prime-window bit count.  Every one of those
is `O(L_q)` exactly when the wire envelope is polynomial, so the whole
external-row exponent is `paper.tex:2253`'s `h_D L_q` and nothing more. -/
theorem stageSeedEnvelope_le_of_bits (wireCap primeBits thrDenBound : ℕ → ℕ)
    (wireBits targetBits thrDenBits : ℕ → ℕ) (n : ℕ)
    (hwire : 4 * wireCap n ≤ 2 ^ wireBits n)
    (htarget : 4 * (unionTarget (stageTarget sources p) (stageArity sources k n) + 1) + 1 ≤
      2 ^ targetBits n)
    (hthr : thrDenBound n + 1 ≤ 2 ^ thrDenBits n) :
    stageSeedEnvelope sources k p wireCap primeBits thrDenBound n ≤
      6 * (8 + wireBits n + wireBits n) + 2 + primeBits n +
        320 * (targetBits n + thrDenBits n) := by
  unfold stageSeedEnvelope
  have hsym := seedEnvelope_le_of_bits (popBits := wireBits n) (touchBits := wireBits n)
    (denBits := targetBits n) hwire hwire htarget
  have hthrEnv := seedEnvelope_le_of_bits (popBits := wireBits n) (touchBits := wireBits n)
    (denBits := thrDenBits n) hwire hwire hthr
  omega

/-! ## §7 The membership-guarded field -- what the record stream actually needs

`phaseRecords'_valid` (`Proof/CaseAnalysis/FinalExactFraction.lean`)
takes its per-record premise as
`∀ address monomial, monomial ∈ (siteCalls …).monomials → Entry.Valid …`.
The MEMBERSHIP is the paper's rejection rule in Lean: the machine only ever
prints monomials of the description it accepted, and an accepted description
clears the per-atom wire envelope.  `exactFraction_records_valid` (`:188`)
discards that membership and re-quantifies over the whole monomial type; from
there it is re-quantified again in `StageBlock'.hden`
(`Proof/CaseAnalysis/FinalExactStagePackage.lean`).

`SiteDenFits` below is the field as `phaseRecords'_valid` consumes it, and
`siteDenFits_of_wireEnvelope` discharges it from the envelope. -/

/-- **The membership-guarded `hden`.** -/
def SiteDenFits (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
      stageDen sources k p liveScale n x bits address monomial <
        2 ^ stageEntryWidth sources k p coefficientFloor n

/-- **The membership-guarded field, DISCHARGED from the per-atom wire
envelope.**  The envelope is demanded only of the atoms the machine actually
prints -- exactly the scope `paper.tex:4292-4302`'s rejection rule has. -/
theorem siteDenFits_of_wireEnvelope (liveScale : ℕ)
    (coefficientFloor wireCap primeBits thrDenBound : ℕ → ℕ)
    (hfloor : ∀ n, stageArity sources k n +
      stageSeedEnvelope sources k p wireCap primeBits thrDenBound n + 1 ≤
      stageEntryWidth sources k p coefficientFloor n)
    (henv : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase)
      (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
      ∀ atom ∈ monomial.factors, atomWires atom ≤ wireCap n)
    (hprime : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      (primesUpTo (primeCutoff (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p x bits monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k n)))).card ≤
        2 ^ primeBits n)
    (hthrden : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      listDenominator (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p x bits monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k n)) ≤ thrDenBound n) :
    SiteDenFits sources k p liveScale coefficientFloor :=
  fun n x bits _hn ph address monomial hmonomial =>
    stageDen_lt_of_wireEnvelope sources k p liveScale coefficientFloor wireCap primeBits
      thrDenBound hfloor x bits address monomial
      (henv n x bits ph address monomial hmonomial)
      (hprime n x bits monomial) (hthrden n x bits monomial)

/-- **Anti-vacuity receipt.**  The per-monomial envelope premise has witnesses at
every cap, so §6 and §7 are not vacuous. -/
theorem envelope_satisfiable {n : ℕ} {x : BitInput n} {bits : List Bool} (cap : ℕ) :
    ∃ monomial : CircuitMonomial (Atoms sources k p x bits) 4,
      ∀ atom ∈ monomial.factors, atomWires atom ≤ cap :=
  ⟨⟨1, [], by simp⟩, by simp⟩

/-- **`ebound` from a TYPE-LEVEL envelope.**  Vacuous at the current `Atom`; see
§8's header. -/
theorem ebound_of_atomWires (liveScale : ℕ)
    (coefficientFloor wireCap primeBits thrDenBound : ℕ → ℕ)
    (hfloor : ∀ n, stageArity sources k n +
      stageSeedEnvelope sources k p wireCap primeBits thrDenBound n + 1 ≤
      stageEntryWidth sources k p coefficientFloor n)
    (henv : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (atom : Atoms sources k p x bits),
      atomWires atom ≤ wireCap n)
    (hprime : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      (primesUpTo (primeCutoff (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p x bits monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k n)))).card ≤
        2 ^ primeBits n)
    (hthrden : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool)
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      listDenominator (decompositionOf sources)
        (rightRequest (unionRequestOf sources k p x bits monomial))
        (unionTarget (stageTarget sources p) (stageArity sources k n)) ≤ thrDenBound n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        stageDen sources k p liveScale n x bits address monomial <
          2 ^ stageEntryWidth sources k p coefficientFloor n :=
  fun n x bits _hn address monomial =>
    stageDen_lt_of_wireEnvelope sources k p liveScale coefficientFloor wireCap primeBits
      thrDenBound hfloor x bits address monomial (fun atom _ => henv n x bits atom)
      (hprime n x bits monomial) (hthrden n x bits monomial)

/-! ## §9 `hfloor` is FREE at the enlarged coefficient floor

`stageEntryWidth` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is a `max`
whose first branch is the caller's `coefficientFloor n`, so re-keying Floor 3 to
the external-row exponent costs nothing structural: the enlarged floor below
makes §6's `hfloor` an instance of `le_max_left`, and it keeps CLAUSEBITS'
coefficient bound by `le_max_left` as well, so `ecoef` transports through
`stage_field_hcoefficients` (`Proof/CaseAnalysis/FinalStageFields.lean`)
unchanged.  `stageScale` is never touched. -/

/-- The enlarged coefficient floor: CLAUSEBITS' own floor, or the external-row
exponent A.8:2253 budgets, whichever is larger. -/
def envelopeFloor (wireCap primeBits thrDenBound : ℕ → ℕ) (n : ℕ) : ℕ :=
  max (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p n)
    (stageArity sources k n +
      stageSeedEnvelope sources k p wireCap primeBits thrDenBound n + 1)

/-- **`hfloor` is free at the enlarged floor.** -/
theorem hfloor_at_envelopeFloor (wireCap primeBits thrDenBound : ℕ → ℕ) (n : ℕ) :
    stageArity sources k n +
      stageSeedEnvelope sources k p wireCap primeBits thrDenBound n + 1 ≤
      stageEntryWidth sources k p
        (envelopeFloor sources k p wireCap primeBits thrDenBound) n :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

/-- **CLAUSEBITS' coefficient bound survives the enlargement**, so `ecoef` is
still discharged and the enlarged floor adds no coefficient obligation. -/
theorem coefficientFloor_le_envelopeFloor (wireCap primeBits thrDenBound : ℕ → ℕ)
    (n : ℕ) :
    CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p n ≤
      envelopeFloor sources k p wireCap primeBits thrDenBound n :=
  le_max_left _ _

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
