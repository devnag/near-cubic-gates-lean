import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRoundBudget

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPorts

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundBudget
  (WidthPoly clearedFuel roundFuel widthPoly_roundFuel widthPoly_clearedFuel)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor (clauseEnvelope)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionRecords (phaseRecords')
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactRecordLoop
  (prefixRecords' addressRecords' siteRecords' prefixRecords'_succ phaseRecords'_flatMap
    prefixBank)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower entryWidthSchedule)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank bankAt words_append)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 The two record ports, and the exact delta one site round owes them -/

/-- **The count port grows by a suffix of set cells.**  `CompareMachine.word`
(`Proof/PCP/VerifierDecodingCompare.lean`) is `false :: List.replicate n true`, so
advancing the record count by `m` is writing `m` cells at the end and nothing
else. -/
theorem word_append (n m : ℕ) :
    CompareMachine.word n ++ List.replicate m true = CompareMachine.word (n + m) := by
  unfold CompareMachine.word
  rw [List.cons_append, ← List.replicate_add]

/-- **One record occupies a fixed number of cells.**  `record_length`
(`Proof/CaseAnalysis/RowsEstimatorCoefficientsPrepare.lean`) at the six fields of
`entryWord` (`Proof/CaseAnalysis/RowsEstimatorCoefficientsLoop.lean`): the width is
a function of the bank width `b` ALONE, not of the record's numbers.  This is
what makes §2's offset identity possible. -/
theorem entryWord_length (b : ℕ) (a : Entry) :
    (CloseoutRowsEstimatorCoefficients.Stream.entryWord b a).length = 20 * b + 22 :=
  CloseoutRowsEstimatorCoefficients.Stream.record_length b a.coefficient a.count a.denominator

/-- **The record stream is a flat block code.**  `Stream.words`
(`Proof/CaseAnalysis/RowsEstimatorCoefficientsLoop.lean`) is a `flatMap` with no
separator, so its length is the RECORD COUNT times the fixed entry width. -/
theorem words_length (b : ℕ) (xs : List Entry) :
    (CloseoutRowsEstimatorCoefficients.Stream.words b xs).length
      = xs.length * (20 * b + 22) := by
  induction xs with
  | nil => simp [CloseoutRowsEstimatorCoefficients.Stream.words]
  | cons a xs ih =>
      have hcons : CloseoutRowsEstimatorCoefficients.Stream.words b (a :: xs)
          = CloseoutRowsEstimatorCoefficients.Stream.entryWord b a
            ++ CloseoutRowsEstimatorCoefficients.Stream.words b xs := by
        simp only [CloseoutRowsEstimatorCoefficients.Stream.words, List.flatMap_cons]
      rw [hcons, List.length_append, ih, entryWord_length, List.length_cons]
      ring

/-- Tape `81` of the round bank is the accumulated record stream. -/
theorem prefixBank_data (extra entryWidth : ℕ) (xs : List Entry) (input witness : List Bool)
    (s : ℕ → List Bool) (i : Fin (218 + (60 + extra))) (hi : i.val = 81) :
    prefixBank extra entryWidth xs input witness s i
      = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth xs := by
  unfold prefixBank bank bankAt
  rw [hi]
  norm_num

/-- Tape `90` of the round bank is the record count, in unary. -/
theorem prefixBank_count (extra entryWidth : ℕ) (xs : List Entry) (input witness : List Bool)
    (s : ℕ → List Bool) (i : Fin (218 + (60 + extra))) (hi : i.val = 90) :
    prefixBank extra entryWidth xs input witness s i
      = CompareMachine.word xs.length := by
  unfold prefixBank bank bankAt
  rw [hi]
  norm_num

/-- **The tape-`81` delta of ONE site round.**  `prefixRecords'_succ`
(`Proof/CaseAnalysis/FinalExactRecordLoop.lean`) plus `words_append`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`): round `j` appends exactly the
words of clause address `j`'s records and touches nothing already written. -/
theorem prefixWords_succ (b : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    CloseoutRowsEstimatorCoefficients.Stream.words b
        (prefixRecords' phase pcpp coordinate systematicAtom record (j + 1))
      = CloseoutRowsEstimatorCoefficients.Stream.words b
          (prefixRecords' phase pcpp coordinate systematicAtom record j)
        ++ CloseoutRowsEstimatorCoefficients.Stream.words b
          (addressRecords' phase pcpp coordinate systematicAtom record j) := by
  rw [prefixRecords'_succ, words_append]

/-- **The tape-`90` delta of ONE site round.** -/
theorem prefixCount_succ (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    CompareMachine.word
        (prefixRecords' phase pcpp coordinate systematicAtom record (j + 1)).length
      = CompareMachine.word
          (prefixRecords' phase pcpp coordinate systematicAtom record j).length
        ++ List.replicate
          (addressRecords' phase pcpp coordinate systematicAtom record j).length true := by
  rw [word_append, prefixRecords'_succ, List.length_append]

/-- **BOTH RECORD PORTS OF ONE SITE ROUND, AT THE BANK.**  The whole visible
obligation of `hsite` (`Proof/CaseAnalysis/FinalExactCallLoopJoin.lean`) on
tapes `81` and `90`: two pure suffix appends, at one clause address's records.

A round that wrote anything but this could not inhabit `hsite`, and a round that
wrote this without computing `record address monomial` could not either --
`record` is `exactFractionRecord` (`Proof/CaseAnalysis/FinalExactFraction.lean`)
at the stage's `num`/`den`, i.e. the AND-four CAPP estimate of
`paper.tex:3555-3557`. -/
theorem site_port_delta (extra entryWidth : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ)
    (input witness : List Bool) (s s' : ℕ → List Bool)
    (i₈₁ i₉₀ : Fin (218 + (60 + extra))) (h81 : i₈₁.val = 81) (h90 : i₉₀.val = 90) :
    prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record (j + 1))
          input witness s' i₈₁
        = prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record j) input witness s i₈₁
          ++ CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
            (addressRecords' phase pcpp coordinate systematicAtom record j)
      ∧ prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record (j + 1))
          input witness s' i₉₀
        = prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record j) input witness s i₉₀
          ++ List.replicate
            (addressRecords' phase pcpp coordinate systematicAtom record j).length true := by
  constructor
  · rw [prefixBank_data extra entryWidth _ input witness s' i₈₁ h81,
      prefixBank_data extra entryWidth _ input witness s i₈₁ h81, prefixWords_succ]
  · rw [prefixBank_count extra entryWidth _ input witness s' i₉₀ h90,
      prefixBank_count extra entryWidth _ input witness s i₉₀ h90, prefixCount_succ]

/-! ## §2 The append offset, in closed form -/

/-- **The data port's length at round `j`.** -/
theorem prefixWords_length (b : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    (CloseoutRowsEstimatorCoefficients.Stream.words b
        (prefixRecords' phase pcpp coordinate systematicAtom record j)).length
      = (prefixRecords' phase pcpp coordinate systematicAtom record j).length
        * (20 * b + 22) :=
  words_length b _

/-- **THE OFFSET IDENTITY.**  The place on tape `81` where round `j` must start
writing is `(the length of tape 90, less one) * (20 * entryWidth + 22)`.

This is the reason the round is buildable at all.  `Step` parks every head at
`0` on entry (`hsite`'s `fun _ => 0`), `Stream.words`
(`Proof/CaseAnalysis/RowsEstimatorCoefficientsLoop.lean`) carries no separator and
no terminator, and `readTapeBit tape position = tape.getD position false`
(`Proof/Foundations/LocalBitMultitapeCore.lean`) makes every cell past the end
read `false` -- so the end of the record stream is NOT findable by scanning.  It
is findable by counting, and this identity is what it counts. -/
theorem site_port_offset (extra entryWidth : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ)
    (input witness : List Bool) (s : ℕ → List Bool)
    (i₈₁ i₉₀ : Fin (218 + (60 + extra))) (h81 : i₈₁.val = 81) (h90 : i₉₀.val = 90) :
    (prefixBank extra entryWidth
        (prefixRecords' phase pcpp coordinate systematicAtom record j)
        input witness s i₈₁).length
      = ((prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record j)
          input witness s i₉₀).length - 1) * (20 * entryWidth + 22) := by
  rw [prefixBank_data extra entryWidth _ input witness s i₈₁ h81,
    prefixBank_count extra entryWidth _ input witness s i₉₀ h90, prefixWords_length]
  have hw : (CompareMachine.word
      (prefixRecords' phase pcpp coordinate systematicAtom record j).length).length
      = (prefixRecords' phase pcpp coordinate systematicAtom record j).length + 1 := by
    unfold CompareMachine.word
    simp
  rw [hw]
  simp

/-! ## §3 The bound that does not mention the round index -/

/-- **A `j`-FREE bound on the append offset**, in the record count `CallsReady`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`) already carries as a port. -/
def portBound (entryWidth callCount : ℕ) : ℕ := callCount * (20 * entryWidth + 22)

/-- **Every round's accumulated stream is a prefix of the phase's.**  The round
loop never rewrites; `prefixRecords'`
(`Proof/CaseAnalysis/FinalExactRecordLoop.lean`) takes a `take` of the address
list and `phaseRecords'_flatMap`
(`Proof/CaseAnalysis/FinalExactRecordLoop.lean`) is the whole list. -/
theorem prefixRecords'_append (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    ∃ ys : List Entry,
      phaseRecords' phase pcpp coordinate systematicAtom record
        = prefixRecords' phase pcpp coordinate systematicAtom record j ++ ys := by
  refine ⟨(((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop j)).flatMap
    (siteRecords' phase pcpp coordinate systematicAtom record), ?_⟩
  rw [phaseRecords'_flatMap]
  unfold prefixRecords'
  rw [← List.flatMap_append, List.take_append_drop]

/-- **The record count at every round is under the phase's own call count.** -/
theorem prefixRecords'_length_le (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    (prefixRecords' phase pcpp coordinate systematicAtom record j).length
      ≤ (phaseRecords' phase pcpp coordinate systematicAtom record).length := by
  obtain ⟨ys, hys⟩ := prefixRecords'_append phase pcpp coordinate systematicAtom record j
  rw [hys, List.length_append]
  omega

/-- **THE `j`-FREE SEEK BOUND.**  Whatever the round, the appender never has to
walk further than `portBound entryWidth callCount`.  The cost of the walk GROWS
with the round index; this BOUND does not, and `hsite`'s one `cost n` can
therefore pay for it. -/
theorem site_port_offset_le (b : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    (CloseoutRowsEstimatorCoefficients.Stream.words b
        (prefixRecords' phase pcpp coordinate systematicAtom record j)).length
      ≤ portBound b (phaseRecords' phase pcpp coordinate systematicAtom record).length := by
  rw [prefixWords_length]
  exact Nat.mul_le_mul_right _
    (prefixRecords'_length_le phase pcpp coordinate systematicAtom record j)

/-- The same for the count port. -/
theorem site_count_length_le (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (j : ℕ) :
    (CompareMachine.word
        (prefixRecords' phase pcpp coordinate systematicAtom record j).length).length
      ≤ (phaseRecords' phase pcpp coordinate systematicAtom record).length + 1 := by
  have hw : (CompareMachine.word
      (prefixRecords' phase pcpp coordinate systematicAtom record j).length).length
      = (prefixRecords' phase pcpp coordinate systematicAtom record j).length + 1 := by
    unfold CompareMachine.word
    simp
  have := prefixRecords'_length_le phase pcpp coordinate systematicAtom record j
  omega

/-! ## §4 The round count is polynomial in `q` -/

/-- `2 ^ Nat.clog 2 m < 2 * m`, the standard ceiling-log estimate, for `1 ≤ m`. -/
theorem two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have h1 : m = 1 := by omega
    subst h1
    rw [Nat.clog_one_right]
    norm_num
  · have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by omega) h
    have hlt : 2 ^ (Nat.clog 2 m - 1) < m :=
      Nat.pow_pred_clog_lt_self (b := 2) (x := m) (by omega) (by omega)
    have hsplit : (2 : ℕ) ^ Nat.clog 2 m = 2 ^ (Nat.clog 2 m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    omega

/-- **`paper.tex:4516`'s `M`, bounded.**  `clauseEnvelope`
(`Proof/CaseAnalysis/FinalRoundCursor.lean`) is
`2 ^ Nat.clog 2 ((q+2)^clauseDegree)`, the paper's
`M = 2^{\lceil d_G\log_2(q+2)\rceil}`; so it is `(q+2)^{d_G}` up to one doubling,
and therefore a FIXED POWER OF `q`.  This is the fact every `j`-free budget in
this module rests on. -/
theorem clauseEnvelope_le (clauseDegree q : ℕ) :
    clauseEnvelope clauseDegree q ≤ 2 ^ (clauseDegree + 1) * (q + 1) ^ clauseDegree := by
  have hm : 1 ≤ (q + 2) ^ clauseDegree := Nat.one_le_pow _ _ (by omega)
  have h1 : clauseEnvelope clauseDegree q ≤ 2 * (q + 2) ^ clauseDegree := by
    unfold clauseEnvelope clauseWidth
    exact two_pow_clog_le _ hm
  have h2 : (q + 2) ^ clauseDegree ≤ 2 ^ clauseDegree * (q + 1) ^ clauseDegree := by
    calc (q + 2) ^ clauseDegree ≤ (2 * (q + 1)) ^ clauseDegree :=
          Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ clauseDegree * (q + 1) ^ clauseDegree := by rw [mul_pow]
  have h3 : 2 * (2 ^ clauseDegree * (q + 1) ^ clauseDegree)
      = 2 ^ (clauseDegree + 1) * (q + 1) ^ clauseDegree := by
    rw [pow_succ]
    ring
  exact le_trans h1 (le_trans (Nat.mul_le_mul_left 2 h2) (le_of_eq h3))

/-- **The round count is `q^{O(1)}`.**  `WidthPoly`
(`Proof/CaseAnalysis/FinalRoundBudget.lean`) at `A := 2^(d+1)`, `c := d`. -/
theorem widthPoly_clauseEnvelope (sources : RepairSource.EightSources) (k clauseDegree : ℕ) :
    WidthPoly sources k (fun N => clauseEnvelope clauseDegree (widthAt sources k N)) := by
  refine ⟨2 ^ (clauseDegree + 1), clauseDegree, fun N => ?_⟩
  show clauseEnvelope clauseDegree (widthAt sources k N)
    ≤ 2 ^ (clauseDegree + 1) * widthPower sources k clauseDegree N
  unfold widthPower
  exact clauseEnvelope_le clauseDegree (widthAt sources k N)

theorem unaryBump_le_envelope (clauseDegree q j : ℕ)
    (hj : j < clauseEnvelope clauseDegree q) :
    2 * j + 2 ≤ 2 * clauseEnvelope clauseDegree q + 2 := by omega

/-- The uniform bump budget is `q^{O(1)}`. -/
theorem widthPoly_unaryBump (sources : RepairSource.EightSources) (k clauseDegree : ℕ) :
    WidthPoly sources k
      (fun N => 2 * clauseEnvelope clauseDegree (widthAt sources k N) + 2) :=
  ((WidthPoly.const sources k 2).mul (widthPoly_clauseEnvelope sources k clauseDegree)).add
    (WidthPoly.const sources k 2)

/-! ## §5 The stage `roundFuel` omits, and the corrected round total -/

def siteRoundFuel (w rows shift decode cursor terms port : ℕ) : ℕ :=
  roundFuel w rows shift decode cursor terms + 1 + clearedFuel port

/-- The `j`-free seek bound is `q^{O(1)}` whenever the entry width and the call
count are. -/
theorem widthPoly_portBound (sources : RepairSource.EightSources) (k : ℕ)
    {w callCount : ℕ → ℕ} (hw : WidthPoly sources k w)
    (hcalls : WidthPoly sources k callCount) :
    WidthPoly sources k (fun N => portBound (w N) (callCount N)) :=
  hcalls.mul (((WidthPoly.const sources k 20).mul hw).add (WidthPoly.const sources k 22))

/-- The corrected round total is `q^{O(1)}`. -/
theorem widthPoly_siteRoundFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows shift decode cursor terms port : ℕ → ℕ} (hw : WidthPoly sources k w)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hcursor : WidthPoly sources k cursor)
    (hterms : WidthPoly sources k terms) (hport : WidthPoly sources k port) :
    WidthPoly sources k
      (fun N => siteRoundFuel (w N) (rows N) (shift N) (decode N) (cursor N) (terms N)
        (port N)) :=
  ((widthPoly_roundFuel sources k hw hrows hshift hdecode hcursor hterms).add
    (WidthPoly.const sources k 1)).add (widthPoly_clearedFuel sources k hport)

theorem siteRoundFuel_le_hotFuel (sources : RepairSource.EightSources) (k r degree : ℕ)
    (rows shift decode cursor terms port : ℕ → ℕ)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hcursor : WidthPoly sources k cursor)
    (hterms : WidthPoly sources k terms) (hport : WidthPoly sources k port) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      siteRoundFuel (entryWidthSchedule sources k r N) (rows N) (shift N) (decode N)
          (cursor N) (terms N) (port N)
        ≤ hotFuel sources k r degree N :=
  (widthPoly_siteRoundFuel sources k
    (CloseoutFinalC10RoundBudget.widthPoly_entryWidthSchedule sources k r) hrows hshift
    hdecode hcursor hterms hport).le_hotFuel r degree

theorem siteRoundFuel_at_ports_le_hotFuel (sources : RepairSource.EightSources)
    (k r degree clauseDegree : ℕ) (rows shift decode terms callCount : ℕ → ℕ)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hterms : WidthPoly sources k terms)
    (hcalls : WidthPoly sources k callCount) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      siteRoundFuel (entryWidthSchedule sources k r N) (rows N) (shift N) (decode N)
          (2 * clauseEnvelope clauseDegree (widthAt sources k N) + 2) (terms N)
          (portBound (entryWidthSchedule sources k r N) (callCount N))
        ≤ hotFuel sources k r degree N :=
  siteRoundFuel_le_hotFuel sources k r degree rows shift decode
    (fun N => 2 * clauseEnvelope clauseDegree (widthAt sources k N) + 2) terms
    (fun N => portBound (entryWidthSchedule sources k r N) (callCount N))
    hrows hshift hdecode (widthPoly_unaryBump sources k clauseDegree) hterms
    (widthPoly_portBound sources k
      (CloseoutFinalC10RoundBudget.widthPoly_entryWidthSchedule sources k r) hcalls)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPorts
