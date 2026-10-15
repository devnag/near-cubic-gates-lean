import Proof.CaseAnalysis.FinalEnvelopeCounter
import Proof.CaseAnalysis.FinalMonomialPrinter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 Two frame readings of the loop bank -/

/-- **Below tape `278` the bank does not see the scratch.**  `bankAt`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) routes the scratch only through
its last branch. -/
theorem bank_frame_scratch {t : ℕ} (stream count driver input witness : List Bool)
    (s s' : ℕ → List Bool) (i : Fin t) (hlt : i.val < 278) :
    bank stream count driver input witness s i
      = bank stream count driver input witness s' i := by
  unfold bank bankAt
  split_ifs <;> first | rfl | omega

/-- **Off the data port `81` and the count port `90`, below `278`, the bank does
not see the record stream either.**  This is the frame clause every per-round
obligation in this module carries. -/
theorem bank_frame_ports {t : ℕ} (stream stream' count count' driver input witness : List Bool)
    (s s' : ℕ → List Bool) (i : Fin t) (h81 : i.val ≠ 81) (h90 : i.val ≠ 90)
    (hlt : i.val < 278) :
    bank stream count driver input witness s i
      = bank stream' count' driver input witness s' i := by
  unfold bank bankAt
  split_ifs <;> first | rfl | omega

/-! ## §2 Threading one round's choice into a family -/

/-- **A per-round existential becomes one family.**  The only place
`Classical.choice` enters this module: `Emits` gives a NEW scratch at each
round and `hbody` wants a single `scratch : ℕ → ℕ → List Bool`, so the rounds'
choices are chained. -/
theorem chain_of_step {α : Type} (rel : ℕ → α → α → Prop) (a : α)
    (h : ∀ (k : ℕ) (b : α), ∃ c : α, rel k b c) :
    ∃ f : ℕ → α, f 0 = a ∧ ∀ k, rel k (f k) (f (k + 1)) := by
  classical
  choose g hg using h
  exact ⟨fun k => Nat.rec (motive := fun _ => α) a (fun j b => g j b) k, rfl, fun k => hg k _⟩

/-! ## §3 The round bank, and the residual -/

/-- **The loop bank at round `k`, as a function of ONE scratch snapshot.**
`loopBank` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) reads the scratch
family only at `k`; saying so is what lets the round obligation quantify over
the incoming scratch instead of over a whole family. -/
noncomputable def roundBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ) : Fin (218 + (60 + extra)) → List Bool :=
  bank
    (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k))
    (CompareMachine.word
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length)
    (List.replicate entryWidth true) input witness s

/-- The two agree, definitionally. -/
theorem loopBank_roundBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k
      = roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness (scratch k) k := rfl

/-- **Round zero is branch-free**: the empty record stream and
`CompareMachine.word 0` (`Proof/PCP/VerifierDecodingCompare.lean`).  This is the
seam with the prologue -- the right-hand side names no `answer`, no `pcpp`, no
`coordinate`. -/
theorem roundBank_zero (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s 0
      = bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness s := rfl

/-- **THE RESIDUAL.**  One machine `body`, one budget `cost`, and for every round
`k` and every incoming scratch `s` a real run that carries the loop bank from
round `k` to round `k+1`, leaving the heads parked at zero and choosing its own
outgoing scratch.

Read the type: `roundBank` at `k` and at `k+1` differ on tape `81` by exactly
`CloseoutRowsEstimatorCoefficients.Stream.words entryWidth (addressRecords ... k)`
and on tape `90` by that list's length (`site_delta`, `idle_delta`), and
`addressRecords` is `siteRecords` -- one `callEntry`
(`Proof/CaseAnalysis/FinalSupplierCalls.lean`) per monomial, carrying
`answer monomial.factors`.  So `Emits` is inhabited only by a machine that
actually produces the AND-four CAPP estimates of `paper.tex:3555-3557` within
`cost`, which is the whole of what is left. -/
def Emits (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool) : Prop :=
  ∀ (k : ℕ) (s : ℕ → List Bool), ∃ s' : ℕ → List Bool,
    Step body cost (fun _ => 0)
      (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k)
      (fun _ => 0)
      (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s' (k + 1))

/-! ## §4 The residual IS `hbody`, both ranges -/

/-- **`hsite` and its idle twin, from one round obligation.**  The two address
ranges of `callsReady_at_clauseWidth`
(`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`) are instances of the SAME
per-round statement, so no separate idle argument is needed and the envelope's
padding rounds cost the emitter nothing beyond running.  `bound` is left free:
the consumer instantiates it at `2 ^ clauseWidth clauseDegree (q len)`. -/
theorem hbody_of_emits (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hemits : Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness)
    (bound : ℕ) :
    ∀ w : ℕ → List Bool,
      ∃ (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool),
        heads 0 = (fun _ => 0) ∧ scratch 0 = w ∧
        (∀ address, address < 2 ^ pcpp.clauseBits →
          Step body cost (heads address)
            (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness scratch address)
            (heads (address + 1))
            (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness scratch (address + 1))) ∧
        (∀ address, 2 ^ pcpp.clauseBits ≤ address → address < bound →
          Step body cost (heads address)
            (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness scratch address)
            (heads (address + 1))
            (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness scratch (address + 1))) := by
  intro w
  obtain ⟨f, hf0, hfstep⟩ :=
    chain_of_step
      (fun k s s' => Step body cost (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s k)
        (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s' (k + 1)))
      w hemits
  refine ⟨fun _ => fun _ => 0, f, rfl, hf0, ?_, ?_⟩
  · intro address _
    simpa only [loopBank_roundBank] using hfstep address
  · intro address _ _
    simpa only [loopBank_roundBank] using hfstep address

/-! ## §5 The consumer: `CallsReady`, from the prologue and the emitter -/

theorem callsReady_of_emits (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hemits : Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness)
    (hpre : ∃ w : ℕ → List Bool,
      Step pre preFuel (fun _ => 0)
        (bank [] [] [] input witness (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))) :
    C10SupplierStage.CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness := by
  obtain ⟨w, hstep⟩ := hpre
  obtain ⟨heads, scratch, hheads, hscratch, hsite, hidle⟩ :=
    hbody_of_emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness hemits (2 ^ clauseWidth clauseDegree q) w
  refine C10EnvelopeCounter.callsReady_at_clauseWidth extra pre body answer denominator phase
    pcpp coordinate systematicAtom entryWidth callCount preFuel cost clauseDegree q
    input witness heads scratch hlen hfit ?_ hsite hidle
  simpa only [hheads, loopBank_roundBank, hscratch, roundBank_zero] using hstep

/-! ## §6 What one round charges the body with, tape by tape -/

/-- Tape `81` of the round bank is the accumulated stream. -/
theorem roundBank_data (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ) (i : Fin (218 + (60 + extra))) (hi : i.val = 81) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k i
      = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k) := by
  unfold roundBank bank bankAt
  rw [hi]
  norm_num

/-- Tape `90` of the round bank is the record count. -/
theorem roundBank_count (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ) (i : Fin (218 + (60 + extra))) (hi : i.val = 90) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k i
      = CompareMachine.word
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length := by
  unfold roundBank bank bankAt
  rw [hi]
  norm_num

/-- Above `278` the round bank IS the scratch. -/
theorem roundBank_scratch (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ) (i : Fin (218 + (60 + extra))) (hi : 278 ≤ i.val) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k i = s i.val := by
  unfold roundBank bank bankAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos hi]

/-- **The ACTIVE round, in full.**  `paper.tex:1306-1309` and
`paper.tex:4133-4142` made physical at one clause address: the data port grows
by one word per monomial of that address's site polynomial -- each word carrying
`coefficientEstimate monomial.coefficient` and `answer monomial.factors`
(`monomialWord`, `Proof/CaseAnalysis/FinalMonomialPrinter.lean`) -- the count
port grows by the TERM COUNT of `paper.tex:1320-1322`, every other tape of the
`278` prefix is unmoved, and the scratch is the emitter's own.

This is the exact delta `Emits` charges at `k < 2 ^ pcpp.clauseBits`; nothing
else about the bank may change. -/
theorem site_delta (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s s' : ℕ → List Bool) (k : ℕ) (hk : k < 2 ^ pcpp.clauseBits) :
    ∃ address : Fin (2 ^ pcpp.clauseBits),
      (∀ i : Fin (218 + (60 + extra)), i.val = 81 →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1) i
          = roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness s k i
            ++ (C10MonomialPrinter.siteWords entryWidth answer denominator phase pcpp
                coordinate systematicAtom address).flatten) ∧
      (∀ i : Fin (218 + (60 + extra)), i.val = 90 →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1) i
          = CompareMachine.word
              ((prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length
                + (siteCalls phase pcpp coordinate systematicAtom address).monomials.length)) ∧
      (∀ i : Fin (218 + (60 + extra)), i.val ≠ 81 → i.val ≠ 90 → i.val < 278 →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1) i
          = roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness s k i) ∧
      (∀ i : Fin (218 + (60 + extra)), 278 ≤ i.val →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1) i = s' i.val) := by
  obtain ⟨address, haddress⟩ :=
    addressRecords_site answer denominator phase pcpp coordinate systematicAtom k hk
  refine ⟨address, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [roundBank_data extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s' (k + 1) i hi,
      roundBank_data extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k i hi,
      C10MonomialPrinter.siteWords_flatten, ← haddress, prefixRecords_succ, words_append]
  · intro i hi
    rw [roundBank_count extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s' (k + 1) i hi, prefixRecords_succ, List.length_append, haddress]
    unfold siteRecords callRecords
    rw [List.length_map]
  · intro i h81 h90 hlt
    exact bank_frame_ports _ _ _ _ _ input witness s' s i h81 h90 hlt
  · intro i hi
    exact roundBank_scratch extra entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness s' (k + 1) i hi

/-- **The IDLE round, in full.**  `paper.tex:1642` -- "Every branch-specific
power-of-two clause list is repeated to this fixed envelope" -- made physical:
past the branch's own address count the `278` prefix of the loop bank does not
move at all, data port and count port included.  So on the envelope's padding
rounds the emitter's entire charge is to RUN within `cost` and disturb nothing;
there is no second machine to build and no second argument to make.

Together with `site_delta` this is why `Emits` has one round clause and not
two. -/
theorem idle_delta (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s s' : ℕ → List Bool) {k : ℕ} (hk : 2 ^ pcpp.clauseBits ≤ k) :
    (addressRecords answer denominator phase pcpp coordinate systematicAtom k = []) ∧
      (∀ i : Fin (218 + (60 + extra)), i.val < 278 →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1) i
          = roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
              input witness s k i) ∧
      (∀ i : Fin (218 + (60 + extra)), 278 ≤ i.val →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1) i = s' i.val) := by
  refine ⟨C10EnvelopeCounter.addressRecords_past_end answer denominator phase pcpp coordinate
      systematicAtom hk, ?_, ?_⟩
  · intro i hlt
    have hsat : ∀ j : ℕ, 2 ^ pcpp.clauseBits ≤ j →
        roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' j i
          = bank
            (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
              (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
            (CompareMachine.word
              (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
            (List.replicate entryWidth true) input witness s' i := by
      intro j hj
      unfold roundBank
      rw [C10EnvelopeCounter.prefixRecords_saturate answer denominator phase pcpp coordinate
        systematicAtom hj]
    rw [hsat (k + 1) (by omega)]
    unfold roundBank
    rw [C10EnvelopeCounter.prefixRecords_saturate answer denominator phase pcpp coordinate
      systematicAtom hk]
    exact bank_frame_scratch _ _ _ input witness s' s i hlt
  · intro i hi
    exact roundBank_scratch extra entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness s' (k + 1) i hi

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
