import Proof.CaseAnalysis.FinalBandRecycle
import Proof.CaseAnalysis.FinalEnvelopeCounter

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage (CallsReady)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The cursor word -/

/-- **The cursor.**  A fixed-width binary word carrying the SATURATING round
index `min k envelope`.  `fixedWidthNatBits`
(`Proof/Foundations/OperationalWilliamsSourceCore.lean`) is
`List.ofFn fun bit : Fin width => value.testBit bit.val`, so the tape holds
exactly `width` cells whatever `k` is. -/
def cursorWord (width envelope k : ℕ) : List Bool :=
  WilliamsPublishedForm.fixedWidthNatBits width (min k envelope)

/-- **The cursor tape has the same length at every round.**  This is the whole
cost argument in one line: no round has to lengthen the cursor tape, so
`length_mono` (`Proof/CaseAnalysis/FinalNativeReload.lean`) costs nothing here
and the per-round charge is a function of `width` and not of `k`. -/
theorem cursorWord_length (width envelope k : ℕ) :
    (cursorWord width envelope k).length = width := by
  simp [cursorWord, WilliamsPublishedForm.fixedWidthNatBits]

/-- **Past the envelope the cursor stops moving.**  This is what makes the tail
of `Rounds` a SINGLE `k`-free obligation instead of a family. -/
theorem cursorWord_saturate (width envelope k : ℕ) (hk : envelope ≤ k) :
    cursorWord width envelope k = cursorWord width envelope envelope := by
  unfold cursorWord
  rw [min_eq_right hk, min_self]

theorem cursorWord_zero (width envelope : ℕ) :
    cursorWord width envelope 0 = ZeroPadding.pad width [] := by
  rw [CloseoutFinalC10BandRecycle.pad_nil]
  unfold cursorWord WilliamsPublishedForm.fixedWidthNatBits
  simp

/-- A fixed-width binary word determines its value below the width's capacity. -/
theorem fixedWidthNatBits_inj {width a b : ℕ} (ha : a < 2 ^ width) (hb : b < 2 ^ width)
    (h : WilliamsPublishedForm.fixedWidthNatBits width a
      = WilliamsPublishedForm.fixedWidthNatBits width b) : a = b := by
  unfold WilliamsPublishedForm.fixedWidthNatBits at h
  have hfun : (fun bit : Fin width => a.testBit bit.val)
      = fun bit : Fin width => b.testBit bit.val := List.ofFn_inj.mp h
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  by_cases hi : i < width
  · simpa using congrFun hfun ⟨i, hi⟩
  · have hp : (2 : ℕ) ^ width ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hp)]

/-- **Below the envelope the cursor determines the round.**  No hypothesis on
any site polynomial, in contrast with `addressDeterminacy_of_nonempty`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`). -/
theorem cursorWord_inj (width envelope : ℕ) (hw : envelope < 2 ^ width) {k₁ k₂ : ℕ}
    (h₁ : k₁ ≤ envelope) (h₂ : k₂ ≤ envelope)
    (h : cursorWord width envelope k₁ = cursorWord width envelope k₂) : k₁ = k₂ := by
  unfold cursorWord at h
  have hm : min k₁ envelope = min k₂ envelope :=
    fixedWidthNatBits_inj (lt_of_le_of_lt (min_le_right _ _) hw)
      (lt_of_le_of_lt (min_le_right _ _) hw) h
  rwa [min_eq_left h₁, min_eq_left h₂] at hm

/-! ## §2 The envelope the paper names, and the width it needs -/

/-- **The paper's branch-independent address count.**  `paper.tex:4516`:
"which is exactly \(\log_2M\) for \(M=2^{\lceil d_G\log_2(q+2)\rceil}\)".  It is
the same number `callsReady_at_clauseWidth`
(`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`) makes the prologue count out
and `counter_length` (`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`)
measures. -/
def clauseEnvelope (clauseDegree q : ℕ) : ℕ := 2 ^ clauseWidth clauseDegree q

/-- **The cursor's tape width**: one cell more than `paper.tex:4516`'s
`\log_2 M`, so that the SATURATED value `clauseEnvelope` itself is representable. -/
def cursorWidth (clauseDegree q : ℕ) : ℕ := clauseWidth clauseDegree q + 1

/-- The width is enough for every value the cursor ever holds. -/
theorem clauseEnvelope_lt (clauseDegree q : ℕ) :
    clauseEnvelope clauseDegree q < 2 ^ cursorWidth clauseDegree q := by
  have h : 1 ≤ 2 ^ clauseWidth clauseDegree q := Nat.one_le_pow _ 2 (by omega)
  unfold clauseEnvelope cursorWidth
  rw [pow_succ]
  omega

/-! ## §3 The cost of the unary alternative, measured -/

def unaryCursorCost : ℕ → ℕ
  | 0 => 0
  | k + 1 => unaryCursorCost k + (2 * k + 2)

theorem unaryCursorCost_eq (E : ℕ) : unaryCursorCost E = E * (E + 1) := by
  induction E with
  | zero => rfl
  | succ n ih =>
      unfold unaryCursorCost
      rw [ih]
      ring

/-! ## §4 The invariant -/

def CursorInv (width envelope cursorTape : ℕ) (Rest : (ℕ → List Bool) → Prop)
    (k : ℕ) (s : ℕ → List Bool) : Prop :=
  s cursorTape = cursorWord width envelope k ∧ Rest s

/-- **The cursor form of `AddressDeterminacy`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`), discharged with no hypothesis
on any site polynomial.**  One scratch snapshot satisfies the invariant at at
most one round, so the round body can read the state that selects the next
clause address even when that address emits nothing. -/
theorem cursorInv_determines_round (width envelope cursorTape : ℕ)
    (Rest : (ℕ → List Bool) → Prop) (hw : envelope < 2 ^ width)
    {k₁ k₂ : ℕ} (h₁ : k₁ ≤ envelope) (h₂ : k₂ ≤ envelope) (s : ℕ → List Bool)
    (hc₁ : CursorInv width envelope cursorTape Rest k₁ s)
    (hc₂ : CursorInv width envelope cursorTape Rest k₂ s) : k₁ = k₂ :=
  cursorWord_inj width envelope hw h₁ h₂ (hc₁.1.symm.trans hc₂.1)

/-- **Writing the cursor onto a scratch.**  Used both to inhabit the invariant
and to show it does not disturb a band above `line`. -/
def setCursor (cursorTape : ℕ) (w : List Bool) (s : ℕ → List Bool) : ℕ → List Bool :=
  fun v => if v = cursorTape then w else s v

theorem cursorInv_setCursor (width envelope cursorTape total line k : ℕ)
    (hcur : cursorTape < line) (s : ℕ → List Bool)
    (hs : CloseoutFinalC10BandRecycle.ZeroBand total line s) :
    CursorInv width envelope cursorTape
      (CloseoutFinalC10BandRecycle.ZeroBand total line) k
      (setCursor cursorTape (cursorWord width envelope k) s) := by
  refine ⟨?_, ?_⟩
  · simp [setCursor]
  · intro v hv
    have hne : v ≠ cursorTape := by omega
    simpa [setCursor, hne] using hs v hv

theorem cursor_frame_of_band (extra cursorTape line : ℕ) (hcur : 278 ≤ cursorTape)
    (hlt : cursorTape < line) {r : ℕ} (slots : Fin r → Fin (218 + (60 + extra)))
    (hband : ∀ j, line ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (A : Fin (218 + (60 + extra)) → List Bool)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      A i = bank stream count driver input witness s i) :
    scratchOf extra A s cursorTape = s cursorTape := by
  by_cases hfit : cursorTape < 218 + (60 + extra)
  · have hoff : ∀ j, slots j ≠ (⟨cursorTape, hfit⟩ : Fin (218 + (60 + extra))) := by
      intro j hj
      have hv : (slots j).val = cursorTape := by rw [hj]
      have := hband j
      omega
    rw [scratchOf_apply extra A s ⟨cursorTape, hfit⟩, hframe _ hoff,
      bank_scratch_apply stream count driver input witness s ⟨cursorTape, hfit⟩ hcur]
  · unfold scratchOf
    rw [dif_neg hfit]

/-! ## §5 The two things the record ports cannot do, and the bank past the
envelope -/

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-- **Why the output alone cannot carry the round index.**  At a clause address
whose site emits nothing, `roundBank`
(`Proof/CaseAnalysis/FinalSiteBodyUniform.lean`) at `k + 1` IS `roundBank` at
`k`: tapes `81` and `90` are identical and every other tape of the bank is
`k`-free.  `momentSite_monomials_nil`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`) exhibits a coordinate family
that makes the hypothesis hold, so this is not a vacuous warning -- it is the
exact reason `AddressDeterminacy` is unavailable on this route. -/
theorem roundBank_stall_of_empty_site (extra entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ)
    (hnil : addressRecords answer denominator phase pcpp coordinate systematicAtom k = []) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s (k + 1)
      = roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k := by
  unfold roundBank
  rw [prefixRecords_succ answer denominator phase pcpp coordinate systematicAtom k, hnil,
    List.append_nil]

/-- **The bank past the branch's own address count**, as ONE `k`-free tape
function.  `prefixRecords_saturate`
(`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`) is what makes it `k`-free. -/
noncomputable def saturatedBank (extra entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) : Fin (218 + (60 + extra)) → List Bool :=
  bank
    (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
    (CompareMachine.word
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
    (List.replicate entryWidth true) input witness s

theorem roundBank_saturate (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) {k : ℕ} (hk : 2 ^ pcpp.clauseBits ≤ k) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k
      = saturatedBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s := by
  unfold roundBank saturatedBank
  rw [prefixRecords_saturate answer denominator phase pcpp coordinate systematicAtom hk]

/-- **`Rounds` from a bounded family of site rounds and ONE idle round.**

This is the reduction the cursor buys.  `Rounds`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) quantifies `k` over all of
`ℕ`; `hsite` supplies only the rounds BELOW the envelope, and `hidle` is a
single obligation with NO `k` in it at all, because
`prefixRecords_saturate` (`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`)
collapses the whole tail to `saturatedBank` and `cursorWord_saturate` collapses
the cursor to its saturated value.

Read the hypotheses: `hsite`'s conclusion is a `Step` of `body` within `cost`
carrying `roundBank` from `k` to `k + 1`, which differ on tape `81` by
`Stream.words entryWidth (addressRecords … k)` -- one `callEntry`
(`Proof/CaseAnalysis/FinalSupplierCalls.lean`) per monomial carrying
`answer monomial.factors`.  So this theorem does not inhabit `Rounds` for free:
it is the envelope bookkeeping, and the AND-four CAPP estimates of
`paper.tex:3555-3557` remain exactly where they were.

`AddressDeterminacy` (`Proof/CaseAnalysis/FinalRoundEmitter.lean`) appears in
neither the statement nor the proof. -/
theorem rounds_of_cursor (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth width envelope cursorTape : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Rest : (ℕ → List Bool) → Prop)
    (henv : 2 ^ pcpp.clauseBits ≤ envelope)
    (hsite : ∀ k : ℕ, k < envelope → ∀ s : ℕ → List Bool,
      CursorInv width envelope cursorTape Rest k s →
      ∃ s' : ℕ → List Bool, CursorInv width envelope cursorTape Rest (k + 1) s' ∧
        Step body cost (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s k)
          (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1)))
    (hidle : ∀ s : ℕ → List Bool,
      s cursorTape = cursorWord width envelope envelope → Rest s →
      ∃ s' : ℕ → List Bool, s' cursorTape = cursorWord width envelope envelope ∧ Rest s' ∧
        Step body cost (fun _ => 0)
          (saturatedBank extra entryWidth answer denominator phase pcpp coordinate
            systematicAtom input witness s)
          (fun _ => 0)
          (saturatedBank extra entryWidth answer denominator phase pcpp coordinate
            systematicAtom input witness s')) :
    Rounds extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness (CursorInv width envelope cursorTape Rest) := by
  intro k s hinv
  rcases Nat.lt_or_ge k envelope with hk | hk
  · exact hsite k hk s hinv
  · have hsat : s cursorTape = cursorWord width envelope envelope := by
      rw [hinv.1, cursorWord_saturate width envelope k hk]
    obtain ⟨s', hcur', hrest', hstep⟩ := hidle s hsat hinv.2
    refine ⟨s', ⟨?_, hrest'⟩, ?_⟩
    · rw [hcur', (cursorWord_saturate width envelope (k + 1) (by omega)).symm]
    · rw [roundBank_saturate extra entryWidth answer denominator phase pcpp coordinate
        systematicAtom input witness s (le_trans henv hk),
        roundBank_saturate extra entryWidth answer denominator phase pcpp coordinate
        systematicAtom input witness s' (le_trans henv (by omega))]
      exact hstep

/-- **The same at the paper's own envelope.**  `hfit` is
`callsReady_at_clauseWidth`'s (`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`)
`M_0 ≤ M`, and it is the only thing needed to put the branch's address count
inside `clauseEnvelope`. -/
theorem rounds_at_clauseEnvelope (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth cursorTape clauseDegree q : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Rest : (ℕ → List Bool) → Prop)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hsite : ∀ k : ℕ, k < clauseEnvelope clauseDegree q → ∀ s : ℕ → List Bool,
      CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest k s →
      ∃ s' : ℕ → List Bool,
        CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest
          (k + 1) s' ∧
        Step body cost (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s k)
          (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1)))
    (hidle : ∀ s : ℕ → List Bool,
      s cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
        (clauseEnvelope clauseDegree q) → Rest s →
      ∃ s' : ℕ → List Bool,
        s' cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
          (clauseEnvelope clauseDegree q) ∧ Rest s' ∧
        Step body cost (fun _ => 0)
          (saturatedBank extra entryWidth answer denominator phase pcpp coordinate
            systematicAtom input witness s)
          (fun _ => 0)
          (saturatedBank extra entryWidth answer denominator phase pcpp coordinate
            systematicAtom input witness s')) :
    Rounds extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness
      (CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest) :=
  rounds_of_cursor extra body cost entryWidth (cursorWidth clauseDegree q)
    (clauseEnvelope clauseDegree q) cursorTape answer denominator phase pcpp coordinate
    systematicAtom input witness Rest (Nat.pow_le_pow_right (by omega) hfit) hsite hidle

theorem callsReady_of_cursor (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost clauseDegree q cursorTape : ℕ) (input witness : List Bool)
    (Rest : (ℕ → List Bool) → Prop)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hsite : ∀ k : ℕ, k < clauseEnvelope clauseDegree q → ∀ s : ℕ → List Bool,
      CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest k s →
      ∃ s' : ℕ → List Bool,
        CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest
          (k + 1) s' ∧
        Step body cost (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s k)
          (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1)))
    (hidle : ∀ s : ℕ → List Bool,
      s cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
        (clauseEnvelope clauseDegree q) → Rest s →
      ∃ s' : ℕ → List Bool,
        s' cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
          (clauseEnvelope clauseDegree q) ∧ Rest s' ∧
        Step body cost (fun _ => 0)
          (saturatedBank extra entryWidth answer denominator phase pcpp coordinate
            systematicAtom input witness s)
          (fun _ => 0)
          (saturatedBank extra entryWidth answer denominator phase pcpp coordinate
            systematicAtom input witness s'))
    (hpre : ∃ w : ℕ → List Bool,
      CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest 0 w ∧
      Step pre preFuel (fun _ => 0)
        (bank [] [] [] input witness (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))) :
    CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness :=
  callsReady_of_rounds extra pre body answer denominator phase pcpp coordinate systematicAtom
    entryWidth callCount preFuel cost clauseDegree q input witness
    (CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest)
    hlen hfit
    (rounds_at_clauseEnvelope extra body cost entryWidth cursorTape clauseDegree q answer
      denominator phase pcpp coordinate systematicAtom input witness Rest hfit hsite hidle)
    hpre

end NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor
