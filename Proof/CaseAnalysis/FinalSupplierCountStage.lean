import Proof.CaseAnalysis.FinalRoundEmitter
import Proof.CaseAnalysis.FinalDividerDock
import Proof.CaseAnalysis.FinalSupplierWidth

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10DividerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The model fact: no `Step` ever blanks a tape -/

/-- **A `Step` cannot turn a nonempty tape into an empty one.**  Immediate from
`length_mono` (`Proof/CaseAnalysis/FinalNativeReload.lean`), and it is the whole
reason the scratch discipline below is a BLANKNESS condition and not a length
bound: there is no eraser in this model, at any bound. -/
theorem blank_not_restorable {t s : ℕ} {M : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A B : Fin t → List Bool} (h : Step M n H A H' B) (i : Fin t) (hB : B i = []) :
    A i = [] := by
  cases hA : A i with
  | nil => rfl
  | cons a as =>
      exfalso
      have hlen := C10NativeReload.length_mono h i
      rw [hA, hB] at hlen
      simp at hlen

/-- **The band a round dirties stays dirty.**  The contrapositive of
`blank_not_restorable`, stated the way a builder meets it: no prefix of a round
program can present a dirty scratch slot as blank to a docked engine. -/
theorem band_never_cleared {t s : ℕ} {M : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A B : Fin t → List Bool} (h : Step M n H A H' B) (i : Fin t) (hA : A i ≠ []) :
    B i ≠ [] := by
  intro hB
  exact hA (blank_not_restorable h i hB)

/-! ## §2 The bank on its scratch band -/

/-- On the scratch band the bank IS the scratch, by tape number. -/
theorem bank_scratch_apply {t : ℕ} (stream count driver input witness : List Bool)
    (s : ℕ → List Bool) (i : Fin t) (hi : 278 ≤ i.val) :
    bank stream count driver input witness s i = s i.val := by
  show bankAt stream count driver input witness s i.val = s i.val
  unfold bankAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos hi]

/-- Off the band and off the six ports the bank is blank, at every scratch. -/
theorem bank_below_blank {t : ℕ} (stream count driver input witness : List Bool)
    (s : ℕ → List Bool) (i : Fin t) (hi : i.val < 278)
    (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) (h81 : i.val ≠ 81) (h90 : i.val ≠ 90)
    (h216 : i.val ≠ 216) (h218 : i.val ≠ 218) :
    bank stream count driver input witness s i = [] := by
  show bankAt stream count driver input witness s i.val = []
  unfold bankAt
  rw [if_neg h0, if_neg h1, if_neg h81, if_neg h90, if_neg h216, if_neg h218,
    if_neg (by omega)]

/-! ## §3 Why `Appends`'s `∀ s` forecloses the whole docked-engine library -/

/-- **The blank-slot hypothesis every docked engine carries is refuted on the
band.**  `sum_dock`, `copy_dock`, `product_dock`, `fixedWord_dock`
(`Proof/CaseAnalysis/FinalWordEngines.lean`, `:90`, `:120`, `:161`),
`divide_dock`, `answer_dock` (`Proof/CaseAnalysis/FinalDividerDock.lean`,
`:141`), `dock`, `clause_dock` and `support_dock`
(`Proof/CaseAnalysis/FinalWordFunctionDock.lean`, `:267`, `:286`) each demand
`A (slots j) = []` at one or more slots.  `Appends`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`) hands the round
`bank ... s` for an ARBITRARY `s`, so the hypothesis fails at `s := fun _ => [true]`
whenever the slot lies on the scratch band -- and by `band_never_cleared` (§1) the
round cannot repair that by clearing the slot first. -/
theorem dock_blank_hypothesis_fails {t r : ℕ} (slots : Fin r → Fin t) (j : Fin r)
    (hj : 278 ≤ (slots j).val) (stream count driver input witness : List Bool) :
    ¬ ∀ s : ℕ → List Bool, bank stream count driver input witness s (slots j) = [] := by
  intro h
  have hb := h (fun _ => [true])
  rw [bank_scratch_apply stream count driver input witness _ (slots j) hj] at hb
  exact absurd hb (by simp)

theorem round_scratch_grows {extra ts : ℕ} {M : Machine (218 + (60 + extra)) ts} {n : ℕ}
    (stream count driver input witness : List Bool) (sc sc' : ℕ → List Bool)
    (h : Step M n (fun _ => 0) (bank stream count driver input witness sc)
      (fun _ => 0) (bank stream count driver input witness sc'))
    (i : Fin (218 + (60 + extra))) (hi : 278 ≤ i.val) :
    (sc i.val).length ≤ (sc' i.val).length := by
  have hlen := C10NativeReload.length_mono h i
  rwa [bank_scratch_apply stream count driver input witness sc i hi,
    bank_scratch_apply stream count driver input witness sc' i hi] at hlen

/-- **A dirty band slot is dirty at every later round.**  This is the fact that
decides the scratch question: the discipline a round machine can maintain is
BLANKNESS OF A BAND IT HAS NOT YET TOUCHED, never "the band is short".  A length
bound on the incoming scratch buys nothing, because no round can shorten it. -/
theorem round_band_dirty_persists {extra ts : ℕ} {M : Machine (218 + (60 + extra)) ts} {n : ℕ}
    (stream count driver input witness : List Bool) (sc sc' : ℕ → List Bool)
    (h : Step M n (fun _ => 0) (bank stream count driver input witness sc)
      (fun _ => 0) (bank stream count driver input witness sc'))
    (i : Fin (218 + (60 + extra))) (hi : 278 ≤ i.val) (hne : sc i.val ≠ []) :
    sc' i.val ≠ [] := by
  intro hnil
  apply hne
  have hlen := round_scratch_grows stream count driver input witness sc sc' h i hi
  rw [hnil] at hlen
  cases hsc : sc i.val with
  | nil => rfl
  | cons a as =>
      exfalso
      rw [hsc] at hlen
      simp at hlen

/-! ## §4 The bank lift: a docked stage on the band IS a round step -/

/-- The scratch function read off an ambient bank-width tape function. -/
noncomputable def scratchOf (extra : ℕ) (A : Fin (218 + (60 + extra)) → List Bool)
    (s : ℕ → List Bool) : ℕ → List Bool :=
  fun v => if h : v < 218 + (60 + extra) then A ⟨v, h⟩ else s v

theorem scratchOf_apply (extra : ℕ) (A : Fin (218 + (60 + extra)) → List Bool)
    (s : ℕ → List Bool) (i : Fin (218 + (60 + extra))) :
    scratchOf extra A s i.val = A i := by
  unfold scratchOf
  rw [dif_pos i.isLt]

/-- **A tape function that agrees with a bank below `278` IS a bank.**  This is
the frame clause of the scratch band, and it is what lets a docked stage's exit
be read back as a round bank rather than as an opaque tape function. -/
theorem bank_of_agree_below (extra : ℕ) (stream count driver input witness : List Bool)
    (s : ℕ → List Bool) (A : Fin (218 + (60 + extra)) → List Bool)
    (hoff : ∀ i : Fin (218 + (60 + extra)), i.val < 278 →
      A i = bank stream count driver input witness s i) :
    A = bank stream count driver input witness (scratchOf extra A s) := by
  funext i
  by_cases h : i.val < 278
  · rw [hoff i h]
    show bankAt stream count driver input witness s i.val
      = bankAt stream count driver input witness (scratchOf extra A s) i.val
    unfold bankAt
    split_ifs <;> first | rfl | omega
  · rw [bank_scratch_apply stream count driver input witness (scratchOf extra A s) i
      (Nat.le_of_not_lt h)]
    exact (scratchOf_apply extra A s i).symm

/-- An exit head function that is pointwise zero is the parked head function. -/
theorem step_heads_parked {t s : ℕ} {M : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A B : Fin t → List Bool} (h : Step M n H A H' B) (hz : ∀ i, H' i = 0) :
    Step M n H A (fun _ => 0) B := by
  have he : H' = fun _ => 0 := funext hz
  rwa [he] at h

theorem round_step_of_dock (extra : ℕ) {ts r : ℕ} {M : Machine (218 + (60 + extra)) ts}
    (fuel : ℕ) (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (slots : Fin r → Fin (218 + (60 + extra))) (hband : ∀ j, 278 ≤ (slots j).val)
    (H' : Fin (218 + (60 + extra)) → ℕ) (A' : Fin (218 + (60 + extra)) → List Bool)
    (hstep : Step M fuel (fun _ => 0) (bank stream count driver input witness s) H' A')
    (hzero : ∀ i, H' i = 0)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      A' i = bank stream count driver input witness s i) :
    Step M fuel (fun _ => 0) (bank stream count driver input witness s) (fun _ => 0)
      (bank stream count driver input witness (scratchOf extra A' s)) := by
  have hoff : ∀ i : Fin (218 + (60 + extra)), i.val < 278 →
      A' i = bank stream count driver input witness s i := by
    intro i hi
    refine hframe i (fun j hj => ?_)
    have := hband j
    rw [hj] at this
    omega
  have hb := bank_of_agree_below extra stream count driver input witness s A' hoff
  rw [← hb]
  exact step_heads_parked hstep hzero

/-! ## §4b The discipline itself: a blank band above a moving line -/

/-- **The scratch discipline a round machine can actually maintain.**  The band is
blank from `line` up.  Contrast a LENGTH BOUND, which `round_band_dirty_persists`
(§3) shows buys nothing: no round can shorten what it received, so the only
invariant a round can restore is blankness of tapes it has not yet touched. -/
def BlankFrom (line : ℕ) (s : ℕ → List Bool) : Prop := ∀ v, line ≤ v → s v = []

/-- **The discipline is maintained.**  A round whose docked stages all sit inside
the block `[line, line + block)` hands the next round a band that is blank from
`line + block` up.  So the invariant of §6 can be taken to be
`fun k s => BlankFrom (line + k * block) s`, every round gets the blank slots
`answer_bank_dock` and the rest of the docked-engine library demand, and nothing
ever has to be erased. -/
theorem blankFrom_scratchOf (extra line block : ℕ) (hline : 278 ≤ line)
    {r : ℕ} (slots : Fin r → Fin (218 + (60 + extra)))
    (hlow : ∀ j, (slots j).val < line + block)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : BlankFrom line s) (A : Fin (218 + (60 + extra)) → List Bool)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      A i = bank stream count driver input witness s i) :
    BlankFrom (line + block) (scratchOf extra A s) := by
  intro v hv
  have hv278 : 278 ≤ v := by omega
  by_cases hlt : v < 218 + (60 + extra)
  · have hoff : ∀ j, slots j ≠ (⟨v, hlt⟩ : Fin (218 + (60 + extra))) := by
      intro j hj
      have hj' : (slots j).val = v := by rw [hj]
      have hb := hlow j
      omega
    rw [scratchOf_apply extra A s ⟨v, hlt⟩, hframe _ hoff,
      bank_scratch_apply stream count driver input witness s ⟨v, hlt⟩ hv278]
    exact hs v (by omega)
  · unfold scratchOf
    rw [dif_neg hlt]
    exact hs v (by omega)

/-! ## §5 The answer channel, on the bank

`answer` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is
`rowAnswer rows arity factors * denominator arity scale / rowDenominator rows arity factors`
-- A.13.9's ratio (`paper.tex:3158-3166`) carried to the uniform denominator. -/

/-- `answer_dock`'s budget, named. -/
def answerFuel (a b : ℕ) : ℕ := 2 * (a * (2 * b + 3) + 2) + 2 + 1 + (8 * (a * b) + 6)

/-- `answer` is literally the floor quotient `answer_dock` computes. -/
theorem answer_eq {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity scale : ℕ)
    (factors : List (Circuit arity)) :
    C10SupplierWidth.answer rows arity scale factors
      = rowAnswer rows arity factors * C10SupplierWidth.denominator arity scale
          / rowDenominator rows arity factors := rfl

/-- **The supplier count's arithmetic, inside the C.10 bank.**  One `Step` of one
machine, entered and left with every head parked at `0`, carries the bank whose
band holds `rowAnswer` in unary, the uniform denominator as a
`CompareMachine.word` and `rowDenominator` as a `UnaryTemplate.tape`, to the bank
whose band holds `List.replicate (C10SupplierWidth.answer rows arity scale factors) true`
-- the AND-four CAPP estimate of `paper.tex:3555-3557` in the record's answer
channel.  The six ports and every other tape below `278` are untouched, because
every slot is on the band.

**The blank hypotheses `h2`, `h3`, `h5`, `h6` are the point of §3**: they are
satisfiable only if the incoming scratch is blank on those slots, which
`Appends`'s `∀ s` (`Proof/CaseAnalysis/FinalRoundEmitter.lean`) never is. -/
theorem answer_bank_dock (extra : ℕ) {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity scale : ℕ)
    (factors : List (Circuit arity))
    (slots : Fin 7 → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val = List.replicate (rowAnswer rows arity factors) true)
    (h1 : s (slots 1).val = CompareMachine.word (C10SupplierWidth.denominator arity scale))
    (h2 : s (slots 2).val = [])
    (h3 : s (slots 3).val = [])
    (h4 : s (slots 4).val = UnaryTemplate.tape (rowDenominator rows arity factors))
    (h5 : s (slots 5).val = [])
    (h6 : s (slots 6).val = []) :
    ∃ s' : ℕ → List Bool,
      Step (answerMachine slots)
        (answerFuel (rowAnswer rows arity factors)
          (C10SupplierWidth.denominator arity scale))
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s') ∧
      s' (slots 5).val =
        List.replicate (C10SupplierWidth.answer rows arity scale factors) true := by
  have hA : ∀ j : Fin 7, bank stream count driver input witness s (slots j) = s (slots j).val :=
    fun j => bank_scratch_apply stream count driver input witness s (slots j) (hband j)
  obtain ⟨H', A', hstep, hzero, _r0, _r1, _r4, r5, hframe⟩ :=
    answer_dock (rowAnswer rows arity factors) (C10SupplierWidth.denominator arity scale)
      (rowDenominator rows arity factors) (C10SupplierWidth.rowDenominator_pos rows arity factors) slots hinj
      (fun _ => 0) (bank stream count driver input witness s) (fun _ => rfl)
      ((hA 0).trans h0) ((hA 1).trans h1) ((hA 2).trans h2) ((hA 3).trans h3)
      ((hA 4).trans h4) ((hA 5).trans h5) ((hA 6).trans h6)
  refine ⟨scratchOf extra A' s, ?_, ?_⟩
  · exact round_step_of_dock extra (answerFuel (rowAnswer rows arity factors)
      (C10SupplierWidth.denominator arity scale)) stream count driver input witness s slots hband
      H' A' hstep hzero
      hframe
  · rw [scratchOf_apply extra A' s (slots 5), answer_eq]
    exact r5

/-! ## §6 The residual that composes -/

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

def Rounds (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop) : Prop :=
  ∀ (k : ℕ) (s : ℕ → List Bool), Inv k s →
    ∃ s' : ℕ → List Bool, Inv (k + 1) s' ∧
      Step body cost (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s k)
        (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s' (k + 1))

theorem rounds_iff_emits (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool) :
    Rounds extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness (fun _ _ => True)
      ↔ Emits extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness := by
  constructor
  · intro h k s
    obtain ⟨s', _, hstep⟩ := h k s trivial
    exact ⟨s', hstep⟩
  · intro h k s _
    obtain ⟨s', hstep⟩ := h k s
    exact ⟨s', trivial, hstep⟩

/-- **The per-round choices, chained with the invariant carried along.**  The only
place a choice principle enters this module. -/
theorem chain_of_rounds (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (hrounds : Rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv)
    (w : ℕ → List Bool) (hw : Inv 0 w) :
    ∃ scratch : ℕ → ℕ → List Bool, scratch 0 = w ∧
      ∀ k : ℕ, Step body cost (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness (scratch k) k)
        (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness (scratch (k + 1)) (k + 1)) := by
  classical
  have hchoice : ∀ (k : ℕ) (s : ℕ → List Bool), ∃ s' : ℕ → List Bool,
      Inv k s → Inv (k + 1) s' ∧
        Step body cost (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s k)
          (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1)) := by
    intro k s
    by_cases hk : Inv k s
    · obtain ⟨s', hinv, hstep⟩ := hrounds k s hk
      exact ⟨s', fun _ => ⟨hinv, hstep⟩⟩
    · exact ⟨s, fun hc => absurd hc hk⟩
  choose g hg using hchoice
  refine ⟨fun k => Nat.rec (motive := fun _ => ℕ → List Bool) w (fun j b => g j b) k, rfl, ?_⟩
  have hinv : ∀ k : ℕ,
      Inv k (Nat.rec (motive := fun _ => ℕ → List Bool) w (fun j b => g j b) k) := by
    intro k
    induction k with
    | zero => exact hw
    | succ k ih => exact ((hg k _) ih).1
  intro k
  exact ((hg k _) (hinv k)).2

theorem callsReady_of_rounds (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hrounds : Rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv)
    (hpre : ∃ w : ℕ → List Bool, Inv 0 w ∧
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
  obtain ⟨w, hw, hstep⟩ := hpre
  obtain ⟨scratch, hs0, hchain⟩ :=
    chain_of_rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv hrounds w hw
  refine C10EnvelopeCounter.callsReady_at_clauseWidth extra pre body answer denominator phase
    pcpp coordinate systematicAtom entryWidth callCount preFuel cost clauseDegree q input witness
    (fun _ => fun _ => 0) scratch hlen hfit ?_ ?_ ?_
  · show Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (motive := fun _ => List Bool)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))
    rw [loopBank_roundBank, hs0, roundBank_zero]
    exact hstep
  · intro address _
    simpa only [loopBank_roundBank] using hchain address
  · intro address _ _
    simpa only [loopBank_roundBank] using hchain address

/-- **The old route is recovered.**  `Appends`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`) gives `Rounds` at the trivial
invariant, so `callsReady_of_appends`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`) factors through
`callsReady_of_rounds`: the invariant form strictly subsumes it. -/
theorem rounds_of_appends (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hdet : C10RoundEmitter.AddressDeterminacy answer denominator phase pcpp coordinate
      systematicAtom)
    (happends : C10RoundEmitter.Appends extra body cost entryWidth input witness
      (C10RoundEmitter.nextRecords answer denominator phase pcpp coordinate systematicAtom)
      (C10RoundEmitter.Reachable answer denominator phase pcpp coordinate systematicAtom)) :
    Rounds extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness (fun _ _ => True) :=
  (rounds_iff_emits extra body cost entryWidth answer denominator phase pcpp coordinate
    systematicAtom input witness).2
    (C10RoundEmitter.emits_of_appends_of_determinacy extra body cost entryWidth answer
      denominator phase pcpp coordinate systematicAtom input witness hdet happends)

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
