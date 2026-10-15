import Proof.CaseAnalysis.FinalNativeReload
import Proof.CaseAnalysis.FinalSiteBodyUniform

namespace NearCubicWires.RepairSource.CloseoutFinal.C10RoundEmitter

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 Two facts about the primitives, neither of which is new mathematics -/

theorem step_tapes_det {t s : ℕ} {p : Machine t s} {n : ℕ} {hin : Fin t → ℕ}
    {tin : Fin t → List Bool} {h₁ h₂ : Fin t → ℕ} {t₁ t₂ : Fin t → List Bool}
    (hstep : Step p n hin tin h₁ t₁) (hstep' : Step p n hin tin h₂ t₂) : t₁ = t₂ := by
  obtain ⟨r, hr, _, ht, _⟩ := hstep
  obtain ⟨r', hr', _, ht', _⟩ := hstep'
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  rw [← ht, ← ht', hrr]

/-- The count port's word determines the count.  `CompareMachine.word`
(`Proof/PCP/VerifierDecodingCompare.lean`) is `false :: List.replicate n true`. -/
theorem word_inj {n m : ℕ} (hword : CompareMachine.word n = CompareMachine.word m) : n = m := by
  have hlen := congrArg List.length hword
  simpa [CompareMachine.word] using hlen

/-! ## §2 The side condition `Emits` carries, and the refutation it implies -/

/-- **`Emits` forces the round's delta to be a function of the accumulated
stream.**  If two rounds present the SAME record list at the data port then the
bank they present is literally the same function, so the deterministic body
produces the same exit bank, so the two rounds must append the same words and
the same number of records.

Nothing here is about the emitter's cleverness: it is a property of the type
`Emits`, and any construction that inhabits `Emits` proves it as a side
effect. -/
theorem emits_delta_det (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hemits : Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness)
    (k₁ k₂ : ℕ)
    (hprefix : prefixRecords answer denominator phase pcpp coordinate systematicAtom k₁
      = prefixRecords answer denominator phase pcpp coordinate systematicAtom k₂) :
    CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (addressRecords answer denominator phase pcpp coordinate systematicAtom k₁)
      = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (addressRecords answer denominator phase pcpp coordinate systematicAtom k₂) ∧
      (addressRecords answer denominator phase pcpp coordinate systematicAtom k₁).length
        = (addressRecords answer denominator phase pcpp coordinate systematicAtom k₂).length := by
  obtain ⟨s₁, hstep₁⟩ := hemits k₁ (fun _ => [])
  obtain ⟨s₂, hstep₂⟩ := hemits k₂ (fun _ => [])
  have hentry : roundBank extra entryWidth answer denominator phase pcpp coordinate
        systematicAtom input witness (fun _ => []) k₂
      = roundBank extra entryWidth answer denominator phase pcpp coordinate
        systematicAtom input witness (fun _ => []) k₁ := by
    unfold roundBank
    rw [hprefix]
  rw [hentry] at hstep₂
  have hout := step_tapes_det hstep₁ hstep₂
  have h81 := congrFun hout (⟨81, by omega⟩ : Fin (218 + (60 + extra)))
  have h90 := congrFun hout (⟨90, by omega⟩ : Fin (218 + (60 + extra)))
  rw [roundBank_data extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness s₁ (k₁ + 1) ⟨81, by omega⟩ rfl,
    roundBank_data extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness s₂ (k₂ + 1) ⟨81, by omega⟩ rfl] at h81
  rw [roundBank_count extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness s₁ (k₁ + 1) ⟨90, by omega⟩ rfl,
    roundBank_count extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness s₂ (k₂ + 1) ⟨90, by omega⟩ rfl] at h90
  rw [prefixRecords_succ, prefixRecords_succ, words_append, words_append, hprefix] at h81
  have hlen := word_inj h90
  rw [prefixRecords_succ, prefixRecords_succ, List.length_append, List.length_append,
    hprefix] at hlen
  exact ⟨List.append_cancel_left h81, by omega⟩

/-- **An address that emits nothing forces the next one to emit nothing.**  The
prefix does not move across an empty address, so the body cannot tell the two
rounds apart. -/
theorem emits_nil_absorbing (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hemits : Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness)
    (k : ℕ)
    (hnil : addressRecords answer denominator phase pcpp coordinate systematicAtom k = []) :
    addressRecords answer denominator phase pcpp coordinate systematicAtom (k + 1) = [] := by
  have hprefix : prefixRecords answer denominator phase pcpp coordinate systematicAtom k
      = prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1) := by
    rw [prefixRecords_succ, hnil, List.append_nil]
  obtain ⟨-, hlen⟩ := emits_delta_det extra body cost entryWidth answer denominator phase pcpp
    coordinate systematicAtom input witness hemits k (k + 1) hprefix
  rw [hnil] at hlen
  exact List.eq_nil_of_length_eq_zero hlen.symm

/-- **The refutation, stated so a builder can check it before writing a machine.**
One clause address that emits no record followed by one that emits a record
makes `Emits` uninhabitable at those parameters, whatever the machine and
whatever the budget. -/
theorem not_emits_of_nil_then_ne_nil (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (k : ℕ)
    (hnil : addressRecords answer denominator phase pcpp coordinate systematicAtom k = [])
    (hne : addressRecords answer denominator phase pcpp coordinate systematicAtom (k + 1) ≠ []) :
    ¬ Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness := by
  intro hemits
  exact hne (emits_nil_absorbing extra body cost entryWidth answer denominator phase pcpp
    coordinate systematicAtom input witness hemits k hnil)

/-! ## §2a The length gate: `length_mono` does NOT refute `Emits` -/

/-- **The constraint, instantiated.**  `length_mono`
(`Proof/CaseAnalysis/FinalNativeReload.lean`) says a `Step` never shortens a tape, so `Emits`
cannot be inhabited unless every tape of `roundBank` is non-decreasing from `k` to `k + 1`. -/
theorem emits_length_necessary (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hemits : Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness)
    (k : ℕ) (s : ℕ → List Bool) :
    ∃ s' : ℕ → List Bool, ∀ i : Fin (218 + (60 + extra)),
      (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k i).length
        ≤ (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s' (k + 1) i).length := by
  obtain ⟨s', hstep⟩ := hemits k s
  exact ⟨s', fun i => C10NativeReload.length_mono hstep i⟩

/-- **The check, and it PASSES.**  On the whole `278` prefix -- the part `Emits` pins and where the
existential outgoing scratch cannot rescue a shrink -- the round bank never gets shorter, at ANY
pair of scratch snapshots.  The data port grows by an append (`prefixRecords_succ`,
`Proof/CaseAnalysis/FinalSupplierCall.lean`, and `words_append`, `:268`); the count port is
`false :: List.replicate n true` at a non-decreasing `n`; tapes `0`, `1`, `216` and `218` are
identical at the two rounds and every other tape of the prefix is blank at both.

So `length_mono` is a real constraint on `Emits` and `Emits` satisfies it; the obstruction of §2 is
the one that bites, and it is a different one. -/
theorem roundBank_length_mono (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s s' : ℕ → List Bool) (k : ℕ) (i : Fin (218 + (60 + extra))) (hi : i.val < 278) :
    (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k i).length
      ≤ (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s' (k + 1) i).length := by
  have hgrow : (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length
      ≤ (prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1)).length := by
    rw [prefixRecords_succ, List.length_append]
    omega
  have hwords : (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom k)).length
      ≤ (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1))).length := by
    rw [prefixRecords_succ, words_append, List.length_append]
    omega
  unfold roundBank bank bankAt
  split_ifs <;> first
    | exact le_refl _
    | exact hwords
    | (simp only [CompareMachine.word, List.length_cons, List.length_replicate]; omega)
    | omega

/-! ## §3 The emptiness is not a phantom -/

/-- One record per monomial, so the address emits nothing exactly when its site
polynomial has no monomial. -/
theorem siteRecords_eq_nil_iff (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) :
    siteRecords answer denominator phase pcpp coordinate systematicAtom address = []
      ↔ (siteCalls phase pcpp coordinate systematicAtom address).monomials = [] := by
  unfold siteRecords callRecords
  exact List.map_eq_nil_iff

/-- **An empty site is reachable.**  `momentSite`
(`Proof/CaseAnalysis/FinalExactness.lean`) is `secondMomentPolynomial` of one
recovered coordinate, i.e. that coordinate's polynomial multiplied by itself,
and `CircuitPolynomial.mul` (`Proof/Circuits/ComponentwisePolynomial.lean`) is a
`flatMap` over the left monomials.  A coordinate family with no monomials is
admitted by the seam -- `coordinateExpands_self`
(`Proof/CaseAnalysis/FinalExactness.lean`) shows `CoordinateExpands` is a
statement about VALUES and constrains no monomial list -- so §2's hypothesis
`addressRecords ... k = []` is not vacuous. -/
theorem momentSite_monomials_nil (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (hnil : ∀ j, (coordinate j).monomials = [])
    (address : Fin (2 ^ pcpp.clauseBits)) :
    (momentSite pcpp coordinate address).monomials = [] := by
  simp [momentSite, CircuitPolynomial.weaken, secondMomentPolynomial, CircuitPolynomial.mul, hnil]

/-! ## §4 The side condition, named, and the fact that discharges it -/

/-- **The datum an emitter cannot do without.**  §2 shows `Emits` implies the
`words`-and-length form of this; this is its list form, and it is what SS5's
reduction consumes. -/
def AddressDeterminacy (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) : Prop :=
  ∀ k₁ k₂ : ℕ,
    prefixRecords answer denominator phase pcpp coordinate systematicAtom k₁
        = prefixRecords answer denominator phase pcpp coordinate systematicAtom k₂ →
      addressRecords answer denominator phase pcpp coordinate systematicAtom k₁
        = addressRecords answer denominator phase pcpp coordinate systematicAtom k₂

/-- Every active round appends at least one record. -/
theorem addressRecords_length_pos (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hne : ∀ address : Fin (2 ^ pcpp.clauseBits),
      (siteCalls phase pcpp coordinate systematicAtom address).monomials ≠ [])
    (k : ℕ) (hk : k < 2 ^ pcpp.clauseBits) :
    0 < (addressRecords answer denominator phase pcpp coordinate systematicAtom k).length := by
  obtain ⟨address, haddress⟩ :=
    addressRecords_site answer denominator phase pcpp coordinate systematicAtom k hk
  rw [haddress]
  refine Nat.pos_of_ne_zero (fun hzero => hne address ?_)
  exact (siteRecords_eq_nil_iff answer denominator phase pcpp coordinate systematicAtom
    address).mp (List.eq_nil_of_length_eq_zero hzero)

/-- One active round strictly lengthens the prefix. -/
theorem prefixRecords_length_lt (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hne : ∀ address : Fin (2 ^ pcpp.clauseBits),
      (siteCalls phase pcpp coordinate systematicAtom address).monomials ≠ [])
    (k : ℕ) (hk : k < 2 ^ pcpp.clauseBits) :
    (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length
      < (prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1)).length := by
  have hpos := addressRecords_length_pos answer denominator phase pcpp coordinate systematicAtom
    hne k hk
  rw [prefixRecords_succ, List.length_append]
  omega

/-- The prefix length is strictly increasing up to the address count. -/
theorem prefixRecords_length_strictMono (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hne : ∀ address : Fin (2 ^ pcpp.clauseBits),
      (siteCalls phase pcpp coordinate systematicAtom address).monomials ≠ [])
    (k₁ k₂ : ℕ) (hlt : k₁ < k₂) (hle : k₂ ≤ 2 ^ pcpp.clauseBits) :
    (prefixRecords answer denominator phase pcpp coordinate systematicAtom k₁).length
      < (prefixRecords answer denominator phase pcpp coordinate systematicAtom k₂).length := by
  induction k₂ with
  | zero => omega
  | succ n inductionHypothesis =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hcase | hcase
      · exact lt_trans (inductionHypothesis hcase (by omega))
          (prefixRecords_length_lt answer denominator phase pcpp coordinate systematicAtom
            hne n (by omega))
      · subst hcase
        exact prefixRecords_length_lt answer denominator phase pcpp coordinate systematicAtom
          hne k₁ (by omega)

/-- **The side condition, discharged from one nonemptiness fact.**  If every
clause address's site polynomial has a monomial then the accumulated stream
determines the round, and §5's reduction applies. -/
theorem addressDeterminacy_of_nonempty (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hne : ∀ address : Fin (2 ^ pcpp.clauseBits),
      (siteCalls phase pcpp coordinate systematicAtom address).monomials ≠ []) :
    AddressDeterminacy answer denominator phase pcpp coordinate systematicAtom := by
  have key : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ →
      prefixRecords answer denominator phase pcpp coordinate systematicAtom k₁
          = prefixRecords answer denominator phase pcpp coordinate systematicAtom k₂ →
        addressRecords answer denominator phase pcpp coordinate systematicAtom k₁
          = addressRecords answer denominator phase pcpp coordinate systematicAtom k₂ := by
    intro k₁ k₂ hle hprefix
    rcases Nat.lt_or_ge k₁ (2 ^ pcpp.clauseBits) with hactive | hpast
    · rcases Nat.eq_or_lt_of_le hle with hEq | hlt
      · rw [hEq]
      · exfalso
        rcases Nat.lt_or_ge k₂ (2 ^ pcpp.clauseBits) with hk₂ | hk₂
        · have hmono := prefixRecords_length_strictMono answer denominator phase pcpp coordinate
            systematicAtom hne k₁ k₂ hlt (le_of_lt hk₂)
          rw [hprefix] at hmono
          omega
        · have hsat₂ := C10EnvelopeCounter.prefixRecords_saturate answer denominator phase pcpp
            coordinate systematicAtom hk₂
          have hsatc := C10EnvelopeCounter.prefixRecords_saturate answer denominator phase pcpp
            coordinate systematicAtom (le_refl (2 ^ pcpp.clauseBits))
          have hsame : (prefixRecords answer denominator phase pcpp coordinate
                systematicAtom k₂).length
              = (prefixRecords answer denominator phase pcpp coordinate systematicAtom
                (2 ^ pcpp.clauseBits)).length := by
            rw [hsat₂, hsatc]
          have hmono := prefixRecords_length_strictMono answer denominator phase pcpp coordinate
            systematicAtom hne k₁ (2 ^ pcpp.clauseBits) hactive (le_refl _)
          rw [hprefix] at hmono
          omega
    · rw [C10EnvelopeCounter.addressRecords_past_end answer denominator phase pcpp coordinate
        systematicAtom hpast,
      C10EnvelopeCounter.addressRecords_past_end answer denominator phase pcpp coordinate
        systematicAtom (le_trans hpast hle)]
  intro k₁ k₂ hprefix
  rcases Nat.le_total k₁ k₂ with hle | hle
  · exact key k₁ k₂ hle hprefix
  · exact (key k₂ k₁ hle hprefix.symm).symm

/-! ## §5 The k-free residual -/

/-- The record lists a round of the loop can actually present at the data
port. -/
def Reachable (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (xs : List Entry) : Prop :=
  ∃ k : ℕ, xs = prefixRecords answer denominator phase pcpp coordinate systematicAtom k

/-- **The round obligation with the round index removed.**  The machine is
handed the record list currently at the data port and must append `next` of it,
leaving the count port consistent, every other tape of the `278` prefix
untouched (that is what `bank`, `Proof/CaseAnalysis/FinalSupplierCall.lean`,
says) and choosing its own outgoing scratch.  The incoming scratch is
universal, so a round program must blank whatever private tapes it uses. -/
def Appends (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (input witness : List Bool)
    (next : List Entry → List Entry) (reach : List Entry → Prop) : Prop :=
  ∀ xs : List Entry, reach xs → ∀ s : ℕ → List Bool, ∃ s' : ℕ → List Bool,
    Step body cost (fun _ => 0)
      (bank (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth xs)
        (CompareMachine.word xs.length) (List.replicate entryWidth true) input witness s)
      (fun _ => 0)
      (bank (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth (xs ++ next xs))
        (CompareMachine.word (xs ++ next xs).length) (List.replicate entryWidth true)
        input witness s')

/-- **`Appends` produces `Emits`.**  No hypothesis beyond the two that say the
`next` the machine implements is the schedule's own address expansion. -/
theorem emits_of_appends (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (next : List Entry → List Entry) (reach : List Entry → Prop)
    (happends : Appends extra body cost entryWidth input witness next reach)
    (hreach : ∀ k : ℕ, reach (prefixRecords answer denominator phase pcpp coordinate
      systematicAtom k))
    (hnext : ∀ k : ℕ,
      next (prefixRecords answer denominator phase pcpp coordinate systematicAtom k)
        = addressRecords answer denominator phase pcpp coordinate systematicAtom k) :
    Emits extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness := by
  intro k s
  obtain ⟨s', hstep⟩ := happends _ (hreach k) s
  refine ⟨s', ?_⟩
  have hsucc : prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1)
      = prefixRecords answer denominator phase pcpp coordinate systematicAtom k
        ++ next (prefixRecords answer denominator phase pcpp coordinate systematicAtom k) := by
    rw [prefixRecords_succ, hnext]
  show Step body cost (fun _ => 0)
    (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness s k)
    (fun _ => 0)
    (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness s' (k + 1))
  unfold roundBank
  rw [hsucc]
  exact hstep

section ClassicalNext
open scoped Classical

/-- **The canonical `next`.**  Under `AddressDeterminacy` the accumulated stream
names the round, so the schedule's expansion IS a function of the stream.  This
is the only place a choice principle enters the module's data. -/
noncomputable def nextRecords (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (xs : List Entry) : List Entry :=
  if h : ∃ k : ℕ, prefixRecords answer denominator phase pcpp coordinate systematicAtom k = xs then
    addressRecords answer denominator phase pcpp coordinate systematicAtom h.choose
  else []

end ClassicalNext

theorem nextRecords_prefix (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hdet : AddressDeterminacy answer denominator phase pcpp coordinate systematicAtom) (k : ℕ) :
    nextRecords answer denominator phase pcpp coordinate systematicAtom
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom k)
      = addressRecords answer denominator phase pcpp coordinate systematicAtom k := by
  unfold nextRecords
  split_ifs with hex
  · exact hdet _ _ hex.choose_spec
  · exact absurd ⟨k, rfl⟩ hex

/-- **`Emits` from the k-free obligation, at the canonical `next`.** -/
theorem emits_of_appends_of_determinacy (extra : ℕ) {bs : ℕ}
    (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hdet : AddressDeterminacy answer denominator phase pcpp coordinate systematicAtom)
    (happends : Appends extra body cost entryWidth input witness
      (nextRecords answer denominator phase pcpp coordinate systematicAtom)
      (Reachable answer denominator phase pcpp coordinate systematicAtom)) :
    Emits extra body cost entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness :=
  emits_of_appends extra body cost entryWidth answer denominator phase pcpp coordinate
    systematicAtom input witness _ _ happends (fun k => ⟨k, rfl⟩)
    (nextRecords_prefix answer denominator phase pcpp coordinate systematicAtom hdet)

/-- **And back: nothing is lost by building against the k-free form.**  Under
the same side condition `Emits` delivers `Appends`, so the reduction of §5 is an
equivalence and a builder may work at the stream level without weakening the
deliverable. -/
theorem appends_of_emits (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (hdet : AddressDeterminacy answer denominator phase pcpp coordinate systematicAtom)
    (hemits : Emits extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness) :
    Appends extra body cost entryWidth input witness
      (nextRecords answer denominator phase pcpp coordinate systematicAtom)
      (Reachable answer denominator phase pcpp coordinate systematicAtom) := by
  rintro xs ⟨k, rfl⟩ s
  obtain ⟨s', hstep⟩ := hemits k s
  refine ⟨s', ?_⟩
  have hsucc : prefixRecords answer denominator phase pcpp coordinate systematicAtom k
        ++ nextRecords answer denominator phase pcpp coordinate systematicAtom
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k)
      = prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1) := by
    rw [nextRecords_prefix answer denominator phase pcpp coordinate systematicAtom hdet,
      prefixRecords_succ]
  rw [hsucc]
  exact hstep

/-! ## §6 The consumer, reached from the k-free obligation -/

theorem callsReady_of_appends (extra : ℕ) {ps bs : ℕ}
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
    (hdet : AddressDeterminacy answer denominator phase pcpp coordinate systematicAtom)
    (happends : Appends extra body cost entryWidth input witness
      (nextRecords answer denominator phase pcpp coordinate systematicAtom)
      (Reachable answer denominator phase pcpp coordinate systematicAtom))
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
      input witness :=
  callsReady_of_emits extra pre body answer denominator phase pcpp coordinate systematicAtom
    entryWidth callCount preFuel cost clauseDegree q input witness hlen hfit
    (emits_of_appends_of_determinacy extra body cost entryWidth answer denominator phase pcpp
      coordinate systematicAtom input witness hdet happends)
    hpre

end NearCubicWires.RepairSource.CloseoutFinal.C10RoundEmitter
