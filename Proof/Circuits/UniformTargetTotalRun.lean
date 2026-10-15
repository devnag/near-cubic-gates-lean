import Proof.MachineModel.BankDispatchedTargetBody
import Proof.MachineModel.BankFramedTargetChains
import Proof.MachineModel.CanonicalBooleanizeProgram

/-!
# The uniform target program is total: `hrun` and `hboolean` without a case premise

`ExecutableInterfaces.executableLanguageProgramOfRun` — and therefore both
`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` and its fixed-rate
twin — charges two obligations that are quantified over **every** request:

* `hrun  : ∀ request, runNPOracleProgram (uniformTargetProgram …) … = some (output request)`
* `hboolean : ∀ request, output request ≤ 1`

Neither carries a schedule premise.  They therefore hold at off-diagonal
lengths, at malformed point codes, and at targets below the Case-1 onset, where
`bodyRun` says nothing at all.  `bodyRun` is *not* a supplier for them and
structurally cannot become one: its conclusion is guarded by `hlarge`, `hyes`,
`hrejects` and `haccepts`.

## The design verdict: what a bad request does

`LanguageEvaluationRequest` is `⟨inputArity, input⟩`, so *every* request is a
`⟨target, input⟩` with `code = encodeBitInput input`; there are no malformed
requests at the type level.  What varies is whether the request's length is on
the schedule's diagonal.  The stream reacts to that as follows.

1. The numeral bank runs.  `run_publishedScheduleNumeralBankProgram` is
   unconditional in the length, so the bank always halts and always leaves the
   frame `pair sourceLength (pair width (pair queryCount (pair copies code)))`.
   Off the diagonal the four numerals are simply the length-decoded ones; they
   are *wrong* for no request, because the bank defines them.
2. The dispatcher runs the selector and reads its tag.  `taggedProgramChoice`
   has exactly **two** branches, `tag = 0` and `tag ≠ 0`, and both are total —
   there is no third path and hence no fail-closed default to write: the
   dispatcher is already fail-closed by exhaustion.
3. The chosen chain is restarted on the retained code.  The bank-frame
   projection `bankFramedChainProgram` reads only the innermost right
   projection, so it too is diagonal-free.

Consequently the *only* thing separating `hrun`/`hboolean` from the closed tree
is a **halting-with-a-boolean** fact for the three streams that are still free
program binders in the integration: the selector (through the emitter and the
free atom `table`), and the two chains.  Everything above them is discharged
here, unconditionally.

`output` is then not a semantic choice at all: it is *defined* by the program
(`totalTargetOutput` below).  The semantic identification stays where it
belongs — inside `huniform`, which `ExecutableTargetLanguagePackaging.output_eq_of_run`
combines with `hrun` on the diagonal.  This module therefore **subsumes**
nothing of `BankDiagonalBodyClosure.inverse_bodyRun_ofDiagonalCluster`; it is
its total complement.

## Layout

* §1 the total-run predicate and the output it defines.
* §2 the numeral bank's link, unconditional in the request.
* §3 the two-branch dispatcher, unconditional in the tag.
* §4 the bank-frame projection in front of a chain, unconditional in the length.
* §4b booleanness for free, behind `CanonicalBooleanizeProgram`, at no cost on
  the diagonal — so the residue below is *halting*, not *halting with a bit*.
* §5 the inverse schedule's `hrun`/`hboolean` from three named total premises.
* §6 the fixed schedule, where the body is still one free binder.
* §7 the consumer check: the two obligations leave the bridge's binder list.
-/

namespace NearCubicWires.UniformTargetTotalRun

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBooleanizeProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private branchTargetBitBits_mono_output from
  Proof.MachineModel.BankDispatchedTargetBody

/-! ## §1 Total boolean halting, and the output it defines -/

/-- **The total obligation, in one shape.**  One instruction stream, one width
and fuel envelope, one starting code per request, and a halt at a value in
`{0, 1}` — with no case premise whatsoever.  `frame` selects the code the
stream is started on: `LanguageEvaluationRequest.code` for a stream reading the
request itself, the numeral bank's frame for a stream below the bank. -/
def TotalBooleanRuns (program : NPOracleProgram)
    (bits fuel frame : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest, ∃ value ≤ 1,
    runNPOracleProgram program (bits request) (fuel request)
        (initialNPOracleState (LanguageEvaluationRequest.length request)
          (frame request)) =
      some value

/-- **The output a total stream defines.**  Nothing semantic is chosen here:
the language's value at a request is whatever the certified interpreter
returns there. -/
noncomputable def totalTargetOutput (program : NPOracleProgram)
    (bits fuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  (runNPOracleProgram program (bits request) (fuel request)
      (initialNPOracleState (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))).getD 0

private theorem totalTargetOutput_eq {program : NPOracleProgram}
    {bits fuel : LanguageEvaluationRequest → ℕ}
    {request : LanguageEvaluationRequest} {value : ℕ}
    (hvalue :
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some value) :
    totalTargetOutput program bits fuel request = value := by
  change
    (runNPOracleProgram program (bits request) (fuel request)
        (initialNPOracleState (LanguageEvaluationRequest.length request)
          (LanguageEvaluationRequest.code request))).getD 0 = value
  rw [hvalue]
  rfl

/-- **`hrun`, from totality alone.**  This is verbatim the binder
`ExecutableInterfaces.executableLanguageProgramOfRun` carries. -/
theorem run_eq_totalTargetOutput (program : NPOracleProgram)
    (bits fuel : LanguageEvaluationRequest → ℕ)
    (htotal : TotalBooleanRuns program bits fuel LanguageEvaluationRequest.code)
    (request : LanguageEvaluationRequest) :
    runNPOracleProgram program (bits request) (fuel request)
        (initialNPOracleState (LanguageEvaluationRequest.length request)
          (LanguageEvaluationRequest.code request)) =
      some (totalTargetOutput program bits fuel request) := by
  obtain ⟨value, _hle, hvalue⟩ := htotal request
  rw [totalTargetOutput_eq hvalue]
  exact hvalue

/-- **`hboolean`, from totality alone.** -/
theorem totalTargetOutput_le_one (program : NPOracleProgram)
    (bits fuel : LanguageEvaluationRequest → ℕ)
    (htotal : TotalBooleanRuns program bits fuel LanguageEvaluationRequest.code)
    (request : LanguageEvaluationRequest) :
    totalTargetOutput program bits fuel request ≤ 1 := by
  obtain ⟨value, hle, hvalue⟩ := htotal request
  rw [totalTargetOutput_eq hvalue]
  exact hle

/-! ## §2 The numeral bank's link is unconditional

The bank halts at every public length, so a body that is total at the bank's
frame makes the whole linked stream total at the request itself.  No schedule
numeral, no diagonal and no source index enters. -/

/-- The numeral bank's frame, as a function of the request. -/
noncomputable def publishedFrame
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedBankFrame outer pcppSource rate
    (LanguageEvaluationRequest.length request)
    (LanguageEvaluationRequest.code request)

/-- **The bank link, totalised.** -/
theorem totalBooleanRuns_uniformTargetProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (publishedFrame outer pcppSource rate)) :
    TotalBooleanRuns (uniformTargetProgram outer pcppSource rate body)
      (uniformTargetBits outer pcppSource rate bodyBits)
      (uniformTargetFuel outer pcppSource rate body bodyFuel)
      LanguageEvaluationRequest.code := by
  intro request
  obtain ⟨value, hle, hvalue⟩ := hbody request
  exact ⟨value, hle,
    run_uniformTargetProgram outer pcppSource rate body bodyBits bodyFuel
      (LanguageEvaluationRequest.length request) request.input value hvalue⟩

/-! ## §3 The dispatcher's branch inventory

`BranchTargetLanguageProgram.branchTargetBitProgram` is
`linkPrograms selector (taggedProgramChoice first second)`, and
`taggedProgramChoice` splits on the tag register with `branchZero`.  The
inventory is therefore closed at two entries — `tag = 0` and `tag ≠ 0` — and
both entries are total.  The dispatcher needs no fail-closed default; what it
needs is that the selector's tag fit the width `bankDispatchedBodyBits`
declares, i.e. that it be a *bit*. -/

/-- The published inverse schedule's bank frame. -/
noncomputable def inverseBankFrame (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedFrame (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) request

/-- **The selector's total obligation.**  At every request the selector halts
inside its declared envelope with a *bit* beside the retained bank frame.  The
tag's value is unconstrained: which branch it selects off the diagonal is the
program's business, not the schedule's. -/
def InverseSelectorTotalRuns (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (selector : NPOracleProgram)
    (selectorBits selectorFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest, ∃ tag ≤ 1,
    runNPOracleProgram selector (selectorBits request) (selectorFuel request)
        (initialNPOracleState (LanguageEvaluationRequest.length request)
          (inverseBankFrame contracts clockDepth advantageExponent request)) =
      some
        (Nat.pair tag
          (inverseBankFrame contracts clockDepth advantageExponent request))

set_option maxHeartbeats 1000000 in
-- One case split on the tag; each branch elaborates the dispatcher's whole
-- width tower once.
/-- **The dispatcher, totalised.**  Both admissible tags are covered, so the
body halts with a bit at every request — on or off the schedule's diagonal. -/
theorem totalBooleanRuns_bankDispatchedBodyProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (selector first second : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hselector :
      InverseSelectorTotalRuns contracts clockDepth advantageExponent selector
        selectorBits selectorFuel)
    (hfirst :
      TotalBooleanRuns first chainBits chainFuel
        (inverseBankFrame contracts clockDepth advantageExponent))
    (hsecond :
      TotalBooleanRuns second chainBits chainFuel
        (inverseBankFrame contracts clockDepth advantageExponent)) :
    TotalBooleanRuns (bankDispatchedBodyProgram selector first second)
      (bankDispatchedBodyBits contracts clockDepth advantageExponent
        selectorBits chainBits)
      (bankDispatchedBodyFuel first second selectorFuel chainFuel)
      (inverseBankFrame contracts clockDepth advantageExponent) := by
  intro request
  obtain ⟨tag, htag, hsel⟩ := hselector request
  by_cases hzero : tag = 0
  · subst hzero
    obtain ⟨value, hle, hvalue⟩ := hfirst request
    refine ⟨value, hle, ?_⟩
    have hrun :=
      run_branchTargetBitProgram_caseOne selector first second
        (LanguageEvaluationRequest.length request)
        (inverseBankFrame contracts clockDepth advantageExponent request)
        (selectorBits request) (selectorFuel request) (chainBits request)
        (chainFuel request) value hsel hvalue
    exact run_bits_mono hrun
      ((branchTargetBitBits_mono_output _ _ _ _ _ _ hle).trans
        (Nat.le_max_left _ _))
  · have hone : tag = 1 := by omega
    subst hone
    obtain ⟨value, hle, hvalue⟩ := hsecond request
    refine ⟨value, hle, ?_⟩
    have hrun :=
      run_branchTargetBitProgram_caseTwo selector first second
        (LanguageEvaluationRequest.length request)
        (inverseBankFrame contracts clockDepth advantageExponent request) 1
        (selectorBits request) (selectorFuel request) (chainBits request)
        (chainFuel request) value Nat.one_ne_zero hsel hvalue
    exact run_bits_mono hrun
      ((branchTargetBitBits_mono_output _ _ _ _ _ _ hle).trans
        (Nat.le_max_right _ _))

/-! ## §4 The bank-frame projection is unconditional

`BankFramedTargetChains.bankFramedChainProgram` is five instructions of right
projection in front of a chain.  It reads no schedule numeral, so a chain that
is total at the requested point code is total at the bank's frame. -/

theorem totalBooleanRuns_bankFramedChainProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (chain : NPOracleProgram)
    (chainBits chainFuel framedFuel : LanguageEvaluationRequest → ℕ)
    (hfuel : ∀ request : LanguageEvaluationRequest,
      linkFuel chain 5 (chainFuel request) ≤ framedFuel request)
    (hchain :
      TotalBooleanRuns chain chainBits chainFuel
        LanguageEvaluationRequest.code) :
    TotalBooleanRuns (bankFramedChainProgram chain)
      (bankFramedChainBits contracts clockDepth advantageExponent chainBits)
      framedFuel (inverseBankFrame contracts clockDepth advantageExponent) := by
  intro request
  obtain ⟨value, hle, hvalue⟩ := hchain request
  exact ⟨value, hle,
    run_bankFramedChainProgram_published contracts clockDepth advantageExponent
      request.input hvalue (hfuel request)⟩

/-! ## §4b Booleanness costs nothing

`hboolean` does not need a semantic premise.  A chain that merely *halts*
becomes a boolean chain behind `CanonicalBooleanizeProgram.booleanizedProgram`,
whose suffix is three total instructions; and on the diagonal the wrapper is
transparent, because the canonical target bit is already a `Bool`.  Wrapping the
two chains therefore reduces the §5 residue from *halts with a bit* to *halts*,
without touching `BankFramedTargetChains`' own point-run premises. -/

/-- Halting alone, with no constraint on the value returned. -/
def TotalRuns (program : NPOracleProgram)
    (bits fuel frame : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest, ∃ value : ℕ,
    runNPOracleProgram program (bits request) (fuel request)
        (initialNPOracleState (LanguageEvaluationRequest.length request)
          (frame request)) =
      some value

private theorem one_le_natBitLength (value : ℕ) : 1 ≤ natBitLength value := by
  unfold natBitLength
  omega

/-- **From halting to halting with a bit.** -/
theorem totalBooleanRuns_booleanizedProgram (chain : NPOracleProgram)
    (bits fuel frame : LanguageEvaluationRequest → ℕ)
    (hlength : ∀ request : LanguageEvaluationRequest,
      natBitLength (LanguageEvaluationRequest.length request) ≤ bits request)
    (htotal : TotalRuns chain bits fuel frame) :
    TotalBooleanRuns (booleanizedProgram chain) bits
      (fun request => booleanizedFuel (fuel request)) frame := by
  intro request
  obtain ⟨value, hvalue⟩ := htotal request
  refine ⟨canonicalBooleanizeOutput value, ?_, ?_⟩
  · have hlt := canonicalBooleanizeOutput_lt_two value
    omega
  · exact run_booleanizedProgram
      ((one_le_natBitLength _).trans (hlength request)) (hlength request) hvalue

/-- **The wrapper is transparent on the Case-1 diagonal.** -/
theorem inverseCaseOnePointRuns_booleanized (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (caseOne : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (hlength : ∀ request : LanguageEvaluationRequest,
      natBitLength (LanguageEvaluationRequest.length request) ≤
        chainBits request)
    (hone :
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        caseOne chainBits chainFuel) :
    InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
      (booleanizedProgram caseOne) chainBits
      (fun request => booleanizedFuel (chainFuel request)) := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  exact run_booleanizedProgram_bool
    ((one_le_natBitLength _).trans (hlength ⟨target, input⟩))
    (hlength ⟨target, input⟩)
    (hone target hlarge hyes hrejects haccepts data hbranch input)

/-- **The wrapper is transparent on the Case-2 diagonal.** -/
theorem inverseCaseTwoPointRuns_booleanized (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (hlength : ∀ request : LanguageEvaluationRequest,
      natBitLength (LanguageEvaluationRequest.length request) ≤
        chainBits request)
    (htwo :
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        caseTwo chainBits chainFuel) :
    InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
      (booleanizedProgram caseTwo) chainBits
      (fun request => booleanizedFuel (chainFuel request)) := by
  intro target hlarge hyes hrejects haccepts branchTwo hbranch input
  exact run_booleanizedProgram_bool
    ((one_le_natBitLength _).trans (hlength ⟨target, input⟩))
    (hlength ⟨target, input⟩)
    (htwo target hlarge hyes hrejects haccepts branchTwo hbranch input)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
-- The conclusion is the whole linked assembly; it elaborates once per premise.
/-- **The uniform target program is total.**  This is the census's
`run_uniformTargetProgram_total`: at the published inverse assembly, every
request halts with a boolean, with no case premise on the request. -/
theorem run_uniformTargetProgram_total
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hselector :
      InverseSelectorTotalRuns contracts clockDepth advantageExponent selector
        selectorBits selectorFuel)
    (hcaseOne :
      TotalBooleanRuns caseOne chainBits chainFuel
        LanguageEvaluationRequest.code)
    (hcaseTwo :
      TotalBooleanRuns caseTwo chainBits chainFuel
        LanguageEvaluationRequest.code) :
    TotalBooleanRuns
      (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
          (bankFramedChainProgram caseTwo)))
      (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (bankDispatchedBodyBits contracts clockDepth advantageExponent
          selectorBits
          (bankFramedChainBits contracts clockDepth advantageExponent
            chainBits)))
      (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
          (bankFramedChainProgram caseTwo))
        (bankDispatchedBodyFuel (bankFramedChainProgram caseOne)
          (bankFramedChainProgram caseTwo) selectorFuel
          (bankFramedChainFuel caseOne caseTwo chainFuel)))
      LanguageEvaluationRequest.code :=
  totalBooleanRuns_uniformTargetProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) _ _ _
    (totalBooleanRuns_bankDispatchedBodyProgram contracts clockDepth
      advantageExponent selector _ _ selectorBits selectorFuel _ _ hselector
      (totalBooleanRuns_bankFramedChainProgram contracts clockDepth
        advantageExponent caseOne chainBits chainFuel _
        (fun _request => Nat.le_max_left _ _) hcaseOne)
      (totalBooleanRuns_bankFramedChainProgram contracts clockDepth
        advantageExponent caseTwo chainBits chainFuel _
        (fun _request => Nat.le_max_right _ _) hcaseTwo))

/-- **The inverse schedule's `output`.**  The language function on the whole
request space, defined by the certified interpreter. -/
noncomputable def inverseDispatchedOutput
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  totalTargetOutput
    (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
        (bankFramedChainProgram caseTwo)))
    (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (bankDispatchedBodyBits contracts clockDepth advantageExponent
        selectorBits
        (bankFramedChainBits contracts clockDepth advantageExponent chainBits)))
    (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
        (bankFramedChainProgram caseTwo))
      (bankDispatchedBodyFuel (bankFramedChainProgram caseOne)
        (bankFramedChainProgram caseTwo) selectorFuel
        (bankFramedChainFuel caseOne caseTwo chainFuel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
-- Same assembly, elaborated once in the statement and once in the proof.
/-- **`hrun` at the published inverse assembly**, in the exact shape
`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` binds. -/
theorem inverse_hrun_of_totalPremises
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hselector :
      InverseSelectorTotalRuns contracts clockDepth advantageExponent selector
        selectorBits selectorFuel)
    (hcaseOne :
      TotalBooleanRuns caseOne chainBits chainFuel
        LanguageEvaluationRequest.code)
    (hcaseTwo :
      TotalBooleanRuns caseTwo chainBits chainFuel
        LanguageEvaluationRequest.code) :
    ∀ request : LanguageEvaluationRequest,
      runNPOracleProgram
          (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
              (bankFramedChainProgram caseTwo)))
          (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (bankDispatchedBodyBits contracts clockDepth advantageExponent
              selectorBits
              (bankFramedChainBits contracts clockDepth advantageExponent
                chainBits))
            request)
          (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
              (bankFramedChainProgram caseTwo))
            (bankDispatchedBodyFuel (bankFramedChainProgram caseOne)
              (bankFramedChainProgram caseTwo) selectorFuel
              (bankFramedChainFuel caseOne caseTwo chainFuel))
            request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some
          (inverseDispatchedOutput contracts clockDepth advantageExponent
            selector caseOne caseTwo selectorBits selectorFuel chainBits
            chainFuel request) :=
  run_eq_totalTargetOutput _ _ _
    (run_uniformTargetProgram_total contracts clockDepth advantageExponent
      selector caseOne caseTwo selectorBits selectorFuel chainBits chainFuel
      hselector hcaseOne hcaseTwo)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
-- Same assembly again.
/-- **`hboolean` at the published inverse assembly.** -/
theorem inverse_hboolean_of_totalPremises
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hselector :
      InverseSelectorTotalRuns contracts clockDepth advantageExponent selector
        selectorBits selectorFuel)
    (hcaseOne :
      TotalBooleanRuns caseOne chainBits chainFuel
        LanguageEvaluationRequest.code)
    (hcaseTwo :
      TotalBooleanRuns caseTwo chainBits chainFuel
        LanguageEvaluationRequest.code) :
    ∀ request : LanguageEvaluationRequest,
      inverseDispatchedOutput contracts clockDepth advantageExponent selector
          caseOne caseTwo selectorBits selectorFuel chainBits chainFuel
          request ≤
        1 :=
  totalTargetOutput_le_one _ _ _
    (run_uniformTargetProgram_total contracts clockDepth advantageExponent
      selector caseOne caseTwo selectorBits selectorFuel chainBits chainFuel
      hselector hcaseOne hcaseTwo)

/-! ## §6 The fixed schedule

`HeadlineRootSkeleton` §5 leaves the fixed-rate body as one free binder, so on
that schedule the bank link of §2 is already the whole reduction: `hrun` and
`hboolean` follow from one total premise about that body at the bank's frame. -/

/-- The published fixed schedule's bank frame. -/
noncomputable def fixedBankFrame (contracts : PublishedContracts)
    (clockDepth : ℕ) (requestedRate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedFrame (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts) (fixedBankRate contracts requestedRate)
    request

/-- **The fixed schedule's totality**, from the body's own total premise. -/
theorem fixed_run_uniformTargetProgram_total (contracts : PublishedContracts)
    (clockDepth : ℕ) (requestedRate : ℕ) (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedBankFrame contracts clockDepth requestedRate)) :
    TotalBooleanRuns
      (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate) body)
      (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate) bodyBits)
      (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate) body bodyFuel)
      LanguageEvaluationRequest.code :=
  totalBooleanRuns_uniformTargetProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts) (fixedBankRate contracts requestedRate)
    body bodyBits bodyFuel hbody

/-- **The fixed schedule's `output`.** -/
noncomputable def fixedTargetOutput (contracts : PublishedContracts)
    (clockDepth : ℕ) (requestedRate : ℕ) (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  totalTargetOutput
    (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate) body)
    (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate) bodyBits)
    (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate) body bodyFuel)

/-- **`hrun` at the published fixed assembly.** -/
theorem fixed_hrun_of_totalPremises (contracts : PublishedContracts)
    (clockDepth : ℕ) (requestedRate : ℕ) (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedBankFrame contracts clockDepth requestedRate)) :
    ∀ request : LanguageEvaluationRequest,
      runNPOracleProgram
          (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body)
          (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) bodyBits request)
          (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body bodyFuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some
          (fixedTargetOutput contracts clockDepth requestedRate body bodyBits
            bodyFuel request) :=
  run_eq_totalTargetOutput _ _ _
    (fixed_run_uniformTargetProgram_total contracts clockDepth requestedRate
      body bodyBits bodyFuel hbody)

/-- **`hboolean` at the published fixed assembly.** -/
theorem fixed_hboolean_of_totalPremises (contracts : PublishedContracts)
    (clockDepth : ℕ) (requestedRate : ℕ) (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedBankFrame contracts clockDepth requestedRate)) :
    ∀ request : LanguageEvaluationRequest,
      fixedTargetOutput contracts clockDepth requestedRate body bodyBits
          bodyFuel request ≤
        1 :=
  totalTargetOutput_le_one _ _ _
    (fixed_run_uniformTargetProgram_total contracts clockDepth requestedRate
      body bodyBits bodyFuel hbody)

/-! ## §7 The consumer check

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` at the published
assembly, with `output`, `hrun` and `hboolean` supplied from §5.  What the
packaging bridge still asks for is `hbits`, `hfuel`, `hinitial` and `bodyRun`
— the two totalisation obligations are gone from its binder list. -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
-- The assembly is elaborated once against the bridge's whole premise list.
example (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (hselector :
      InverseSelectorTotalRuns contracts clockDepth advantageExponent selector
        selectorBits selectorFuel)
    (hcaseOne :
      TotalBooleanRuns caseOne chainBits chainFuel
        LanguageEvaluationRequest.code)
    (hcaseTwo :
      TotalBooleanRuns caseTwo chainBits chainFuel
        LanguageEvaluationRequest.code) :=
  fun hbits hfuel hinitial bodyRun =>
    inverse_hexecutes_of_bodyRun contracts clockDepth machine advantageExponent
      (bankDispatchedBodyProgram selector (bankFramedChainProgram caseOne)
        (bankFramedChainProgram caseTwo))
      (bankDispatchedBodyBits contracts clockDepth advantageExponent
        selectorBits
        (bankFramedChainBits contracts clockDepth advantageExponent chainBits))
      (bankDispatchedBodyFuel (bankFramedChainProgram caseOne)
        (bankFramedChainProgram caseTwo) selectorFuel
        (bankFramedChainFuel caseOne caseTwo chainFuel))
      exponent hexponent
      (inverseDispatchedOutput contracts clockDepth advantageExponent selector
        caseOne caseTwo selectorBits selectorFuel chainBits chainFuel)
      hbits hfuel hinitial
      (inverse_hrun_of_totalPremises contracts clockDepth advantageExponent
        selector caseOne caseTwo selectorBits selectorFuel chainBits chainFuel
        hselector hcaseOne hcaseTwo)
      (inverse_hboolean_of_totalPremises contracts clockDepth advantageExponent
        selector caseOne caseTwo selectorBits selectorFuel chainBits chainFuel
        hselector hcaseOne hcaseTwo)
      bodyRun

end NearCubicWires.UniformTargetTotalRun
