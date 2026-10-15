import Proof.MachineModel.BankEmittedAtomLoop
import Proof.Circuits.FixedScheduleAtomLoop

/-!
# The numeral bank driven by a supplied scheduled length

`ScheduleDiagonalObstruction` and `ScheduleImageDiagonalObstruction` between
them refute every restatement of `hdiagonal`: the numeral bank decodes its
source index from the request's public length
(`RecoveryScheduleEnvelope.sourceIndexOfLength`), the two chains take theirs
from the envelope's first-crossing selector, and no restriction of the request
makes the two agree above an onset.  The repair therefore has to change the
*bank*, not the binder.

This module performs the structural half of that repair, and it turns out to be
a re-composition rather than a new arithmetic.

## The observation that makes it cheap

Read `RuntimeScheduleNumeralBank` §5–§6 as a pipeline:

```
bankLengthProgram  ⊕  dupLeft ⊕ width ⊕ dup ⊕ copies ⊕ callFrame ⊕ shape ⊕ queryCount
```

Only the *first* stage looks at the request.  Every later stage is arithmetic in
the length that stage produced: `bankWidth` is `widthValue … (bankSourceLength …)`,
`bankCopyCount` is `copyCountValue … (bankWidth …)`, and the shape runner is
called at `bankSourceLength …` in both its length and its code register.  The
public length register is never read again.

So the bank is `lengthStage ⊕ f`, with `f` closed in the emitted length.  §1
below re-composes exactly that `f` against a **parameter** length stage, whose
only obligation is

```
run lengthProgram … (initialNPOracleState inputLength code) =
  some (Nat.pair sourceLen code).
```

Nothing else in the bank changes: every stage lemma of
`RuntimeScheduleNumeralBank` is already stated at an arbitrary `sourceLen`.

## Why this deletes the diagonal

`RuntimeScheduleNumeralBank` §8 already proves the three identities the chains
want — `bankWidth_at_sourceLength`, `bankCopyCount_at_sourceLength`,
`bankSourceLength_sourceLength` — **unconditionally in the source index**.  They
were unusable only because the bank re-derived that index from the request, so a
consumer had to assume the request's length was the scheduled one.  Feed the
scheduled length *in* and §2's published run emits

```
scheduleNumeralBankOutput (sourceLength scheduleIndex)
  (scheduledWidth outer scheduleIndex)
  (outer.pcp.queryCount (sourceLength scheduleIndex))
  (inverseCopies outer pcppSource rate scheduleIndex) code
```

for an arbitrary `scheduleIndex`, with no hypothesis relating `scheduleIndex` to
`inputLength`.  That is verbatim the right-hand side of
`BankScheduleDiagonal.publishedBankFrame_of_eq_sourceLength`, so §3 instantiates
`scheduleIndex` at each chain's *own* index and the frame identification becomes
`rfl` — `hdiagonal` is gone, not restated.

## What is left

Exactly one obligation, and it is purely executable with no schedule semantics
in it: `InverseScheduledLengthRuns` / `FixedScheduledLengthRuns` of §4 — a
program that emits `Nat.pair (inverseScheduleLength …) code` from the request.
Its intended supplier is the selector-driven decode
(`UnaryPolynomialSelector.executableEnvelopeSchedule.selector`, an
`ExponentialNatProgram`, then `RecoveryScheduleEnvelope.inverseSourceIndex`'s
bounded `Nat.findGreatest` scan, then `CanonicalTwoPowProgram`), which is a
program-construction task rather than a hypothesis.  On the fixed schedule the
scan is not even needed: `fixedScheduleLength` is `sourceLength` of the selected
source itself.
-/

namespace NearCubicWires.SourceDrivenNumeralBank

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open private dupLeftProgram dupLeftBits run_dupLeftProgram
  queryCallFrameProgram queryCallFrameOutput queryCallFrameBits
  run_queryCallFrameProgram queryCountFrameProgram queryCountFrameInput
  queryCountFrameBits run_queryCountFrameProgram from
  Proof.MachineModel.RuntimeScheduleNumeralBank

/-! ## 1. The bank, re-composed against a supplied length stage -/

/-- The supplied length stage, then the duplication the width stage expects. -/
private def lengthDupProgram (lengthProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms lengthProgram dupLeftProgram

private def lengthDupFuel (lengthFuel : ℕ) : ℕ :=
  linkFuel dupLeftProgram lengthFuel 3

private def lengthDupBits (inputLength lengthBits sourceLen code : ℕ) : ℕ :=
  occurrenceStageBits inputLength lengthBits (dupLeftBits sourceLen code)

private theorem run_lengthDupProgram (lengthProgram : NPOracleProgram)
    (inputLength lengthBits lengthFuel sourceLen code : ℕ)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code)) :
    runNPOracleProgram (lengthDupProgram lengthProgram)
        (lengthDupBits inputLength lengthBits sourceLen code)
        (lengthDupFuel lengthFuel)
        (initialNPOracleState inputLength code) =
      some (Nat.pair sourceLen (Nat.pair sourceLen code)) :=
  run_occurrenceStage hlength (run_dupLeftProgram inputLength sourceLen code)

private def widthProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms (lengthDupProgram lengthProgram)
    (preserveRightProgram (widthEnvelopeProgram clockDepth coefficient exponent))

private def widthFuel (clockDepth coefficient exponent lengthFuel
    sourceLen : ℕ) : ℕ :=
  linkFuel
    (preserveRightProgram (widthEnvelopeProgram clockDepth coefficient exponent))
    (lengthDupFuel lengthFuel)
    (preserveRightFuel
      (widthEnvelopeFuel clockDepth coefficient exponent sourceLen))

private def widthBits (clockDepth coefficient exponent inputLength lengthBits
    sourceLen code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (lengthDupBits inputLength lengthBits sourceLen code)
    (preserveRightBits
      (widthEnvelopeBits inputLength clockDepth coefficient exponent sourceLen)
      sourceLen (Nat.pair sourceLen code)
      (widthValue clockDepth coefficient exponent sourceLen))

private theorem run_widthProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent inputLength lengthBits lengthFuel sourceLen
      code : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code)) :
    runNPOracleProgram (widthProgram lengthProgram clockDepth coefficient
        exponent)
        (widthBits clockDepth coefficient exponent inputLength lengthBits
          sourceLen code)
        (widthFuel clockDepth coefficient exponent lengthFuel sourceLen)
        (initialNPOracleState inputLength code) =
      some
        (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
          (Nat.pair sourceLen code)) :=
  run_occurrenceStage
    (run_lengthDupProgram lengthProgram inputLength lengthBits lengthFuel
      sourceLen code hlength)
    (run_preserveRightProgram
      (widthEnvelopeProgram clockDepth coefficient exponent) inputLength
      (widthEnvelopeBits inputLength clockDepth coefficient exponent sourceLen)
      (widthEnvelopeFuel clockDepth coefficient exponent sourceLen) sourceLen
      (Nat.pair sourceLen code)
      (widthValue clockDepth coefficient exponent sourceLen)
      (run_widthEnvelopeProgram inputLength clockDepth coefficient exponent
        sourceLen hbudget))

private def widthDupProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms (widthProgram lengthProgram clockDepth coefficient exponent)
    dupLeftProgram

private def widthDupFuel (clockDepth coefficient exponent lengthFuel
    sourceLen : ℕ) : ℕ :=
  linkFuel dupLeftProgram
    (widthFuel clockDepth coefficient exponent lengthFuel sourceLen) 3

private def widthDupBits (clockDepth coefficient exponent inputLength lengthBits
    sourceLen code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (widthBits clockDepth coefficient exponent inputLength lengthBits sourceLen
      code)
    (dupLeftBits (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.pair sourceLen code))

private theorem run_widthDupProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent inputLength lengthBits lengthFuel sourceLen
      code : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code)) :
    runNPOracleProgram
        (widthDupProgram lengthProgram clockDepth coefficient exponent)
        (widthDupBits clockDepth coefficient exponent inputLength lengthBits
          sourceLen code)
        (widthDupFuel clockDepth coefficient exponent lengthFuel sourceLen)
        (initialNPOracleState inputLength code) =
      some
        (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
          (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
            (Nat.pair sourceLen code))) :=
  run_occurrenceStage
    (run_widthProgram lengthProgram clockDepth coefficient exponent inputLength
      lengthBits lengthFuel sourceLen code hbudget hlength)
    (run_dupLeftProgram inputLength
      (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.pair sourceLen code))

/-- The supplied length stage, the scheduled width, and the scheduled copy
count. -/
private def frontProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms (widthDupProgram lengthProgram clockDepth coefficient exponent)
    (preserveRightProgram (copyCountProgram factor summand))

private def frontFuel (clockDepth coefficient exponent factor summand lengthFuel
    sourceLen : ℕ) : ℕ :=
  linkFuel (preserveRightProgram (copyCountProgram factor summand))
    (widthDupFuel clockDepth coefficient exponent lengthFuel sourceLen)
    (preserveRightFuel
      (copyCountFuel factor summand
        (widthValue clockDepth coefficient exponent sourceLen)))

private def frontBits (clockDepth coefficient exponent factor summand
    inputLength lengthBits sourceLen code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (widthDupBits clockDepth coefficient exponent inputLength lengthBits
      sourceLen code)
    (preserveRightBits
      (copyCountBits inputLength factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
        (Nat.pair sourceLen code))
      (copyCountValue factor summand
        (widthValue clockDepth coefficient exponent sourceLen)))

private theorem run_frontProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength lengthBits
      lengthFuel sourceLen code : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code)) :
    runNPOracleProgram
        (frontProgram lengthProgram clockDepth coefficient exponent factor
          summand)
        (frontBits clockDepth coefficient exponent factor summand inputLength
          lengthBits sourceLen code)
        (frontFuel clockDepth coefficient exponent factor summand lengthFuel
          sourceLen)
        (initialNPOracleState inputLength code) =
      some
        (bankFrontOutput
          (copyCountValue factor summand
            (widthValue clockDepth coefficient exponent sourceLen))
          (widthValue clockDepth coefficient exponent sourceLen) sourceLen
          code) :=
  run_occurrenceStage
    (run_widthDupProgram lengthProgram clockDepth coefficient exponent
      inputLength lengthBits lengthFuel sourceLen code hbudget hlength)
    (run_preserveRightProgram (copyCountProgram factor summand) inputLength
      (copyCountBits inputLength factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      (copyCountFuel factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
        (Nat.pair sourceLen code))
      (copyCountValue factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      (run_copyCountProgram inputLength factor summand
        (widthValue clockDepth coefficient exponent sourceLen)))

private def callFrameProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms
    (frontProgram lengthProgram clockDepth coefficient exponent factor summand)
    queryCallFrameProgram

private def callFrameFuel (clockDepth coefficient exponent factor summand
    lengthFuel sourceLen : ℕ) : ℕ :=
  linkFuel queryCallFrameProgram
    (frontFuel clockDepth coefficient exponent factor summand lengthFuel
      sourceLen)
    11

private def callFrameBits (clockDepth coefficient exponent factor summand
    inputLength lengthBits sourceLen code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (frontBits clockDepth coefficient exponent factor summand inputLength
      lengthBits sourceLen code)
    (queryCallFrameBits
      (copyCountValue factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      (widthValue clockDepth coefficient exponent sourceLen) sourceLen code)

private theorem run_callFrameProgram (lengthProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength lengthBits
      lengthFuel sourceLen code : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code)) :
    runNPOracleProgram
        (callFrameProgram lengthProgram clockDepth coefficient exponent factor
          summand)
        (callFrameBits clockDepth coefficient exponent factor summand
          inputLength lengthBits sourceLen code)
        (callFrameFuel clockDepth coefficient exponent factor summand lengthFuel
          sourceLen)
        (initialNPOracleState inputLength code) =
      some
        (queryCallFrameOutput
          (copyCountValue factor summand
            (widthValue clockDepth coefficient exponent sourceLen))
          (widthValue clockDepth coefficient exponent sourceLen) sourceLen
          code) :=
  run_occurrenceStage
    (run_frontProgram lengthProgram clockDepth coefficient exponent factor
      summand inputLength lengthBits lengthFuel sourceLen code hbudget hlength)
    (run_queryCallFrameProgram inputLength
      (copyCountValue factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      (widthValue clockDepth coefficient exponent sourceLen) sourceLen code)

private def callProgram (lengthProgram shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms
    (callFrameProgram lengthProgram clockDepth coefficient exponent factor
      summand)
    (nativeContextCallProgram shapeProgram)

private def callFuel (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand lengthFuel sourceLen
      shapeFuel : ℕ) : ℕ :=
  linkFuel (nativeContextCallProgram shapeProgram)
    (callFrameFuel clockDepth coefficient exponent factor summand lengthFuel
      sourceLen)
    (nativeContextCallFuel shapeProgram shapeFuel sourceLen sourceLen)

private def callBits (clockDepth coefficient exponent factor summand
    inputLength lengthBits sourceLen code shapeBits shapeOutput : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (callFrameBits clockDepth coefficient exponent factor summand inputLength
      lengthBits sourceLen code)
    (nativeContextCallBits inputLength sourceLen sourceLen
      (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
        (Nat.pair
          (copyCountValue factor summand
            (widthValue clockDepth coefficient exponent sourceLen))
          code))
      shapeOutput shapeBits)

private theorem run_callProgram (lengthProgram shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength lengthBits
      lengthFuel sourceLen code shapeBits shapeFuel shapeOutput : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code))
    (hshape :
      runNPOracleProgram shapeProgram shapeBits shapeFuel
          (initialNPOracleState sourceLen sourceLen) =
        some shapeOutput) :
    runNPOracleProgram
        (callProgram lengthProgram shapeProgram clockDepth coefficient exponent
          factor summand)
        (callBits clockDepth coefficient exponent factor summand inputLength
          lengthBits sourceLen code shapeBits shapeOutput)
        (callFuel shapeProgram clockDepth coefficient exponent factor summand
          lengthFuel sourceLen shapeFuel)
        (initialNPOracleState inputLength code) =
      some
        (queryCountFrameInput shapeOutput sourceLen
          (widthValue clockDepth coefficient exponent sourceLen)
          (copyCountValue factor summand
            (widthValue clockDepth coefficient exponent sourceLen))
          code) :=
  run_occurrenceStage
    (run_callFrameProgram lengthProgram clockDepth coefficient exponent factor
      summand inputLength lengthBits lengthFuel sourceLen code hbudget hlength)
    (run_nativeContextCallProgram shapeProgram inputLength sourceLen sourceLen
      (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
        (Nat.pair
          (copyCountValue factor summand
            (widthValue clockDepth coefficient exponent sourceLen))
          code))
      shapeOutput shapeBits shapeFuel hshape)

/-- **The source-driven numeral bank.**  `RuntimeScheduleNumeralBank`'s stream
with its length decode replaced by a supplied stage.  Nothing else changes:
every later stage was already closed in the emitted length. -/
def sourceDrivenBankProgram (lengthProgram shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand : ℕ) : NPOracleProgram :=
  linkPrograms
    (callProgram lengthProgram shapeProgram clockDepth coefficient exponent
      factor summand)
    queryCountFrameProgram

def sourceDrivenBankFuel (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand lengthFuel sourceLen
      shapeFuel : ℕ) : ℕ :=
  linkFuel queryCountFrameProgram
    (callFuel shapeProgram clockDepth coefficient exponent factor summand
      lengthFuel sourceLen shapeFuel)
    11

def sourceDrivenBankBits (clockDepth coefficient exponent factor summand
    inputLength lengthBits sourceLen code shapeBits shapeOutput : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (callBits clockDepth coefficient exponent factor summand inputLength
      lengthBits sourceLen code shapeBits shapeOutput)
    (queryCountFrameBits shapeOutput sourceLen
      (widthValue clockDepth coefficient exponent sourceLen)
      (copyCountValue factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      code)

/-- **The source-driven bank, executed.**  The public length is consumed only
by the supplied stage; every numeral below is the published arithmetic at the
length that stage emitted. -/
theorem run_sourceDrivenBankProgram (lengthProgram shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent factor summand inputLength lengthBits
      lengthFuel sourceLen code shapeBits shapeFuel shapeOutput : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair sourceLen code))
    (hshape :
      runNPOracleProgram shapeProgram shapeBits shapeFuel
          (initialNPOracleState sourceLen sourceLen) =
        some shapeOutput) :
    runNPOracleProgram
        (sourceDrivenBankProgram lengthProgram shapeProgram clockDepth
          coefficient exponent factor summand)
        (sourceDrivenBankBits clockDepth coefficient exponent factor summand
          inputLength lengthBits sourceLen code shapeBits shapeOutput)
        (sourceDrivenBankFuel shapeProgram clockDepth coefficient exponent
          factor summand lengthFuel sourceLen shapeFuel)
        (initialNPOracleState inputLength code) =
      some
        (scheduleNumeralBankOutput sourceLen
          (widthValue clockDepth coefficient exponent sourceLen)
          (Nat.unpair shapeOutput).2
          (copyCountValue factor summand
            (widthValue clockDepth coefficient exponent sourceLen))
          code) :=
  run_occurrenceStage
    (run_callProgram lengthProgram shapeProgram clockDepth coefficient exponent
      factor summand inputLength lengthBits lengthFuel sourceLen code shapeBits
      shapeFuel shapeOutput hbudget hlength hshape)
    (run_queryCountFrameProgram inputLength shapeOutput sourceLen
      (widthValue clockDepth coefficient exponent sourceLen)
      (copyCountValue factor summand
        (widthValue clockDepth coefficient exponent sourceLen))
      code)

/-! ## 2. The published bank at a supplied scheduled index -/

/-- The published source-driven bank: the published parameters, with the length
decode taken as a stage. -/
noncomputable def publishedSourceDrivenBankProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (lengthProgram : NPOracleProgram) : NPOracleProgram :=
  sourceDrivenBankProgram lengthProgram outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1)

noncomputable def publishedSourceDrivenBankFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate lengthFuel sourceLen : ℕ) :
    ℕ :=
  sourceDrivenBankFuel outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1) lengthFuel
    sourceLen (outer.pcp.shape.budget sourceLen)

noncomputable def publishedSourceDrivenBankBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (rate inputLength lengthBits sourceLen code : ℕ) : ℕ :=
  sourceDrivenBankBits clockDepth outer.pcp.shape.coefficient
    outer.proofExponent (recoveryBlock pcppSource * rate)
    (recoveryBlock pcppSource + 1) inputLength lengthBits sourceLen code
    (outer.pcp.shape.budget sourceLen) (outer.pcp.shape.execute sourceLen)

/-- **The published source-driven bank, executed at a supplied index.**  The
emitted frame is the chain's frame at `scheduleIndex`, and `scheduleIndex` is
*unconstrained*: nothing here relates it to `inputLength`.  This is the theorem
`hdiagonal` used to stand in for. -/
theorem run_publishedSourceDrivenBankProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (lengthProgram : NPOracleProgram)
    (inputLength lengthBits lengthFuel scheduleIndex code : ℕ)
    (hlength :
      runNPOracleProgram lengthProgram lengthBits lengthFuel
          (initialNPOracleState inputLength code) =
        some (Nat.pair (sourceLength scheduleIndex) code)) :
    runNPOracleProgram
        (publishedSourceDrivenBankProgram outer pcppSource rate lengthProgram)
        (publishedSourceDrivenBankBits outer pcppSource rate inputLength
          lengthBits (sourceLength scheduleIndex) code)
        (publishedSourceDrivenBankFuel outer pcppSource rate lengthFuel
          (sourceLength scheduleIndex))
        (initialNPOracleState inputLength code) =
      some
        (scheduleNumeralBankOutput (sourceLength scheduleIndex)
          (scheduledWidth outer scheduleIndex)
          (outer.pcp.queryCount (sourceLength scheduleIndex))
          (inverseCopies outer pcppSource rate scheduleIndex) code) := by
  have hwidth :
      scheduledWidth outer scheduleIndex =
        widthValue clockDepth outer.pcp.shape.coefficient outer.proofExponent
          (sourceLength scheduleIndex) := by
    rw [← bankWidth_at_sourceLength outer scheduleIndex, bankWidth,
      bankSourceLength_sourceLength]
  have hcopies :
      inverseCopies outer pcppSource rate scheduleIndex =
        copyCountValue (recoveryBlock pcppSource * rate)
          (recoveryBlock pcppSource + 1)
          (widthValue clockDepth outer.pcp.shape.coefficient
            outer.proofExponent (sourceLength scheduleIndex)) := by
    rw [← bankCopyCount_at_sourceLength outer pcppSource rate scheduleIndex,
      bankCopyCount, bankWidth, bankSourceLength_sourceLength]
  have hcount :
      outer.pcp.queryCount (sourceLength scheduleIndex) =
        (Nat.unpair (outer.pcp.shape.execute (sourceLength scheduleIndex))).2 :=
    (unpair_shapeExecute_eq_queryCount outer (sourceLength scheduleIndex)).symm
  rw [hwidth, hcopies, hcount]
  exact run_sourceDrivenBankProgram lengthProgram outer.pcp.shape.program
    clockDepth outer.pcp.shape.coefficient outer.proofExponent
    (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1) inputLength
    lengthBits lengthFuel (sourceLength scheduleIndex) code
    (outer.pcp.shape.budget (sourceLength scheduleIndex))
    (outer.pcp.shape.budget (sourceLength scheduleIndex))
    (outer.pcp.shape.execute (sourceLength scheduleIndex))
    (publishedWidthBudget_positive outer (sourceLength scheduleIndex))
    hlength (run_publishedShapeProgram outer (sourceLength scheduleIndex))

/-! ## 3. The frame the chains work at, definitionally -/

/-- **The selector-driven frame.**  Defined at the chain's own source index, so
the identification `BankScheduleDiagonal.publishedBankFrame_of_eq_sourceLength`
had to assume is now the definition. -/
noncomputable def selectorDrivenBankFrame
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate scheduleIndex code : ℕ) :
    ℕ :=
  scheduleNumeralBankOutput (sourceLength scheduleIndex)
    (scheduledWidth outer scheduleIndex)
    (outer.pcp.queryCount (sourceLength scheduleIndex))
    (inverseCopies outer pcppSource rate scheduleIndex) code

/-- The published bank frame at a request whose length *is* the scheduled one
is the selector-driven frame — and this is the only place the old diagonal
survived, now as a `rfl`-level fact about `sourceLength`. -/
theorem publishedBankFrame_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate scheduleIndex code : ℕ) :
    UniformTargetLanguageBank.publishedBankFrame outer pcppSource rate
        (sourceLength scheduleIndex) code =
      selectorDrivenBankFrame outer pcppSource rate scheduleIndex code := by
  rw [UniformTargetLanguageBank.publishedBankFrame, selectorDrivenBankFrame,
    bankSourceLength_sourceLength, sourceIndexOfLength_sourceLength]

/-! ## 4. The one remaining obligation, at both published schedules -/

/-- **The inverse schedule's residual.**  A program that emits the inverse
chain's scheduled source length from the request.  No schedule semantics
appear: this is a statement about one instruction stream, and it is satisfiable
— unlike every form of `hdiagonal`. -/
def InverseScheduledLengthRuns
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (lengthProgram : NPOracleProgram)
    (lengthBits lengthFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ) (input : BitInput target),
    runNPOracleProgram lengthProgram (lengthBits ⟨target, input⟩)
        (lengthFuel ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (Nat.pair
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (encodeBitInput input))

/-- Fixed-rate counterpart.  On this schedule the supplier needs no
`inverseSourceIndex` scan at all: `fixedScheduleLength` is `sourceLength` of the
selected source itself. -/
def FixedScheduledLengthRuns
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (lengthProgram : NPOracleProgram)
    (lengthBits lengthFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ) (input : BitInput target),
    runNPOracleProgram lengthProgram (lengthBits ⟨target, input⟩)
        (lengthFuel ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (Nat.pair
          (fixedScheduleLength contracts clockDepth requestedRate target)
          (encodeBitInput input))

/-- **The inverse schedule's bank, executed with no diagonal.**  From the
residual alone, the published source-driven bank emits the inverse chain's own
frame at every request — the statement `hdiagonal` was threaded to produce. -/
theorem run_inverseSelectorDrivenBankProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (lengthProgram : NPOracleProgram)
    (lengthBits lengthFuel : LanguageEvaluationRequest → ℕ)
    (hlength :
      InverseScheduledLengthRuns contracts clockDepth advantageExponent
        lengthProgram lengthBits lengthFuel)
    (target : ℕ) (input : BitInput target) :
    runNPOracleProgram
        (publishedSourceDrivenBankProgram
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts
            advantageExponent)
          lengthProgram)
        (publishedSourceDrivenBankBits
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts
            advantageExponent)
          target (lengthBits ⟨target, input⟩)
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (encodeBitInput input))
        (publishedSourceDrivenBankFuel
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts
            advantageExponent)
          (lengthFuel ⟨target, input⟩)
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (selectorDrivenBankFrame
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts
            advantageExponent)
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))
          (encodeBitInput input)) :=
  run_publishedSourceDrivenBankProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (UniformTargetLanguageBank.inverseBankRate contracts advantageExponent)
    lengthProgram target (lengthBits ⟨target, input⟩)
    (lengthFuel ⟨target, input⟩)
    (inverseSourceIndex
      (inverseSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target))
    (encodeBitInput input) (hlength target input)

/-- Fixed-rate counterpart of `run_inverseSelectorDrivenBankProgram`. -/
theorem run_fixedSelectorDrivenBankProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (lengthProgram : NPOracleProgram)
    (lengthBits lengthFuel : LanguageEvaluationRequest → ℕ)
    (hlength :
      FixedScheduledLengthRuns contracts clockDepth requestedRate lengthProgram
        lengthBits lengthFuel)
    (target : ℕ) (input : BitInput target) :
    runNPOracleProgram
        (publishedSourceDrivenBankProgram
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          lengthProgram)
        (publishedSourceDrivenBankBits
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          target (lengthBits ⟨target, input⟩)
          (fixedScheduleLength contracts clockDepth requestedRate target)
          (encodeBitInput input))
        (publishedSourceDrivenBankFuel
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          (lengthFuel ⟨target, input⟩)
          (fixedScheduleLength contracts clockDepth requestedRate target))
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (selectorDrivenBankFrame
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          (encodeBitInput input)) :=
  run_publishedSourceDrivenBankProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
    lengthProgram target (lengthBits ⟨target, input⟩)
    (lengthFuel ⟨target, input⟩)
    (fixedSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)
    (encodeBitInput input) (hlength target input)

end NearCubicWires.SourceDrivenNumeralBank
