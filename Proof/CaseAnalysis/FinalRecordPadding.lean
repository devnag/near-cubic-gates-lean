import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalStageSeamBridge
import Proof.CaseAnalysis.FinalCallCountCap
import Proof.CaseAnalysis.FinalEnvelopeCounter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (worker)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth flag
  result inputTape)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1  The words stage's budget is monotone in the call count -/

/-- The address counter's own budget (`Proof/PCP/ProjectionNormalizationCounter.lean`)
is linear. -/
theorem counterBudget_mono {c c' : ℕ} (h : c ≤ c') :
    ProjectionNormalization.Counter.budget c ≤ ProjectionNormalization.Counter.budget c' := by
  unfold ProjectionNormalization.Counter.budget
  omega

theorem wordsFuel_mono (entryWidth : ℕ) {c c' : ℕ} (h : c ≤ c') :
    CloseoutFinalC10WordsStage.wordsFuel entryWidth c
      ≤ CloseoutFinalC10WordsStage.wordsFuel entryWidth c' := by
  have hj : joinScalarWidth entryWidth c ≤ joinScalarWidth entryWidth c' :=
    CloseoutFinalC10CallCountMajorant.joinScalarWidth_mono entryWidth h
  have hdim : CompetitorDimensions.budget (joinScalarWidth entryWidth c)
      ≤ CompetitorDimensions.budget (joinScalarWidth entryWidth c') :=
    CloseoutFinalC10CallCountMajorant.dimensions_budget_mono hj
  have hcap : CompetitorReusableDecision.capacity (joinScalarWidth entryWidth c)
      ≤ CompetitorReusableDecision.capacity (joinScalarWidth entryWidth c') :=
    CloseoutFinalC10CallCountMajorant.capacity_mono hj
  have hwid : CompetitorRationalDecision.width (joinScalarWidth entryWidth c)
      ≤ CompetitorRationalDecision.width (joinScalarWidth entryWidth c') := by
    unfold CompetitorRationalDecision.width
    omega
  have hcnt := counterBudget_mono h
  have hmulA : (CompetitorRationalDecision.width entryWidth + 1) * (2 * c + 3)
      ≤ (CompetitorRationalDecision.width entryWidth + 1) * (2 * c' + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  have hmulB : (CompetitorRationalDecision.width entryWidth + 1) * c
      ≤ (CompetitorRationalDecision.width entryWidth + 1) * c' :=
    Nat.mul_le_mul_left _ h
  unfold CloseoutFinalC10WordsStage.wordsFuel
  omega

/-- **The stage's budget is monotone in the `Parts.callCount` field.**  This is
the whole content of the separation: `callCount` reaches `stageFuel`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`) only inside `wordsFuel`. -/
theorem stageFuel_mono (callFuel : Phase → ℕ → ℕ) (entryWidth callCount callCount' : ℕ → ℕ)
    (ph : Phase) (n : ℕ) (h : callCount n ≤ callCount' n) :
    C10SupplierStage.stageFuel callFuel entryWidth callCount ph n
      ≤ C10SupplierStage.stageFuel callFuel entryWidth callCount' ph n := by
  have hw := wordsFuel_mono (entryWidth n) h
  unfold C10SupplierStage.stageFuel
  omega

theorem stagedFuel_mono_stageFuel (stageFuel stageFuel' emitFuel : ℕ → ℕ)
    (entryWidth callCount n : ℕ) (h : stageFuel n ≤ stageFuel' n) :
    CloseoutFinalC10StageSeam.stagedFuel stageFuel emitFuel entryWidth callCount n
      ≤ CloseoutFinalC10StageSeam.stagedFuel stageFuel' emitFuel entryWidth callCount n := by
  unfold CloseoutFinalC10StageSeam.stagedFuel
  omega

/-- **`BlockRuns` is monotone in its fuel.**  `BlockRuns`
(`Proof/CaseAnalysis/FinalTailCompose.lean`) mentions `F` in exactly one of its
four conjuncts -- the `Step` -- so T3's block obligation lifts the same way the
stage's does.  This is the glue `blockRuns_of_supplierStage`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`) needs to be read at the
branch's own record count and a length-only `Parts.callCount`. -/
theorem blockRuns_enlarge (e : ℕ) {bs : ℕ} (body : LocalBitMultitape.Machine (218 + e) bs)
    {F F' : ℕ} {input witness rec : List Bool}
    (h : C10TailCompose.BlockRuns e body F input witness rec) (hF : F ≤ F') :
    C10TailCompose.BlockRuns e body F' input witness rec := by
  obtain ⟨heads, exit, hstep, hport, hin, hwit⟩ := h
  exact ⟨heads, exit, hstep.enlarge hF, hport, hin, hwit⟩

/-! ## Section 2  The stage, run at a length-only fuel over the UNPADDED stream -/

/-- **The deliverable (U1).**  One run of the supplier stage at the fuel
`C10SupplierStage.stageFuel callFuel entryWidth callCount ph len` -- a function
of `len` alone through the `Parts` fields `callFuel`, `entryWidth`, `callCount`
-- landing on a bank whose data port `81` carries the branch's OWN record
stream and whose counter port `90` carries the branch's OWN record count.  The
only link between the two is `hcap`, an inequality.

Nothing is padded and nothing is weakened: `hcalls` is `CallsReady` at the EXACT
count `(phaseRecords ...).length`, which is what `call_run`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) writes on tape `90` without any
hypothesis at all. -/
theorem stage_step_at_cap {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (extra : ℕ) {cs : Phase → ℕ}
    (calls : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (cs ph))
    (callFuel : Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (ph : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (hcap : (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length
      ≤ callCount len)
    (hcalls : C10SupplierStage.CallsReady extra (calls ph) (callFuel ph len) (entryWidth len)
      (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom))
      (List.ofFn x) bits)
    {sp : ℕ} (pmach : LocalBitMultitape.Machine (218 + (60 + extra)) sp)
    (ht : 2 ≤ 218 + (60 + extra)) :
    ∃ (bank : Fin 218 → List Bool) (scratch : Fin (60 + extra) → List Bool),
      Step (C10SupplierStage.stage extra calls ph)
        (C10SupplierStage.stageFuel callFuel entryWidth callCount ph len) (fun _ => 0)
        (C10LengthGate.exitTapes (Fin.castAdd (60 + extra) flag)
          ((UAcceptanceCarrier.verifier pmach ht (Fin.castAdd (60 + extra) result)).inputTapes
            (List.ofFn x) bits) 0 true)
        (fun _ => 0) (Fin.addCases bank scratch) ∧
      bank 81 = CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom) ∧
      bank 90 = CompareMachine.word
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length ∧
      DockReady (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom) bank ∧
      EmitEntry (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) bank := by
  obtain ⟨bank, scratch, hstep, h81, h90, hready, hentry, _h0, _h1, _h216, _hw56, _hw57⟩ :=
    C10SupplierStage.stage_run extra calls callFuel entryWidth
      (fun _ => (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length)
      answer denominator ph pcpp coordinate systematicAtom len x bits rfl hcalls pmach ht
  exact ⟨bank, scratch,
    hstep.enlarge (stageFuel_mono callFuel entryWidth _ callCount ph len hcap),
    h81, h90, hready, hentry⟩

/-! ## Section 3  The seam, with the equality replaced by the paper's bound -/

/-- **`stageReady_of_stageRun` (`Proof/CaseAnalysis/FinalStageSeamBridge.lean`)
with `hlen` weakened from `=` to `<=`.**  Binder for binder the same statement,
except that the record count reaches `CallsReady` EXACTLY (so the counter tape is
not touched) and reaches `Parts.callCount` only through `hcap`.  Everything
`StageReady` asserts about the records -- `hready`, `hentry`, `hwidth` -- is at
the branch's own `records`, unchanged. -/
theorem stageReady_of_stageRun_cap (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (P : C10StageSeamBridge.Parts sources k p)
    (he : 58 ≤ (C10StageSeamBridge.stageData_of_parts sources k p P).e)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (hcap : (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p P)
        x bits ph).length ≤ P.callCount n)
    (hcalls : C10SupplierStage.CallsReady P.extra (P.calls ph) (P.callFuel ph n)
      (P.entryWidth n)
      (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p P)
        x bits ph).length
      (CloseoutRowsEstimatorCoefficients.Stream.words (P.entryWidth n)
        (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p P) x bits ph))
      (List.ofFn x) bits) :
    ∃ (bank : Fin 218 → List Bool)
      (scratch : Fin (C10StageSeamBridge.stageData_of_parts sources k p P).e → List Bool),
      StageReady sources k p (C10StageSeamBridge.stageData_of_parts sources k p P)
        he x bits ph bank scratch := by
  obtain ⟨bank, scratch, hstep, _h81, _h90, hready, hentry, h0, h1, _h216, hw56, hw57⟩ :=
    C10SupplierStage.stage_run (Atom := Atoms sources k p x bits) P.extra P.calls P.callFuel
      P.entryWidth
      (fun _ => (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p P)
        x bits ph).length)
      (P.answer n x bits) (P.denominator n) ph
      (pcppOf sources k p x bits) (P.coordinate n x bits) C10TotalDecode.Atom.systematic
      n x bits rfl hcalls
      (worker (Soundness.cutoff (constantsOf sources))
        (Fin.castAdd (60 + P.extra) inputTape) (Fin.castAdd (60 + P.extra) flag)
        (Fin.castAdd (60 + P.extra) result)
        (C10TailComposeUniform.body sources k p
          (C10StageSeamBridge.stageData_of_parts sources k p P) ph))
      (by omega)
  refine ⟨bank, scratch,
    hstep.enlarge (stageFuel_mono P.callFuel P.entryWidth _ P.callCount ph n hcap),
    hready, hentry, h0, h1, rfl, ?_⟩
  have hwidth := C10StageSeamBridge.width_of_scratch he
    (joinScalarWidth (P.entryWidth n)
      (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p P)
        x bits ph).length)
    bank scratch hw56 hw57
  intro j
  rw [hwidth j]
  unfold widthOf
  rw [foldWidth_eq_joinScalarWidth]
  rfl

/-! ## Section 4  The producer side: the loop writes its own count, with no hypothesis -/

theorem callsReady_of_call_true {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (extra : ℕ) {ps bs : ℕ}
    (pre : LocalBitMultitape.Machine (218 + (60 + extra) + 1) ps)
    (body : LocalBitMultitape.Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth preFuel cost : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hpre : Step pre preFuel (fun _ => 0)
      (C10SupplierCall.bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ pcpp.clauseBits))))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch address)
        (heads (address + 1))
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch (address + 1))) :
    C10SupplierStage.CallsReady (extra + 2) (C10SupplierCall.callMachine extra pre body)
      (C10SupplierCall.callFuel preFuel pcpp.clauseBits cost) entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness :=
  C10SupplierCall.callsReady_of_call extra pre body answer denominator phase pcpp coordinate
    systematicAtom entryWidth _ preFuel cost input witness heads scratch rfl hpre hsite

theorem callsReady_at_clauseWidth_true {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} (extra : ℕ) {ps bs : ℕ}
    (pre : LocalBitMultitape.Machine (218 + (60 + extra) + 1) ps)
    (body : LocalBitMultitape.Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hfit : pcpp.clauseBits ≤ CloseoutLanguage.clauseWidth clauseDegree q)
    (hpre : Step pre preFuel (fun _ => 0)
      (C10SupplierCall.bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch 0)
        (fun _ : Fin 1 =>
          CompareMachine.word (2 ^ CloseoutLanguage.clauseWidth clauseDegree q))))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch address)
        (heads (address + 1))
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch (address + 1)))
    (hidle : ∀ address, 2 ^ pcpp.clauseBits ≤ address →
        address < 2 ^ CloseoutLanguage.clauseWidth clauseDegree q →
      Step body cost (heads address)
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch address)
        (heads (address + 1))
        (C10SupplierCall.loopBank extra entryWidth answer denominator phase pcpp coordinate
          systematicAtom input witness scratch (address + 1))) :
    C10SupplierStage.CallsReady (extra + 2) (C10SupplierCall.callMachine extra pre body)
      (C10SupplierCall.callFuel preFuel (CloseoutLanguage.clauseWidth clauseDegree q) cost)
      entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness :=
  C10EnvelopeCounter.callsReady_at_clauseWidth extra pre body answer denominator phase pcpp
    coordinate systematicAtom entryWidth _ preFuel cost clauseDegree q input witness heads
    scratch rfl hfit hpre hsite hidle

/-! ## Section 5  The cap, and where it lands on the width schedule -/

/-- `siteCap` is quartic and `2 ^ clauseWidth` is `two_pow_clauseWidth_le`'s
own bound, so the product of the two sits at exponent `2 * degree + 4 * m + 5`
whenever the coordinate bound `L` sits at exponent `m`. -/
theorem envelope_le_widthPower (degree m q L : ℕ) (hq : 1 ≤ q) (hL : L + 1 ≤ (q + 1) ^ m) :
    2 ^ CloseoutLanguage.clauseWidth degree q * CloseoutFinalC10CallCountCap.siteCap L
      ≤ (q + 1) ^ (2 * degree + 4 * m + 5) := by
  have h1 : 2 ^ CloseoutLanguage.clauseWidth degree q ≤ (q + 1) ^ (2 * degree + 1) :=
    C10LedgerBounds.two_pow_clauseWidth_le degree q hq
  have h16 : (16 : ℕ) ≤ (q + 1) ^ 4 := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ (q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h4 : (L + 1) ^ 4 ≤ ((q + 1) ^ m) ^ 4 := Nat.pow_le_pow_left hL 4
  have hexp2 : (4 : ℕ) + m * 4 = 4 * m + 4 := by ring
  have h2 : CloseoutFinalC10CallCountCap.siteCap L ≤ (q + 1) ^ (4 * m + 4) := by
    unfold CloseoutFinalC10CallCountCap.siteCap
    calc 16 * (L + 1) ^ 4 ≤ (q + 1) ^ 4 * ((q + 1) ^ m) ^ 4 := Nat.mul_le_mul h16 h4
      _ = (q + 1) ^ 4 * (q + 1) ^ (m * 4) := by rw [← pow_mul]
      _ = (q + 1) ^ (4 + m * 4) := by rw [← pow_add]
      _ = (q + 1) ^ (4 * m + 4) := by rw [hexp2]
  have hexp : 2 * degree + 4 * m + 5 = 2 * degree + 1 + (4 * m + 4) := by ring
  rw [hexp, pow_add]
  exact Nat.mul_le_mul h1 h2

theorem records_length_le_envelope (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (P : C10StageSeamBridge.Parts sources k p)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) (Lval : ℕ)
    (hL : ∀ i, ((P.coordinate n x bits) i).monomials.length ≤ Lval)
    (hfit : (pcppOf sources k p x bits).clauseBits
      ≤ CloseoutLanguage.clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n)) :
    (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p P)
        x bits ph).length
      ≤ 2 ^ CloseoutLanguage.clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n)
        * CloseoutFinalC10CallCountCap.siteCap Lval := by
  have hbase := CloseoutFinalC10CallCountCap.phaseRecords_length_le
    (Atom := Atoms sources k p x bits) Lval _ (pcppOf sources k p x bits) (P.answer n x bits)
    (P.denominator n) ph (P.coordinate n x bits) C10TotalDecode.Atom.systematic hL
  refine hbase.trans (Nat.mul_le_mul_right _ ?_)
  exact Nat.pow_le_pow_right (by norm_num) hfit

/-- **`hlen` at `partsOfSchedule`, as a `<=` that lands.**  With the coordinate
bound at exponent `m` and the schedule exponent `r` at least
`2 * p.clauseDegree + 4 * m + 5`, the branch's own record count is under
`(partsOfSchedule ...).callCount n = (q(n)+1)^r`
(`callCountSchedule`, `Proof/CaseAnalysis/FinalPartsSchedule.lean`). -/
theorem records_length_le_callCount (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r m : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) (Lval : ℕ)
    (hq : 1 ≤ C10PartsSchedule.widthAt sources k n)
    (hL : ∀ i, ((P.coordinate n x bits) i).monomials.length ≤ Lval)
    (hLfit : Lval + 1 ≤ C10PartsSchedule.widthPower sources k m n)
    (hfit : (pcppOf sources k p x bits).clauseBits
      ≤ C10PartsSchedule.clauseBitsSchedule sources k p.clauseDegree n)
    (hr : 2 * p.clauseDegree + 4 * m + 5 ≤ r) :
    (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (C10PartsSchedule.partsOfSchedule sources k p r P)) x bits ph).length
      ≤ (C10PartsSchedule.partsOfSchedule sources k p r P).callCount n := by
  have hbase := records_length_le_envelope sources k p
    (C10PartsSchedule.partsOfSchedule sources k p r P) x bits ph Lval hL hfit
  refine hbase.trans ?_
  refine (envelope_le_widthPower p.clauseDegree m _ Lval hq hLfit).trans ?_
  exact Nat.pow_le_pow_right (by omega) hr

/-! ## Section 6  The payoff: `StageReady` at the schedule, with no record-count
hypothesis -/

theorem stageReady_at_schedule (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r m : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    (he : 58 ≤ (C10StageSeamBridge.stageData_of_parts sources k p
      (C10PartsSchedule.partsOfSchedule sources k p r P)).e)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) (Lval : ℕ)
    (hq : 1 ≤ C10PartsSchedule.widthAt sources k n)
    (hL : ∀ i, ((P.coordinate n x bits) i).monomials.length ≤ Lval)
    (hLfit : Lval + 1 ≤ C10PartsSchedule.widthPower sources k m n)
    (hfit : (pcppOf sources k p x bits).clauseBits
      ≤ C10PartsSchedule.clauseBitsSchedule sources k p.clauseDegree n)
    (hr : 2 * p.clauseDegree + 4 * m + 5 ≤ r)
    (hcalls : C10SupplierStage.CallsReady
      (C10PartsSchedule.partsOfSchedule sources k p r P).extra
      ((C10PartsSchedule.partsOfSchedule sources k p r P).calls ph)
      ((C10PartsSchedule.partsOfSchedule sources k p r P).callFuel ph n)
      ((C10PartsSchedule.partsOfSchedule sources k p r P).entryWidth n)
      (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (C10PartsSchedule.partsOfSchedule sources k p r P)) x bits ph).length
      (CloseoutRowsEstimatorCoefficients.Stream.words
        ((C10PartsSchedule.partsOfSchedule sources k p r P).entryWidth n)
        (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
          (C10PartsSchedule.partsOfSchedule sources k p r P)) x bits ph))
      (List.ofFn x) bits) :
    ∃ (bank : Fin 218 → List Bool)
      (scratch : Fin (C10StageSeamBridge.stageData_of_parts sources k p
        (C10PartsSchedule.partsOfSchedule sources k p r P)).e → List Bool),
      StageReady sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (C10PartsSchedule.partsOfSchedule sources k p r P)) he x bits ph bank scratch :=
  stageReady_of_stageRun_cap sources k p (C10PartsSchedule.partsOfSchedule sources k p r P)
    he x bits ph
    (records_length_le_callCount sources k p r m P x bits ph Lval hq hL hLfit hfit hr)
    hcalls

end NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding
