import Proof.CaseAnalysis.FinalWordsStage
import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalStageSeamBlock
import Proof.CaseAnalysis.FinalTailCompose

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth flag
  result inputTape)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold (foldWidth)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other
  install_existing)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The words stage's tapes sit at the bottom of the stage bank -/

theorem words_tapes : 219 + CloseoutFinalC10WordsStage.s = 278 := rfl

theorem e_floor (extra : ℕ) : 219 + CloseoutFinalC10WordsStage.s ≤ 218 + (60 + extra) := by
  have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
  omega

/-- The prefix slot map: tape `k` of the words stage is tape `k` of the stage. -/
def wslot (extra : ℕ) (i : Fin (219 + CloseoutFinalC10WordsStage.s)) :
    Fin (218 + (60 + extra)) :=
  ⟨i.val, by
    have h := i.isLt
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    omega⟩

theorem wslot_val (extra : ℕ) (i : Fin (219 + CloseoutFinalC10WordsStage.s)) :
    (wslot extra i).val = i.val := rfl

theorem wslot_inj (extra : ℕ) : Function.Injective (wslot extra) := by
  intro a b hab
  exact Fin.ext (by simpa only [wslot_val] using congrArg Fin.val hab)

/-- A bank port of the dock, as a words-stage port. -/
theorem castAdd_eq_wslot (extra : ℕ) (k : Fin 218)
    (j : Fin (219 + CloseoutFinalC10WordsStage.s)) (h : k.val = j.val) :
    Fin.castAdd (60 + extra) k = wslot extra j := Fin.ext h

/-- An extension port of the stage, as a words-stage port. -/
theorem natAdd_eq_wslot (extra : ℕ) (k : Fin (60 + extra))
    (j : Fin (219 + CloseoutFinalC10WordsStage.s)) (h : 218 + k.val = j.val) :
    Fin.natAdd 218 k = wslot extra j := Fin.ext h

/-- Splitting a stage-bank tape function into the dock's bank and the extension. -/
theorem addCases_restrict {n : ℕ} (T : Fin (218 + n) → List Bool) :
    Fin.addCases (fun k : Fin 218 => T (Fin.castAdd n k))
      (fun k : Fin n => T (Fin.natAdd 218 k)) = T := by
  funext i
  refine Fin.addCases (m := 218) (n := n) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
  · rw [Fin.addCases_right]

/-- Docking a heads profile that is zero inside and zero outside is zero. -/
theorem dockH_zero {t u : ℕ} (slots : Fin t → Fin u) :
    dockH slots (fun _ => 0) (fun _ => 0) = (fun _ : Fin u => (0 : ℕ)) := by
  funext i
  cases h : RecoveryFocus.pick slots i with
  | none => simp [dockH, h]
  | some j => simp [dockH, h]

/-- The words stage's view of the stage bank. -/
def wordsBank (extra : ℕ) (mid : Fin (218 + (60 + extra)) → List Bool) :
    Fin (219 + CloseoutFinalC10WordsStage.s) → List Bool := fun j => mid (wslot extra j)

def CallsReady (extra : ℕ) {cs : ℕ} (calls : Machine (218 + (60 + extra)) cs) (fuel : ℕ)
    (entryWidth callCount : ℕ) (stream input witness : List Bool) : Prop :=
  ∃ mid : Fin (218 + (60 + extra)) → List Bool,
    Step calls fuel (fun _ => 0)
      (C10TailCompose.entryOf (C10TailCompose.wflag (60 + extra)) input witness)
      (fun _ => 0) mid ∧
    wordsBank extra mid 81 = stream ∧
    wordsBank extra mid 90 = CompareMachine.word callCount ∧
    wordsBank extra mid ⟨218, by decide⟩ = List.replicate entryWidth true ∧
    wordsBank extra mid 0 = frame input ∧
    wordsBank extra mid 1 = frame witness ∧
    wordsBank extra mid 216 = [true] ∧
    (∀ j : Fin (219 + CloseoutFinalC10WordsStage.s), 2 ≤ j.val → j.val ≠ 81 → j.val ≠ 90 →
      j.val ≠ 216 → j.val ≠ 218 → wordsBank extra mid j = [])

/-! ## §3 The stage, its fuel, and its state count -/

noncomputable def stage (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (ph : CloseoutRowsOriginalSchedule.Phase) :=
  Composition.machine (calls ph)
    (RecoveryFocus.machine (wslot extra) CloseoutFinalC10WordsStage.wordsMachine)

/-- The state count of a machine, so `StageData.st` can name `stage`'s. -/
def stateCount {t n : ℕ} (_ : Machine t n) : ℕ := n

/-- `StageData.st`. -/
noncomputable def stageStates (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (ph : CloseoutRowsOriginalSchedule.Phase) : ℕ :=
  stateCount (stage extra calls ph)

def stageFuel (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ)
    (entryWidth callCount : ℕ → ℕ) (ph : CloseoutRowsOriginalSchedule.Phase) (n : ℕ) : ℕ :=
  callFuel ph n + 1 + CloseoutFinalC10WordsStage.wordsFuel (entryWidth n) (callCount n)

/-- The driver half of the split: everything the stage spends that is not the
external-row loop. -/
def driverFuel (entryWidth callCount : ℕ → ℕ) (n : ℕ) : ℕ :=
  CloseoutFinalC10WordsStage.wordsFuel (entryWidth n) (callCount n) + 1

theorem stageFuel_split (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ)
    (entryWidth callCount : ℕ → ℕ) (driver rowCount rowFuel :
      CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (onset : ℕ)
    (hcall : ∀ ph N, onset ≤ N → callFuel ph N ≤ rowCount ph N * rowFuel ph N)
    (hdriver : ∀ ph N, onset ≤ N → driverFuel entryWidth callCount N ≤ driver ph N) :
    ∀ ph N, onset ≤ N →
      stageFuel callFuel entryWidth callCount ph N ≤ driver ph N + rowCount ph N * rowFuel ph N := by
  intro ph N hN
  have h1 := hcall ph N hN
  have h2 := hdriver ph N hN
  unfold stageFuel
  unfold driverFuel at h2
  omega

/-! ## §4 The run -/

theorem stage_run {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (hlen : (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length
      = callCount len)
    (hcalls : CallsReady extra (calls ph) (callFuel ph len) (entryWidth len) (callCount len)
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom))
      (List.ofFn x) bits)
    {sp : ℕ} (p : Machine (218 + (60 + extra)) sp) (ht : 2 ≤ 218 + (60 + extra)) :
    ∃ (bank : Fin 218 → List Bool) (scratch : Fin (60 + extra) → List Bool),
      Step (stage extra calls ph) (stageFuel callFuel entryWidth callCount ph len) (fun _ => 0)
        (C10LengthGate.exitTapes (Fin.castAdd (60 + extra) flag)
          ((UAcceptanceCarrier.verifier p ht (Fin.castAdd (60 + extra) result)).inputTapes
            (List.ofFn x) bits) 0 true)
        (fun _ => 0) (Fin.addCases bank scratch) ∧
      bank 81 = CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom) ∧
      bank 90 = CompareMachine.word
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length ∧
      DockReady (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom) bank ∧
      EmitEntry (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) bank ∧
      bank 0 = frame (List.ofFn x) ∧ bank 1 = frame bits ∧ bank 216 = [true] ∧
      scratch ⟨56, by omega⟩ = List.replicate (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) true ∧
      scratch ⟨57, by omega⟩ = List.replicate (CompetitorRationalDecision.width
        (joinScalarWidth (entryWidth len)
          (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length)) true := by
  classical
  obtain ⟨mid, hstep, m81, m90, m218, m0, m1, m216, mblank⟩ := hcalls
  obtain ⟨Hw, Aw, hws, hwh, w83, w84, w85, w86, w90, w98, w176, w182, w186, w187,
    w213, w214, w274, w275, wfr⟩ :=
    CloseoutFinalC10WordsStage.words_step (entryWidth len) (callCount len)
      (fun _ => 0) (wordsBank extra mid) (fun _ => rfl) m218 m90
      (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        refine mblank i ?_ ?_ ?_ ?_ ?_ <;> omega)
      (by
        intro i hi
        refine mblank i ?_ ?_ ?_ ?_ ?_ <;> omega)
  have hHw : Hw = fun _ => 0 := funext hwh
  subst hHw
  have hfocus := hws.focus (wslot extra) (wslot_inj extra) (fun _ => 0) mid
  rw [dockH_zero, install_existing (wslot extra) mid (wordsBank extra mid) (fun _ => rfl)] at hfocus
  have hentry := C10TailCompose.entry_eq p ht (Fin.castAdd (60 + extra) result)
    (C10TailCompose.wflag (60 + extra)) (by simp) (by simp) (List.ofFn x) bits
  have hrun : Step (stage extra calls ph) (stageFuel callFuel entryWidth callCount ph len)
      (fun _ => 0)
      (C10LengthGate.exitTapes (Fin.castAdd (60 + extra) flag)
        ((UAcceptanceCarrier.verifier p ht (Fin.castAdd (60 + extra) result)).inputTapes
          (List.ofFn x) bits) 0 true)
      (fun _ => 0) (install (wslot extra) mid Aw) :=
    (hstep.seq hfocus).congr_in rfl hentry.symm
  have hb : ∀ (k : Fin 218) (j : Fin (219 + CloseoutFinalC10WordsStage.s)), k.val = j.val →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k) = Aw j := by
    intro k j hkj
    rw [castAdd_eq_wslot extra k j hkj]
    exact install_slot (wslot extra) (wslot_inj extra) mid Aw j
  have hsc : ∀ (k : Fin (60 + extra)) (j : Fin (219 + CloseoutFinalC10WordsStage.s)),
      218 + k.val = j.val →
      install (wslot extra) mid Aw (Fin.natAdd 218 k) = Aw j := by
    intro k j hkj
    rw [natAdd_eq_wslot extra k j hkj]
    exact install_slot (wslot extra) (wslot_inj extra) mid Aw j
  have hkeep : ∀ (k : Fin 218) (j : Fin (219 + CloseoutFinalC10WordsStage.s)), k.val = j.val →
      j.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} : Finset ℕ) →
      j.val < 219 →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k) = wordsBank extra mid j :=
    fun k j h hm hl => (hb k j h).trans (wfr j hm hl)
  -- the thirteen ports of the ready bank
  have b81 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (81 : Fin 218)) =
      CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom) :=
    (hkeep 81 81 rfl (by decide) (by decide)).trans m81
  have b83 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (83 : Fin 218)) =
      List.replicate (CompetitorRationalDecision.width (entryWidth len)) true :=
    (hb 83 83 rfl).trans w83
  have b84 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (84 : Fin 218)) =
      List.replicate (CompetitorRationalDecision.width (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length)) true := by
    rw [hlen]; exact (hb 84 84 rfl).trans w84
  have b85 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (85 : Fin 218)) =
      List.replicate (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) true := by
    rw [hlen]; exact (hb 85 85 rfl).trans w85
  have b86 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (86 : Fin 218)) =
      List.replicate (CompetitorReusableDecision.capacity (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length)) true := by
    rw [hlen]; exact (hb 86 86 rfl).trans w86
  have b90 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (90 : Fin 218)) =
      CompareMachine.word
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length := by
    rw [hlen]; exact (hb 90 90 rfl).trans w90
  have b98 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (98 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (84 : Fin 218)) :=
    ((hb 98 98 rfl).trans w98).trans (hb 84 84 rfl).symm
  have b176 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (176 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (85 : Fin 218)) :=
    ((hb 176 176 rfl).trans w176).trans (hb 85 85 rfl).symm
  have b182 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (182 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (86 : Fin 218)) :=
    ((hb 182 182 rfl).trans w182).trans (hb 86 86 rfl).symm
  have b186 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (186 : Fin 218)) =
      CompareMachine.word
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length := by
    rw [hlen]; exact (hb 186 186 rfl).trans w186
  have b187 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (187 : Fin 218)) =
      List.replicate (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) true := by
    rw [hlen]; exact (hb 187 187 rfl).trans w187
  have b213 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (213 : Fin 218)) =
      frame (SignedSortKey.binary (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) 1) := by
    rw [hlen]; exact (hb 213 213 rfl).trans w213
  have b214 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (214 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (213 : Fin 218)) :=
    ((hb 214 214 rfl).trans w214).trans (hb 213 213 rfl).symm
  -- everything else of the estimator bank is blank
  have bblank : ∀ i : Fin 218, 2 ≤ i.val → i.val < 187 →
      i.val ≠ 81 → i.val ≠ 83 → i.val ≠ 84 → i.val ≠ 85 → i.val ≠ 86 → i.val ≠ 90 →
      i.val ≠ 98 → i.val ≠ 176 → i.val ≠ 182 → i.val ≠ 186 →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) i) = [] := by
    intro i h2 hlt c81 c83 c84 c85 c86 c90 c98 c176 c182 c186
    have hi := i.isLt
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    refine (hkeep i ⟨i.val, by omega⟩ rfl ?_ ?_).trans ?_
    · show i.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · show i.val < 219
      omega
    · refine mblank _ ?_ ?_ ?_ ?_ ?_
      · show 2 ≤ i.val
        omega
      · show i.val ≠ 81
        omega
      · show i.val ≠ 90
        omega
      · show i.val ≠ 216
        omega
      · show i.val ≠ 218
        omega
  have banswer : ∀ i : Fin 218, 187 < i.val → i.val < 216 → i.val ≠ 213 → i.val ≠ 214 →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) i) = [] := by
    intro i hlt hlt' c213 c214
    have hi := i.isLt
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    refine (hkeep i ⟨i.val, by omega⟩ rfl ?_ ?_).trans ?_
    · show i.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · show i.val < 219
      omega
    · refine mblank _ ?_ ?_ ?_ ?_ ?_
      · show 2 ≤ i.val
        omega
      · show i.val ≠ 81
        omega
      · show i.val ≠ 90
        omega
      · show i.val ≠ 216
        omega
      · show i.val ≠ 218
        omega
  have bready := CloseoutFinalC10WordsStage.ready_of_words (entryWidth len)
    (phaseRecords answer denominator ph pcpp coordinate systematicAtom)
    (fun k : Fin 218 => install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k))
    b81 ⟨b83, b84, b85, b86, b90, b98, b176, b182, b186, b187, b213, b214⟩ bblank banswer
  have b0 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (0 : Fin 218)) =
      frame (List.ofFn x) := (hkeep 0 0 rfl (by decide) (by decide)).trans m0
  have b1 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (1 : Fin 218)) =
      frame bits := (hkeep 1 1 rfl (by decide) (by decide)).trans m1
  have b216 : install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (216 : Fin 218)) =
      [true] := (hkeep 216 216 rfl (by decide) (by decide)).trans m216
  have s274 : install (wslot extra) mid Aw (Fin.natAdd 218 (⟨56, by omega⟩ : Fin (60 + extra))) =
      List.replicate (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length) true := by
    rw [hlen]
    exact ((hsc ⟨56, by omega⟩ ⟨274, by decide⟩ rfl).trans w274).trans w85
  have s275 : install (wslot extra) mid Aw (Fin.natAdd 218 (⟨57, by omega⟩ : Fin (60 + extra))) =
      List.replicate (CompetitorRationalDecision.width (joinScalarWidth (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length)) true := by
    rw [hlen]
    exact ((hsc ⟨57, by omega⟩ ⟨275, by decide⟩ rfl).trans w275).trans w84
  exact ⟨fun k : Fin 218 => install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k),
    fun k : Fin (60 + extra) => install (wslot extra) mid Aw (Fin.natAdd 218 k),
    (addCases_restrict (install (wslot extra) mid Aw)).symm ▸ hrun,
    b81, b90, bready.1, bready.2, b0, b1, b216, s274, s275⟩

/-! ## §5 The block, from the prologue obligation alone -/

/-- **T3's `BlockRuns` for this stage** -- `blockRuns_of_stage` applied to
`stage_run`, so the whole phase block (supplier stage, then the embedded dock)
runs from T3's parked bank and leaves the record word of the fold on `wport`.
This is the consumer-side check that `stage_run`'s `Step` really IS the `hstage`
that `Proof/CaseAnalysis/FinalStageSeamBlock.lean` takes. -/
theorem blockRuns_of_supplierStage {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (onset len : ℕ) (x : BitInput len) (bits : List Bool)
    (hentries : ∀ entry ∈ phaseRecords answer denominator ph pcpp coordinate systematicAtom,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid (entryWidth len) entry)
    (hlen : (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length
      = callCount len)
    (hcalls : CallsReady extra (calls ph) (callFuel ph len) (entryWidth len) (callCount len)
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom))
      (List.ofFn x) bits) :
    C10TailCompose.BlockRuns (60 + extra)
      (CloseoutFinalC10StageSeam.stagedBody (stage extra calls ph)
        CloseoutFinalC10WorkerEmitLoader.emitLoader)
      (CloseoutFinalC10StageSeam.stagedFuel (stageFuel callFuel entryWidth callCount ph)
        (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
          (joinScalarWidth (entryWidth len)
            (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length))
        (entryWidth len)
        (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length len)
      (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width (entryWidth len))
          (phaseRecords answer denominator ph pcpp coordinate systematicAtom))
        (CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions (phaseRecords answer denominator ph pcpp coordinate systematicAtom)))
        1 1) := by
  obtain ⟨bank, scratch, hrun, -, -, hready, hentry, h0, h1, -, -, -⟩ :=
    stage_run extra calls callFuel entryWidth callCount answer denominator ph pcpp coordinate
      systematicAtom len x bits hlen hcalls
      (CloseoutFinalC10WorkerChain.worker onset (Fin.castAdd (60 + extra) inputTape)
        (Fin.castAdd (60 + extra) flag) (Fin.castAdd (60 + extra) result)
        (CloseoutFinalC10StageSeam.stagedBody (stage extra calls ph)
          CloseoutFinalC10WorkerEmitLoader.emitLoader))
      (by omega)
  exact CloseoutFinalC10StageSeamBlock.blockRuns_of_stage (stage extra calls ph)
    (stageFuel callFuel entryWidth callCount ph) _ onset (entryWidth len) len x bits
    (phaseRecords answer denominator ph pcpp coordinate systematicAtom) hentries bank scratch
    hready hentry h0 h1 rfl hrun

-- followed by a `depends on axioms` line.

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage
