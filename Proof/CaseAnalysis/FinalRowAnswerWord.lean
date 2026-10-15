import Proof.CaseAnalysis.FinalAnswerShift
import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.Hierarchy.CompetitorCountEntry
import Proof.MachineModel.OrdinaryRewindWorkspace

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
  (rowAnswer rowDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift
  (rowDenominator_eq_two_pow shiftAmount answerShiftFuel answer_shift_bank_dock)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
  (answer seedExponent rowAnswer_le_rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
  (bank_scratch_apply scratchOf scratchOf_apply round_step_of_dock)
open NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
  (pairList pairValue familyTotal_eq_acceptanceCount pairList_length familyWriter familyFuel
    flatten_getD)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule partsOnset width_ge_floor)
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
  (polyFuel poly_polylog_le_polyFuel repinOnset partsOnset_le_repinOnset)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel polyFuel_le_hotFuel)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The payloads of the external-row family, and their total

A.13.9's numerator, as a LIST of per-row counts. -/

/-- **The per-external-row payloads**, in the family scan order of
`pairList` (`Proof/CaseAnalysis/FinalExternalRowLoop.lean`): one
\(\sum_{z:\mathbf F(z)=\mathbf f}T_{e,\mathbf f}(z)\) per printed row. -/
noncomputable def payloadList (liveScale : ℕ) (target : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : List ℕ :=
  (pairList liveScale target request).map
    (fun p => pairValue liveScale target request p.1 p.2)

/-- The payload words at scalar width `w`, one per printed external row. -/
noncomputable def payloadWords (w liveScale : ℕ) (target : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : List (List Bool) :=
  (payloadList liveScale target request).map (binary w)

@[simp] theorem payloadWords_length (w liveScale : ℕ) (target : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (payloadWords w liveScale target request).length
      = (payloadList liveScale target request).length := by
  unfold payloadWords
  exact List.length_map _

/-- **The concatenated payload words ARE the summation engine's input word.**
`CompetitorCountFold.raw` (`Proof/Hierarchy/CompetitorCountFold.lean`) is by definition
the flat-mapped binary words, so no reformatting stands between the family's
emitted stream and the accumulator. -/
theorem payloadWords_flatten (w liveScale : ℕ) (target : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (payloadWords w liveScale target request).flatten
      = CompetitorCountFold.raw w (payloadList liveScale target request) := by
  unfold payloadWords CompetitorCountFold.raw
  rw [List.flatMap_def]

/-- **The payloads total `rowAnswer`.**  A.13.9's double sum, as one equation:
`familyTotal_eq_acceptanceCount` (`Proof/CaseAnalysis/FinalExternalRowLoop.lean`)
against `rowAnswer`'s definition as the aggregation's `acceptanceCount`
(`Proof/CaseAnalysis/FinalSupplierAccuracy.lean`). -/
theorem payloadList_sum (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity)) :
    (payloadList liveScale target ⟨arity, factors⟩).sum
      = rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors :=
  familyTotal_eq_acceptanceCount spectrum liveScale target ⟨arity, factors⟩

/-- **The numerator fits the record width**, from exactly the two hypotheses
`answer_shift_bank_dock` (`Proof/CaseAnalysis/FinalAnswerShift.lean`) already
carries: `rowAnswer` never exceeds A.13.9's own denominator
`|\mathcal E| * 2^q = 2 ^ (seedExponent + arity)` (`rowAnswer_le_rowDenominator`,
`Proof/CaseAnalysis/FinalSupplierWidth.lean`; `rowDenominator_eq_two_pow`,
`Proof/CaseAnalysis/FinalAnswerShift.lean`). -/
theorem rowAnswer_lt_two_pow (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity scale w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale)
    (hw : arity + scale + 2 ≤ w) :
    rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors < 2 ^ w := by
  have hle := rowAnswer_le_rowDenominator (symmetricFourfoldRows spectrum liveScale target)
    arity factors
  rw [rowDenominator_eq_two_pow spectrum liveScale target arity factors] at hle
  have hlt : (2 : ℕ) ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity) < 2 ^ w :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- **Every single payload fits too.**  The payloads are natural numbers whose
total is `rowAnswer`, so each is under the same bound -- the accumulator's
per-cell hypothesis `hx` costs nothing beyond §1's fit. -/
theorem payload_lt_two_pow (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity scale w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale)
    (hw : arity + scale + 2 ≤ w) :
    ∀ x ∈ payloadList liveScale target ⟨arity, factors⟩, x < 2 ^ w := by
  intro x hx
  have hsum : x ≤ (payloadList liveScale target ⟨arity, factors⟩).sum := List.le_sum_of_mem hx
  rw [payloadList_sum spectrum liveScale target arity factors] at hsum
  have := rowAnswer_lt_two_pow spectrum liveScale target arity scale w factors hfit hw
  omega

/-! ## §2 The summation engine, with its heads parked

`CompetitorCountEntry.machine` (`Proof/Hierarchy/CompetitorCountEntry.lean`) leaves its
source and count cursors where it found the ends of the words
(`CompetitorCountEntry.finalHeads`, `Proof/Hierarchy/CompetitorCountEntryHeads.lean`), so
it is not by itself dock-shaped.  `Rewind.machine`
(`Proof/Foundations/OrdinaryRewind.lean`) adds one workspace tape and parks every head at
`0` for twice the run plus two. -/

noncomputable def sumMachine :
    Machine (9 + 1) (2 + Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control 17) + 2) :=
  Rewind.machine CompetitorCountEntry.machine

/-- **The summation's fuel**: `2 * (rows * (16*w+20) + 5) + 2`.  Linear in the
number of external rows, linear in the record width -- `paper.tex:1382-1385`'s
`q^{O(1)}`, not `paper.tex:3555-3557`'s `2^q/q^\sigma`. -/
def rowAnswerFuel (w rows : ℕ) : ℕ := 2 * (rows * (16 * w + 20) + 5) + 2

/-- The ten tapes the summation reads, at scalar width `w` on both the cell and
the accumulator: the payload stream, the two paid widths, the accumulator seeded
at `frame (binary w 0)`, the field backing, the round counter, and three blanks
plus the rewind workspace. -/
noncomputable def sumInput (w : ℕ) (xs : List ℕ) : Fin (9 + 1) → List Bool :=
  fun i => match i.val with
    | 0 => CompetitorCountFold.raw w xs
    | 1 => List.replicate w true
    | 2 => List.replicate w true
    | 4 => List.replicate (2 * w + 1) false
    | 5 => frame (binary w 0)
    | 8 => RepairSource.VerifierDecoding.CompareMachine.word xs.length
    | _ => []

theorem sumInput_eq (w : ℕ) (xs : List ℕ) :
    (Fin.addCases (motive := fun _ : Fin (9 + 1) => List Bool)
        (CompetitorCountEntry.input w w xs) (fun _ : Fin 1 => List.replicate 0 false))
      = sumInput w xs := by
  funext i
  fin_cases i <;> rfl

theorem sum_ready (w : ℕ) (xs : List ℕ)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hfit : xs.sum < 2 ^ w) :
    ∃ r : ExecutionReceipt (9 + 1)
        (2 + Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control 17) + 2),
      run sumMachine (rowAnswerFuel w xs.length) (sumInput w xs) = some r ∧
      r.final.tapes 5 = frame (binary w xs.sum) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ rowAnswerFuel w xs.length := by
  obtain ⟨base, hbase, h5, _h0, hsteps⟩ :=
    CompetitorCountEntry.entry_run w w xs (le_refl w) hx hfit
  obtain ⟨r, hrun, htapes, _hwork, hheads, hrsteps, _⟩ :=
    Rewind.Workspace.reset_workspace CompetitorCountEntry.machine _ _ base hbase 0
  rw [hsteps] at hrun hrsteps
  rw [sumInput_eq w xs] at hrun
  refine ⟨r, hrun, ?_, hheads, le_of_eq hrsteps⟩
  exact (htapes 5).trans h5

/-- **The natural-count summation, docked.**  Slot `0` carries the concatenated
payload words, slots `1` and `2` the paid widths, slot `4` the field backing,
slot `5` the accumulator seeded at zero, slot `8` the round counter; slots `3`,
`6`, `7` and the rewind workspace `9` start blank.  On exit slot `5` carries
`frame (binary w xs.sum)`, every head is parked at `0`, and every tape outside
the slot map is untouched. -/
theorem sum_dock {m : ℕ} (w : ℕ) (xs : List ℕ)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hfit : xs.sum < 2 ^ w)
    (slots : Fin (9 + 1) → Fin m) (hinj : Function.Injective slots)
    (H : Fin m → ℕ) (A : Fin m → List Bool) (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = CompetitorCountFold.raw w xs)
    (h1 : A (slots 1) = List.replicate w true)
    (h2 : A (slots 2) = List.replicate w true)
    (h4 : A (slots 4) = List.replicate (2 * w + 1) false)
    (h5 : A (slots 5) = frame (binary w 0))
    (h8 : A (slots 8) = RepairSource.VerifierDecoding.CompareMachine.word xs.length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots sumMachine) (rowAnswerFuel w xs.length) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 5) = frame (binary w xs.sum) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, ht5, hheads, hsteps⟩ := sum_ready w xs hx hfit
  have hstep : Step sumMachine (rowAnswerFuel w xs.length) (fun _ => 0) (sumInput w xs)
      (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, hsteps⟩
  have hA : ∀ j : Fin (9 + 1), A (slots j) = sumInput w xs j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact hblank 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h4
    · exact h5
    · exact hblank 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hblank 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h8
    · exact hblank 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, CloseoutFinalC10WordEngines.dockH_all_zero slots H hH, ?_, ?_⟩
  · exact (RecoveryRootRound.install_slot slots hinj A rc.final.tapes 5).trans ht5
  · intro i hi
    exact RecoveryRootRound.install_other slots A rc.final.tapes i hi

theorem rowAnswer_bank_dock (extra : ℕ) (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target : ℕ → ℕ) (arity scale w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale)
    (hw : arity + scale + 2 ≤ w)
    (slots : Fin (9 + 1) → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val
      = CompetitorCountFold.raw w (payloadList liveScale target ⟨arity, factors⟩))
    (h1 : s (slots 1).val = List.replicate w true)
    (h2 : s (slots 2).val = List.replicate w true)
    (h4 : s (slots 4).val = List.replicate (2 * w + 1) false)
    (h5 : s (slots 5).val = frame (binary w 0))
    (h8 : s (slots 8).val = RepairSource.VerifierDecoding.CompareMachine.word
      (payloadList liveScale target ⟨arity, factors⟩).length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → s (slots j).val = []) :
    ∃ s' : ℕ → List Bool,
      Step (RecoveryFocus.machine slots sumMachine)
        (rowAnswerFuel w (payloadList liveScale target ⟨arity, factors⟩).length)
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s') ∧
      s' (slots 5).val
        = frame (binary w (rowAnswer (symmetricFourfoldRows spectrum liveScale target)
            arity factors)) ∧
      (∀ i : Fin (218 + (60 + extra)), 278 ≤ i.val → (∀ j, slots j ≠ i) →
        s' i.val = s i.val) := by
  have hA : ∀ j : Fin (9 + 1),
      bank stream count driver input witness s (slots j) = s (slots j).val :=
    fun j => bank_scratch_apply stream count driver input witness s (slots j) (hband j)
  have hsum := payloadList_sum spectrum liveScale target arity factors
  have hlt := rowAnswer_lt_two_pow spectrum liveScale target arity scale w factors hfit hw
  have hcells := payload_lt_two_pow spectrum liveScale target arity scale w factors hfit hw
  have htotal : (payloadList liveScale target ⟨arity, factors⟩).sum < 2 ^ w := by
    rw [hsum]
    exact hlt
  obtain ⟨H', A', hstep, hzero, ht5, hframe⟩ :=
    sum_dock w (payloadList liveScale target ⟨arity, factors⟩) hcells htotal
      slots hinj (fun _ => 0) (bank stream count driver input witness s) (fun _ => rfl)
      ((hA 0).trans h0) ((hA 1).trans h1) ((hA 2).trans h2) ((hA 4).trans h4)
      ((hA 5).trans h5) ((hA 8).trans h8)
      (fun j e0 e1 e2 e4 e5 e8 => (hA j).trans (hblank j e0 e1 e2 e4 e5 e8))
  refine ⟨scratchOf extra A' s, ?_, ?_, ?_⟩
  · exact round_step_of_dock extra
      (rowAnswerFuel w (payloadList liveScale target ⟨arity, factors⟩).length)
      stream count driver input witness s slots hband H' A' hstep hzero hframe
  · rw [scratchOf_apply extra A' s (slots 5), ht5, hsum]
  · intro i hi hoff
    rw [scratchOf_apply extra A' s i, hframe i hoff,
      bank_scratch_apply stream count driver input witness s i hi]

/-! ## §5 The word the summation eats is the loop's own emit

`family_run` (`Proof/CaseAnalysis/FinalExternalRowLoop.lean`) states its round
body as the HYPOTHESIS `hrow` and lays the emitted words end to end on the
driver's output slot.  The driver `CloseoutRowsDegreeLoop.loop_run`
(`Proof/CaseAnalysis/RowsDegreeLoop.lean`) is generic in the emitted word, so the
same loop at the PAYLOAD-WORD emit lays down exactly `CompetitorCountFold.raw w`
of the payload list -- §4's `h0` -- at the same `familyFuel` and under the same
class of body hypothesis.  Nothing here discharges that body hypothesis; it
relocates it from `Stream.recordWord` to `binary w`. -/

/-- **The family loop at the payload-word emit.**  Same driver, same fuel, same
body obligation shape as `family_run`; the accumulated word is the summation
engine's input, and the payloads still total `rowAnswer`. -/
theorem raw_family_run (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    {tp st : ℕ} (body : Machine tp st)
    (source : ℕ → List Bool → Configuration tp st) (slot : Fin tp) (rowCost : ℕ)
    (out : List Bool)
    (hslot : ∀ k pre, (source k pre).tapes slot = pre)
    (hstart : ∀ k < (payloadWords w liveScale target ⟨arity, factors⟩).length,
      ∀ pre, (source k pre).control = body.start)
    (hrow : ∀ k < (payloadWords w liveScale target ⟨arity, factors⟩).length,
      ∀ pre, ∃ rc : ExecutionReceipt tp st,
        runFrom body rowCost (source k pre) = some rc ∧
        rc.final.heads = (source (k + 1) (pre ++
          (payloadWords w liveScale target ⟨arity, factors⟩).getD k [])).heads ∧
        rc.final.tapes = (source (k + 1) (pre ++
          (payloadWords w liveScale target ⟨arity, factors⟩).getD k [])).tapes ∧
        rc.steps ≤ rowCost) :
    ∃ T, Step (familyWriter body)
        (familyFuel (payloadWords w liveScale target ⟨arity, factors⟩).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (payloadWords w liveScale target ⟨arity, factors⟩).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (payloadWords w liveScale target ⟨arity, factors⟩).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (source (payloadWords w liveScale target ⟨arity, factors⟩).length
            (out ++ (payloadWords w liveScale target ⟨arity, factors⟩).flatten))
          (payloadWords w liveScale target ⟨arity, factors⟩).length 1).heads T ∧
      T (slot.castAdd 1) =
        out ++ CompetitorCountFold.raw w (payloadList liveScale target ⟨arity, factors⟩) ∧
      (payloadList liveScale target ⟨arity, factors⟩).sum
        = rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors := by
  obtain ⟨r, hr, hf, hst⟩ := CloseoutRowsDegreeLoop.loop_run body source
    (fun k => (payloadWords w liveScale target ⟨arity, factors⟩).getD k []) rowCost
    (payloadWords w liveScale target ⟨arity, factors⟩).length hstart hrow out
  rw [flatten_getD (payloadWords w liveScale target ⟨arity, factors⟩)] at hf
  refine ⟨_, ⟨r, hr, congrArg Configuration.heads hf, congrArg Configuration.tapes hf, hst⟩, ?_,
    payloadList_sum spectrum liveScale target arity factors⟩
  rw [RepairSource.CloseoutFinal.C10SupplierSelect.cfg_tapes_castAdd]
  rw [hslot, payloadWords_flatten]

private theorem absorb (y : ℕ) (hy : 1 ≤ y) : 104 * y + 12 ≤ 128 * y := by omega

theorem rowAnswerFuel_le_widthPower (sources : RepairSource.EightSources)
    (k r degree N c rows : ℕ) (hr : 1 ≤ r) (hN : partsOnset sources k r degree ≤ N)
    (hrows : rows ≤ widthPower sources k c N) :
    rowAnswerFuel (entryWidthSchedule sources k r N) rows
      ≤ 128 * widthPower sources k (r + c) N := by
  have hq : thresholdFloor sources + 2 ≤ widthAt sources k N :=
    width_ge_floor sources k r degree N hN
  have hqp : widthAt sources k N ≤ widthPower sources k r N := by
    unfold widthPower
    calc widthAt sources k N ≤ widthAt sources k N + 1 := Nat.le_succ _
      _ = (widthAt sources k N + 1) ^ 1 := (pow_one _).symm
      _ ≤ (widthAt sources k N + 1) ^ r := Nat.pow_le_pow_right (by omega) hr
  have hP : 1 ≤ widthPower sources k r N := one_le_widthPower sources k r N
  have hQ : 1 ≤ widthPower sources k c N := one_le_widthPower sources k c N
  have hwidth : entryWidthSchedule sources k r N + 1 ≤ 2 * widthPower sources k r N := by
    unfold entryWidthSchedule
    omega
  have hfac : 16 * entryWidthSchedule sources k r N + 20 ≤ 52 * widthPower sources k r N := by
    omega
  have hsplit : widthPower sources k (r + c) N
      = widthPower sources k r N * widthPower sources k c N := by
    unfold widthPower
    rw [← pow_add]
  have hPQ : 1 ≤ widthPower sources k r N * widthPower sources k c N := by
    calc 1 = 1 * 1 := by norm_num
      _ ≤ widthPower sources k r N * widthPower sources k c N := Nat.mul_le_mul hP hQ
  have hmain : rowAnswerFuel (entryWidthSchedule sources k r N) rows
      ≤ 104 * (widthPower sources k r N * widthPower sources k c N) + 12 := by
    have hstep : rows * (16 * entryWidthSchedule sources k r N + 20)
        ≤ widthPower sources k c N * (52 * widthPower sources k r N) :=
      Nat.mul_le_mul hrows hfac
    unfold rowAnswerFuel
    nlinarith [hstep]
  calc rowAnswerFuel (entryWidthSchedule sources k r N) rows
      ≤ 104 * (widthPower sources k r N * widthPower sources k c N) + 12 := hmain
    _ ≤ 128 * (widthPower sources k r N * widthPower sources k c N) := absorb _ hPQ
    _ = 128 * widthPower sources k (r + c) N := by rw [hsplit]

theorem rowAnswerFuel_le_hotFuel (sources : RepairSource.EightSources)
    (k r degree c : ℕ) (hr : 1 ≤ r) (rows : ℕ → ℕ)
    (hrows : ∀ N, rows N ≤ widthPower sources k c N) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      rowAnswerFuel (entryWidthSchedule sources k r N) (rows N)
        ≤ hotFuel sources k r degree N := by
  obtain ⟨onset0, honset0⟩ :=
    poly_polylog_le_polyFuel 0 (128 * widthConst sources k ^ (r + c)) (r + c) 1 1
      (le_refl 1) (by omega)
  refine ⟨max onset0 (repinOnset sources k r degree 1), fun N hN => ?_⟩
  have hN0 : onset0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : repinOnset sources k r degree 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : partsOnset sources k r degree ≤ N :=
    le_trans (partsOnset_le_repinOnset sources k r degree 1) hN1
  have hstep1 := rowAnswerFuel_le_widthPower sources k r degree N c (rows N) hr hNp (hrows N)
  have hstep2 : 128 * widthPower sources k (r + c) N
      ≤ 128 * (widthConst sources k ^ (r + c) * logScale N ^ (r + c)) :=
    Nat.mul_le_mul_left _ (widthPower_le_logScale sources k (r + c) N)
  have hstep3 := honset0 N hN0
  have hstep4 := polyFuel_le_hotFuel sources k r degree 1 1 N (by omega) hN1
  have hre : (N + 1) ^ 0 * (128 * widthConst sources k ^ (r + c) * logScale N ^ (r + c))
      = 128 * (widthConst sources k ^ (r + c) * logScale N ^ (r + c)) := by ring
  rw [hre] at hstep3
  omega

/-- **THE ANSWER CHANNEL, END TO END, ON THE C.10 BAND.**  One `Step` of one
composed machine carries the bank whose band holds the family's payload words and
the shift word to the bank whose band holds A.13.9's estimate in binary at the
record width.  Every head is parked at `0` at both ends; the six ports and every
tape below `278` are untouched. -/
theorem answer_channel_bank_dock (extra : ℕ) (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target : ℕ → ℕ) (arity scale w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale)
    (hw : arity + scale + 2 ≤ w)
    (slots : Fin (9 + 1) → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (mslots : Fin 14 → Fin (218 + (60 + extra))) (hminj : Function.Injective mslots)
    (hmband : ∀ j, 278 ≤ (mslots j).val)
    (hjoin : mslots 8 = slots 5)
    (hdisj : ∀ j : Fin 14, j.val ≠ 8 → ∀ i : Fin (9 + 1), slots i ≠ mslots j)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val
      = CompetitorCountFold.raw w (payloadList liveScale target ⟨arity, factors⟩))
    (h1 : s (slots 1).val = List.replicate w true)
    (h2 : s (slots 2).val = List.replicate w true)
    (h4 : s (slots 4).val = List.replicate (2 * w + 1) false)
    (h5 : s (slots 5).val = frame (binary w 0))
    (h8 : s (slots 8).val = RepairSource.VerifierDecoding.CompareMachine.word
      (payloadList liveScale target ⟨arity, factors⟩).length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → s (slots j).val = [])
    (m0 : s (mslots 0).val = frame (CompetitorDenominator.powerBits
      (shiftAmount spectrum liveScale target arity scale factors)))
    (m9 : s (mslots 9).val = List.replicate w true)
    (mblank : ∀ j : Fin 14, j.val ≠ 0 → j.val ≠ 8 → j.val ≠ 9 → s (mslots j).val = []) :
    ∃ s'' : ℕ → List Bool,
      Step (Composition.machine (RecoveryFocus.machine slots sumMachine)
          (RecoveryFocus.machine mslots HierarchyMultiplyEntry.machine))
        (rowAnswerFuel w (payloadList liveScale target ⟨arity, factors⟩).length + 1
          + answerShiftFuel w (shiftAmount spectrum liveScale target arity scale factors))
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s'') ∧
      s'' (mslots 3).val
        = frame (binary w (answer (symmetricFourfoldRows spectrum liveScale target)
            arity scale factors)) := by
  obtain ⟨s', hsum, hacc, hkeep⟩ :=
    rowAnswer_bank_dock extra spectrum liveScale target arity scale w factors hfit hw
      slots hinj hband stream count driver input witness s h0 h1 h2 h4 h5 h8 hblank
  have hother : ∀ j : Fin 14, j.val ≠ 8 → s' (mslots j).val = s (mslots j).val :=
    fun j hj => hkeep (mslots j) (hmband j) (fun i => hdisj j hj i)
  obtain ⟨s'', hshift, hout⟩ :=
    answer_shift_bank_dock extra spectrum liveScale target arity scale w factors hfit hw
      mslots hminj hmband stream count driver input witness s'
      ((hother 0 (by decide)).trans m0)
      (by rw [hjoin]; exact hacc)
      ((hother 9 (by decide)).trans m9)
      (fun j e0 e8 e9 => (hother j e8).trans (mblank j e0 e8 e9))
  exact ⟨s'', hsum.seq hshift, hout⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord
