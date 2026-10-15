import Proof.CaseAnalysis.RowsEstimatorAppendPadded
import Proof.CaseAnalysis.RowsEstimatorParityCounter
import Proof.CaseAnalysis.FinalSiteRoundPorts

/-! The physical record/count append segment of a C.10 site round.

The local record is an explicit produced-input precondition. The same fixed
four-tape machine appends its six fields to an arbitrary existing stream and
increments the existing unary record count. It returns the record cursor and
the same padded reset log, so a second operation reuses both tapes literally.
The copy's 40*b+56 includes its cursor restore; the counter pays 2*n+2; their
composition pays one bridge step. No empty-scratch restoration is assumed.

This segment starts/ends with the stream at its append cursor and the count
at head 1. The enclosing hsite starts/ends with ALL heads at 0. Its seek/rewind
and actual record producer are still separate typed obligations; this file
does not assert hsite or supply those operands for free.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPortAppend

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
open CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 4 → ℕ := ![0, out.length, 0, 1]

def data (payload out : List Bool) (logSize count : ℕ) : Fin 4 → List Bool :=
  ![payload, out, List.replicate logSize false, CompareMachine.word count]

def countSlot (_ : Fin 1) : Fin 4 := 3

theorem countSlot_injective : Function.Injective countSlot := by decide

noncomputable def machine := Composition.machine
  (TapeEmbedding.machine 1 CloseoutRowsEstimator.AppendCopy.machine)
  (RecoveryFocus.machine countSlot CloseoutRowsEstimatorParity.Counter.machine)

def budget (width count : ℕ) : ℕ := (40 * width + 56) + 1 + (2 * count + 2)

theorem count_heads (out : List Bool) :
    dockH countSlot (heads out) (fun _ : Fin 1 => 1) = heads out := by
  apply dockH_existing
  intro j
  rfl

theorem install_count (payload out : List Bool) (logSize oldCount newCount : ℕ) :
    install countSlot (data payload out logSize oldCount)
      (fun _ : Fin 1 => CompareMachine.word newCount) = data payload out logSize newCount := by
  funext i
  fin_cases i
  · exact install_other countSlot _ _ 0 (by intro j; fin_cases j; decide)
  · exact install_other countSlot _ _ 1 (by intro j; fin_cases j; decide)
  · exact install_other countSlot _ _ 2 (by intro j; fin_cases j; decide)
  · exact install_slot countSlot countSlot_injective _ _ 0

/-- A complete physical append of one supplied record and its unary count. -/
theorem append_step (width numerator denominator padding logSize count : ℕ)
    (coefficient : CompetitorValidity.Estimate) (out : List Bool)
    (hlog : 20 * width + 27 ≤ logSize) :
    let payload := ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator)
    let next := out ++ Stream.recordWord width coefficient numerator denominator
    Step machine (budget width count) (heads out) (data payload out logSize count)
      (heads next) (data payload next logSize (count + 1)) := by
  dsimp only
  obtain ⟨r, hr, hh, ht, hs⟩ := CloseoutRowsEstimator.AppendPadded.run
    width coefficient numerator denominator padding logSize out hlog
  have raw : Step CloseoutRowsEstimator.AppendCopy.machine (40 * width + 56)
      ![0, out.length, 0]
      ![ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator),
        out, List.replicate logSize false]
      ![0, (out ++ Stream.recordWord width coefficient numerator denominator).length, 0]
      ![ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator),
        out ++ Stream.recordWord width coefficient numerator denominator,
        List.replicate logSize false] := ⟨r, hr, hh, ht, hs⟩
  have embedded := raw.embed (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word count)
  have first : Step (TapeEmbedding.machine 1 CloseoutRowsEstimator.AppendCopy.machine)
      (40 * width + 56) (heads out)
      (data (ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator))
        out logSize count)
      (heads (out ++ Stream.recordWord width coefficient numerator denominator))
      (data (ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator))
        (out ++ Stream.recordWord width coefficient numerator denominator) logSize count) := by
    refine (embedded.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i; fin_cases i <;> rfl
  have counted := (CloseoutRowsEstimatorParity.Counter.increment_run count).focus
    countSlot countSlot_injective
    (heads (out ++ Stream.recordWord width coefficient numerator denominator))
    (data (ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator))
      (out ++ Stream.recordWord width coefficient numerator denominator) logSize count)
  have second := (counted.congr_in (count_heads _) (install_count _ _ _ _ _)).congr
    (count_heads _) (install_count _ _ _ _ _)
  exact first.seq second

noncomputable def twice := Composition.machine machine machine

def twiceBudget (width count : ℕ) : ℕ := budget width count + 1 + budget width (count + 1)

theorem twiceBudget_eq (width count : ℕ) :
    twiceBudget width count = 80 * width + 4 * count + 121 := by
  unfold twiceBudget budget
  omega

/-- The record-count cap gives a budget independent of the current round. -/
theorem twiceBudget_le (width count callCap : ℕ) (hcount : count ≤ callCap) :
    twiceBudget width count ≤ 80 * width + 4 * callCap + 121 := by
  rw [twiceBudget_eq]
  omega

/-- Both calls use the same source and zero log; the second starts from the
first's actual nonempty appended output and incremented public count. -/
theorem two_appends (width numerator denominator padding logSize count : ℕ)
    (coefficient : CompetitorValidity.Estimate) (out : List Bool)
    (hlog : 20 * width + 27 ≤ logSize) :
    let record := Stream.recordWord width coefficient numerator denominator
    let payload := ZeroPadding.pad padding record
    Step twice (twiceBudget width count) (heads out) (data payload out logSize count)
      (heads ((out ++ record) ++ record))
      (data payload ((out ++ record) ++ record) logSize (count + 2)) := by
  dsimp only
  have first := append_step width numerator denominator padding logSize count coefficient out hlog
  have second := append_step width numerator denominator padding logSize (count + 1) coefficient
    (out ++ Stream.recordWord width coefficient numerator denominator) hlog
  exact first.seq second

/-- The runtime ports are exactly the existing stream/count words after two
copies of the same record. The prefix may already contain any records. -/
theorem two_entries (width padding logSize : ℕ) (entry : Stream.Entry) (xs : List Stream.Entry)
    (hlog : 20 * width + 27 ≤ logSize) :
    let payload := ZeroPadding.pad padding (Stream.entryWord width entry)
    Step twice (twiceBudget width xs.length) (heads (Stream.words width xs))
      (data payload (Stream.words width xs) logSize xs.length)
      (heads (Stream.words width (xs ++ [entry, entry])))
      (data payload (Stream.words width (xs ++ [entry, entry])) logSize
        (xs ++ [entry, entry]).length) := by
  simpa only [Stream.words, Stream.entryWord, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, List.length_append,
    List.length_cons, List.length_nil] using
    two_appends width entry.count entry.denominator padding logSize xs.length
      entry.coefficient (Stream.words width xs) hlog

/-- Fixed ambient slots: payload and log are private; 81/90 are the public
stream/count ports. Additional scratch, including a cursor, stays outside them. -/
def portSlots (extra : ℕ) (hfit : 2 ≤ extra) : Fin 4 → Fin (218 + (60 + extra)) :=
  ![⟨278, by omega⟩, ⟨81, by omega⟩, ⟨279, by omega⟩, ⟨90, by omega⟩]

theorem portSlots_injective (extra : ℕ) (hfit : 2 ≤ extra) :
    Function.Injective (portSlots extra hfit) := by
  intro i j hij
  have h := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> simp_all [portSlots]

/-- A checked physical two-operation run in the C.10 bank, with every untouched
tape/head retained by `install`/`dockH`, including input and witness ports. -/
theorem two_entries_at_ports (extra : ℕ) (hfit : 2 ≤ extra)
    (width padding logSize : ℕ) (entry : Stream.Entry) (xs : List Stream.Entry)
    (ambientH : Fin (218 + (60 + extra)) → ℕ)
    (ambient : Fin (218 + (60 + extra)) → List Bool)
    (hlog : 20 * width + 27 ≤ logSize) :
    let slots := portSlots extra hfit
    let payload := ZeroPadding.pad padding (Stream.entryWord width entry)
    Step (RecoveryFocus.machine slots twice) (twiceBudget width xs.length)
      (dockH slots ambientH (heads (Stream.words width xs)))
      (install slots ambient (data payload (Stream.words width xs) logSize xs.length))
      (dockH slots ambientH (heads (Stream.words width (xs ++ [entry, entry]))))
      (install slots ambient (data payload (Stream.words width (xs ++ [entry, entry])) logSize
        (xs ++ [entry, entry]).length)) :=
  (two_entries width padding logSize entry xs hlog).focus
    (portSlots extra hfit) (portSlots_injective extra hfit) ambientH ambient

def bankHeads (extra width : ℕ) (xs : List Stream.Entry) : Fin (218 + (60 + extra)) → ℕ :=
  fun i => if i.val = 81 then (Stream.words width xs).length else if i.val = 90 then 1 else 0

theorem dock_bankHeads (extra : ℕ) (hfit : 2 ≤ extra) (width : ℕ)
    (xs ys : List Stream.Entry) :
    dockH (portSlots extra hfit) (bankHeads extra width xs) (heads (Stream.words width ys)) =
      bankHeads extra width ys := by
  funext i
  by_cases hi : ∃ j, portSlots extra hfit j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [dockH_slot _ (portSlots_injective extra hfit)]
    fin_cases j <;> rfl
  · have hn : ∀ j, portSlots extra hfit j ≠ i := by simpa only [not_exists] using hi
    have h81 : i.val ≠ 81 := fun hv => hn 1 (Fin.ext hv.symm)
    have h90 : i.val ≠ 90 := fun hv => hn 3 (Fin.ext hv.symm)
    rw [dockH_other _ _ _ _ hn]
    simp only [bankHeads, h81, h90, ↓reduceIte]

theorem install_prefixBank (extra : ℕ) (hfit : 2 ≤ extra) (width padding logSize : ℕ)
    (entry : Stream.Entry) (xs ys : List Stream.Entry) (input witness : List Bool)
    (scratch : ℕ → List Bool)
    (hp : scratch 278 = ZeroPadding.pad padding (Stream.entryWord width entry))
    (hl : scratch 279 = List.replicate logSize false) :
    install (portSlots extra hfit)
      (CloseoutFinalC10ExactRecordLoop.prefixBank extra width xs input witness scratch)
      (data (ZeroPadding.pad padding (Stream.entryWord width entry))
        (Stream.words width ys) logSize ys.length) =
      CloseoutFinalC10ExactRecordLoop.prefixBank extra width ys input witness scratch := by
  funext i
  by_cases hi : ∃ j, portSlots extra hfit j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [install_slot _ (portSlots_injective extra hfit)]
    fin_cases j <;>
      simp [data, CloseoutFinalC10ExactRecordLoop.prefixBank,
        RepairSource.CloseoutFinal.C10SupplierCall.bank,
        RepairSource.CloseoutFinal.C10SupplierCall.bankAt, portSlots, hp, hl]
  · have hn : ∀ j, portSlots extra hfit j ≠ i := by simpa only [not_exists] using hi
    have h81 : i.val ≠ 81 := fun hv => hn 1 (Fin.ext hv.symm)
    have h90 : i.val ≠ 90 := fun hv => hn 3 (Fin.ext hv.symm)
    rw [install_other _ _ _ _ hn]
    simp only [CloseoutFinalC10ExactRecordLoop.prefixBank,
      RepairSource.CloseoutFinal.C10SupplierCall.bank,
      RepairSource.CloseoutFinal.C10SupplierCall.bankAt, h81, h90, ↓reduceIte]

/-- The actual prefixBank-to-prefixBank segment, with explicit physical payload
and log premises. Every other bank tape, including input/witness/cursor scratch,
is preserved. The only remaining positioning difference from hsite is bankHeads. -/
theorem two_entries_bank (extra : ℕ) (hfit : 2 ≤ extra) (width padding logSize : ℕ)
    (entry : Stream.Entry) (xs : List Stream.Entry) (input witness : List Bool)
    (scratch : ℕ → List Bool)
    (hp : scratch 278 = ZeroPadding.pad padding (Stream.entryWord width entry))
    (hl : scratch 279 = List.replicate logSize false)
    (hlog : 20 * width + 27 ≤ logSize) :
    Step (RecoveryFocus.machine (portSlots extra hfit) twice) (twiceBudget width xs.length)
      (bankHeads extra width xs)
      (CloseoutFinalC10ExactRecordLoop.prefixBank extra width xs input witness scratch)
      (bankHeads extra width (xs ++ [entry, entry]))
      (CloseoutFinalC10ExactRecordLoop.prefixBank extra width (xs ++ [entry, entry])
        input witness scratch) := by
  have actual := two_entries_at_ports extra hfit width padding logSize entry xs
    (bankHeads extra width xs)
    (CloseoutFinalC10ExactRecordLoop.prefixBank extra width xs input witness scratch) hlog
  exact (actual.congr_in (dock_bankHeads _ _ _ _ _)
    (install_prefixBank _ _ _ _ _ _ _ _ _ _ _ hp hl)).congr
    (dock_bankHeads _ _ _ _ _) (install_prefixBank _ _ _ _ _ _ _ _ _ _ _ hp hl)

/-- The current appender boundary is not the all-zero-head hsite boundary. -/
theorem entry_heads_ne_zero (out : List Bool) : heads out ≠ (fun _ => 0) := by
  intro h
  have impossible := congrFun h 3
  change 1 = 0 at impossible
  omega

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPortAppend
