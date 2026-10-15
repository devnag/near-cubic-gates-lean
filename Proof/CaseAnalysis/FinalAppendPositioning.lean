import Proof.CaseAnalysis.FinalSiteRoundPortAppend
import Proof.PCP.PCPPQueryRows
import Proof.Circuits.DecompositionCountPosition

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AppendPositioning

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seekSlots : Fin 4 → Fin 5 := ![4, 1, 2, 3]
theorem seekSlots_injective : Function.Injective seekSlots := by decide

def heads (pos : ℕ) : Fin 5 → ℕ := ![0, pos, 0, 1, 1]
def data (width : ℕ) (payload out : List Bool) (logSize count : ℕ) : Fin 5 → List Bool :=
  ![payload, out, List.replicate logSize false, CompareMachine.word count,
    UnaryTemplate.tape (20 * width + 22)]

def enter := DecompositionCountPosition.move
  (![.stay, .stay, .stay, .right, .right] : Fin 5 → HeadMove)
noncomputable def seek := RecoveryFocus.machine seekSlots PCPPQueryRows.skip
noncomputable def raw := Composition.machine (Composition.machine enter seek)
  (TapeEmbedding.machine 1 CloseoutFinalC10SiteRoundPortAppend.twice)
noncomputable def machine := MaskedReset.machine raw (fun _ => true)

def seekBudget (width count : ℕ) := count * (2 * (20 * width + 22) + 7) + 3
def rawBudget (width count : ℕ) := 1 + 1 + seekBudget width count + 1 + CloseoutFinalC10SiteRoundPortAppend.twiceBudget width count
def budget (width count : ℕ) := 2 * rawBudget width count + 2

theorem budget_eq (width count : ℕ) :
    budget width count = 80 * count * width + 110 * count + 160 * width + 256 := by
  unfold budget rawBudget seekBudget
  rw [CloseoutFinalC10SiteRoundPortAppend.twiceBudget_eq]
  ring

/-- A global call-count cap pays the same machine independently of the round. -/
theorem rawBudget_mono (width count callCap : ℕ) (hcount : count ≤ callCap) :
    rawBudget width count ≤ rawBudget width callCap := by
  unfold rawBudget seekBudget
  rw [CloseoutFinalC10SiteRoundPortAppend.twiceBudget_eq,
    CloseoutFinalC10SiteRoundPortAppend.twiceBudget_eq]
  have hm := Nat.mul_le_mul_right (2 * (20 * width + 22) + 7) hcount
  omega

theorem budget_mono (width count callCap : ℕ) (hcount : count ≤ callCap) :
    budget width count ≤ budget width callCap := by
  unfold budget
  have hm := rawBudget_mono width count callCap hcount
  omega

theorem enter_step (tapes : Fin 5 → List Bool) :
    Step enter 1 (fun _ => 0) tapes (heads 0) tapes := by
  obtain ⟨r, hr, hf, hs⟩ := DecompositionCountPosition.move_run
    (![.stay, .stay, .stay, .right, .right] : Fin 5 → HeadMove) (fun _ => 0) tapes
  refine ⟨r, hr, ?_, ?_, le_of_eq hs⟩
  · rw [hf]; funext i; fin_cases i <;> rfl
  · rw [hf]

/-- Skip whole records using the resident unary count and width. The unused
skip output is padded to the existing copy log, so no empty tape is demanded. -/
theorem seek_step (width logSize : ℕ) (payload : List Bool) (xs : List Stream.Entry) :
    Step seek (seekBudget width xs.length) (heads 0)
      (data width payload (Stream.words width xs) logSize xs.length)
      (heads (Stream.words width xs).length)
      (data width payload (Stream.words width xs) logSize xs.length) := by
  let rows := xs.map (Stream.entryWord width)
  have hw : ∀ row ∈ rows, row.length = 20 * width + 22 := by
    intro row hrow
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hrow
    exact CloseoutFinalC10SiteRoundPorts.entryWord_length width entry
  obtain ⟨r, hr, hf, hs⟩ := PCPPQueryRows.skip_run (20 * width + 22) [] rows [] [] hw
  have hrows : rows.flatten = Stream.words width xs := by
    simp [rows, Stream.words, List.flatMap]
  have hlen : rows.length = xs.length := by simp [rows]
  simp only [hrows, hlen, List.nil_append, List.append_nil, List.length_nil,
    Nat.zero_add] at hr hf hs
  have hinit : PCPPQueryRows.cfg 0 (20 * width + 22) (Stream.words width xs) 0 [] xs.length 1 =
      (⟨PCPPQueryRows.skip.start, ![1, 0, 0, 1],
        ![UnaryTemplate.tape (20 * width + 22), Stream.words width xs, [],
          CompareMachine.word xs.length]⟩ : Configuration 4 _) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have localRun : Step PCPPQueryRows.skip (seekBudget width xs.length)
      ![1, 0, 0, 1]
      ![UnaryTemplate.tape (20 * width + 22), Stream.words width xs, [], CompareMachine.word xs.length]
      ![1, (Stream.words width xs).length, 0, 1]
      ![UnaryTemplate.tape (20 * width + 22), Stream.words width xs, [], CompareMachine.word xs.length] := by
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · simpa only [hinit, seekBudget] using hr
    · rw [hf]; funext i; fin_cases i <;>
        rfl
    · rw [hf]; funext i; fin_cases i <;>
        rfl
    · exact le_of_eq hs
  have padded := localRun.pad (![0, 0, logSize, 0] : Fin 4 → ℕ)
  have hpad : (fun i : Fin 4 => ZeroPadding.pad
      ((![0, 0, logSize, 0] : Fin 4 → ℕ) i)
      ((![UnaryTemplate.tape (20 * width + 22), Stream.words width xs, [],
        CompareMachine.word xs.length] : Fin 4 → List Bool) i)) =
      ![UnaryTemplate.tape (20 * width + 22), Stream.words width xs,
        List.replicate logSize false, CompareMachine.word xs.length] := by
    funext i; fin_cases i <;> simp [ZeroPadding.pad]
  have actual := ((padded.congr_in rfl hpad).congr rfl hpad).focus seekSlots seekSlots_injective
    (heads 0) (data width payload (Stream.words width xs) logSize xs.length)
  refine (actual.congr_in ?_ ?_).congr ?_ ?_
  all_goals
    funext i
    fin_cases i
    · first | exact dockH_other seekSlots _ _ 0 (by decide)
            | exact install_other seekSlots _ _ 0 (by decide)
    · first | exact dockH_slot seekSlots seekSlots_injective _ _ 1
            | exact install_slot seekSlots seekSlots_injective _ _ 1
    · first | exact dockH_slot seekSlots seekSlots_injective _ _ 2
            | exact install_slot seekSlots seekSlots_injective _ _ 2
    · first | exact dockH_slot seekSlots seekSlots_injective _ _ 3
            | exact install_slot seekSlots seekSlots_injective _ _ 3
    · first | exact dockH_slot seekSlots seekSlots_injective _ _ 0
            | exact install_slot seekSlots seekSlots_injective _ _ 0

theorem raw_step (width padding logSize : ℕ) (entry : Stream.Entry) (xs : List Stream.Entry)
    (hlog : 20 * width + 27 ≤ logSize) :
    let payload := ZeroPadding.pad padding (Stream.entryWord width entry)
    Step raw (rawBudget width xs.length) (fun _ => 0)
      (data width payload (Stream.words width xs) logSize xs.length)
      (heads (Stream.words width (xs ++ [entry, entry])).length)
      (data width payload (Stream.words width (xs ++ [entry, entry])) logSize
        (xs ++ [entry, entry]).length) := by
  dsimp only
  have copied := (CloseoutFinalC10SiteRoundPortAppend.two_entries width padding logSize entry xs hlog).embed
    (fun _ : Fin 1 => 1) (fun _ => UnaryTemplate.tape (20 * width + 22))
  have last : Step (TapeEmbedding.machine 1 CloseoutFinalC10SiteRoundPortAppend.twice) (CloseoutFinalC10SiteRoundPortAppend.twiceBudget width xs.length)
      (heads (Stream.words width xs).length)
      (data width (ZeroPadding.pad padding (Stream.entryWord width entry))
        (Stream.words width xs) logSize xs.length)
      (heads (Stream.words width (xs ++ [entry, entry])).length)
      (data width (ZeroPadding.pad padding (Stream.entryWord width entry))
        (Stream.words width (xs ++ [entry, entry])) logSize (xs ++ [entry, entry]).length) := by
    refine (copied.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i; fin_cases i <;> rfl
  exact ((enter_step _).seq (seek_step width logSize _ xs)).seq last

def tapes (width padding logSize resetSize : ℕ) (entry : Stream.Entry)
    (xs : List Stream.Entry) : Fin 6 → List Bool :=
  fun i => Fin.addCases (motive := fun _ => List Bool)
    (data width (ZeroPadding.pad padding (Stream.entryWord width entry))
      (Stream.words width xs) logSize xs.length) (fun _ : Fin 1 => List.replicate resetSize false) i

/-- The fixed machine pays setup, seeking, both appends and a full local rewind.
Both ends have zero heads and exactly the same resident private tapes. -/
theorem two_entries_zero (width padding logSize resetSize : ℕ)
    (entry : Stream.Entry) (xs : List Stream.Entry)
    (hlog : 20 * width + 27 ≤ logSize)
    (hreset : rawBudget width xs.length ≤ resetSize) :
    Step machine (budget width xs.length) (fun _ => 0)
      (tapes width padding logSize resetSize entry xs) (fun _ => 0)
      (tapes width padding logSize resetSize entry (xs ++ [entry, entry])) := by
  have actual := (raw_step width padding logSize entry xs hlog).mask
    (fun _ => true) (by intros; rfl) hreset
  refine (actual.congr_in ?_ rfl).congr ?_ rfl
  all_goals funext i; fin_cases i <;> rfl

/-- Only four private tapes: the existing record and copy log, then a resident
record-width template and the padded rewind log. Public ports remain 81/90. -/
def portSlots (extra : ℕ) (hfit : 4 ≤ extra) : Fin 6 → Fin (218 + (60 + extra)) :=
  ![⟨278, by omega⟩, ⟨81, by omega⟩, ⟨279, by omega⟩, ⟨90, by omega⟩,
    ⟨280, by omega⟩, ⟨281, by omega⟩]

theorem portSlots_injective (extra : ℕ) (hfit : 4 ≤ extra) :
    Function.Injective (portSlots extra hfit) := by
  intro i j hij
  have h := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> simp_all [portSlots]

theorem install_prefixBank (extra : ℕ) (hfit : 4 ≤ extra)
    (width padding logSize resetSize : ℕ) (entry : Stream.Entry)
    (xs ys : List Stream.Entry) (input witness : List Bool) (scratch : ℕ → List Bool)
    (hp : scratch 278 = ZeroPadding.pad padding (Stream.entryWord width entry))
    (hl : scratch 279 = List.replicate logSize false)
    (hw : scratch 280 = UnaryTemplate.tape (20 * width + 22))
    (hr : scratch 281 = List.replicate resetSize false) :
    install (portSlots extra hfit)
      (CloseoutFinalC10ExactRecordLoop.prefixBank extra width xs input witness scratch)
      (tapes width padding logSize resetSize entry ys) =
      CloseoutFinalC10ExactRecordLoop.prefixBank extra width ys input witness scratch := by
  funext i
  by_cases hi : ∃ j, portSlots extra hfit j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [install_slot _ (portSlots_injective extra hfit)]
    fin_cases j <;>
      simp [tapes, data, CloseoutFinalC10ExactRecordLoop.prefixBank,
        RepairSource.CloseoutFinal.C10SupplierCall.bank,
        RepairSource.CloseoutFinal.C10SupplierCall.bankAt, portSlots, hp, hl, hw, hr] <;> rfl
  · have hn : ∀ j, portSlots extra hfit j ≠ i := by simpa only [not_exists] using hi
    have h81 : i.val ≠ 81 := fun hv => hn 1 (Fin.ext hv.symm)
    have h90 : i.val ≠ 90 := fun hv => hn 3 (Fin.ext hv.symm)
    rw [install_other _ _ _ _ hn]
    simp only [CloseoutFinalC10ExactRecordLoop.prefixBank,
      RepairSource.CloseoutFinal.C10SupplierCall.bank,
      RepairSource.CloseoutFinal.C10SupplierCall.bankAt, h81, h90, ↓reduceIte]

/-- Actual zero-head prefixBank-to-prefixBank append, with the four resident
scratch operands exposed. Every other tape, including cursor/cache data, stays
literal. This is a segment; the supplied record still needs its site producer. -/
theorem two_entries_bank (extra : ℕ) (hfit : 4 ≤ extra)
    (width padding logSize resetSize : ℕ) (entry : Stream.Entry)
    (xs : List Stream.Entry) (input witness : List Bool) (scratch : ℕ → List Bool)
    (hp : scratch 278 = ZeroPadding.pad padding (Stream.entryWord width entry))
    (hl : scratch 279 = List.replicate logSize false)
    (hw : scratch 280 = UnaryTemplate.tape (20 * width + 22))
    (hr : scratch 281 = List.replicate resetSize false)
    (hlog : 20 * width + 27 ≤ logSize)
    (hreset : rawBudget width xs.length ≤ resetSize) :
    Step (RecoveryFocus.machine (portSlots extra hfit) machine) (budget width xs.length)
      (fun _ => 0) (CloseoutFinalC10ExactRecordLoop.prefixBank extra width xs input witness scratch)
      (fun _ => 0) (CloseoutFinalC10ExactRecordLoop.prefixBank extra width (xs ++ [entry, entry])
        input witness scratch) := by
  have actual := (two_entries_zero width padding logSize resetSize entry xs hlog hreset).focus
    (portSlots extra hfit) (portSlots_injective extra hfit) (fun _ => 0)
    (CloseoutFinalC10ExactRecordLoop.prefixBank extra width xs input witness scratch)
  have hh := dockH_existing (portSlots extra hfit) (fun _ => 0) (fun _ => 0) (by intros; rfl)
  exact (actual.congr_in hh (install_prefixBank _ _ _ _ _ _ _ _ _ _ _ _ hp hl hw hr)).congr hh
    (install_prefixBank _ _ _ _ _ _ _ _ _ _ _ _ hp hl hw hr)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10AppendPositioning
