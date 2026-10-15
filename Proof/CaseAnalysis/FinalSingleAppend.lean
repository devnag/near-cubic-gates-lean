import Proof.CaseAnalysis.FinalAppendPositioning

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SingleAppend

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def raw := Composition.machine
  (Composition.machine CloseoutFinalC10AppendPositioning.enter CloseoutFinalC10AppendPositioning.seek)
  (TapeEmbedding.machine 1 CloseoutFinalC10SiteRoundPortAppend.machine)

noncomputable def machine := MaskedReset.machine raw (fun _ => true)

private theorem words_snoc (b : Nat) (xs : List Stream.Entry) (entry : Stream.Entry) :
    Stream.words b (xs++[entry])=Stream.words b xs++Stream.entryWord b entry := by
  simp only [Stream.words,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- Exact single append; the old two-append budget is a conservative bound. -/
theorem raw_step (width padding logSize : Nat) (entry : Stream.Entry) (xs : List Stream.Entry)
    (hlog : 20*width+27≤logSize) :
    let payload := ZeroPadding.pad padding (Stream.entryWord width entry)
    Step raw (CloseoutFinalC10AppendPositioning.rawBudget width xs.length) (fun _ => 0)
      (CloseoutFinalC10AppendPositioning.data width payload (Stream.words width xs) logSize xs.length)
      (CloseoutFinalC10AppendPositioning.heads (Stream.words width (xs++[entry])).length)
      (CloseoutFinalC10AppendPositioning.data width payload
        (Stream.words width (xs++[entry])) logSize (xs++[entry]).length) := by
  dsimp only
  have copied := (CloseoutFinalC10SiteRoundPortAppend.append_step width entry.count
    entry.denominator padding logSize xs.length entry.coefficient (Stream.words width xs) hlog).embed
      (fun _ : Fin 1 => 1) (fun _ => UnaryTemplate.tape (20*width+22))
  have last : Step (TapeEmbedding.machine 1 CloseoutFinalC10SiteRoundPortAppend.machine)
      (CloseoutFinalC10SiteRoundPortAppend.budget width xs.length)
      (CloseoutFinalC10AppendPositioning.heads (Stream.words width xs).length)
      (CloseoutFinalC10AppendPositioning.data width
        (ZeroPadding.pad padding (Stream.entryWord width entry)) (Stream.words width xs) logSize xs.length)
      (CloseoutFinalC10AppendPositioning.heads (Stream.words width (xs++[entry])).length)
      (CloseoutFinalC10AppendPositioning.data width
        (ZeroPadding.pad padding (Stream.entryWord width entry))
        (Stream.words width (xs++[entry])) logSize (xs++[entry]).length) := by
    rw [words_snoc,show (xs++[entry]).length=xs.length+1 from by simp]
    refine (copied.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i; fin_cases i <;> rfl
  have joined := ((CloseoutFinalC10AppendPositioning.enter_step _).seq
    (CloseoutFinalC10AppendPositioning.seek_step width logSize _ xs)).seq last
  apply joined.enlarge
  unfold CloseoutFinalC10AppendPositioning.rawBudget CloseoutFinalC10SiteRoundPortAppend.twiceBudget
  omega

/-- Six resident tapes, all local heads zero on both sides; the payload,
    copy log, width template and reset log are literally reusable. -/
theorem run (width padding logSize resetSize : Nat)
    (entry : Stream.Entry) (xs : List Stream.Entry)
    (hlog : 20*width+27≤logSize)
    (hreset : CloseoutFinalC10AppendPositioning.rawBudget width xs.length≤resetSize) :
    Step machine (CloseoutFinalC10AppendPositioning.budget width xs.length) (fun _ => 0)
      (CloseoutFinalC10AppendPositioning.tapes width padding logSize resetSize entry xs)
      (fun _ => 0)
      (CloseoutFinalC10AppendPositioning.tapes width padding logSize resetSize entry (xs++[entry])) := by
  have actual := (raw_step width padding logSize entry xs hlog).mask
    (fun _ => true) (by intros; rfl) hreset
  refine (actual.congr_in ?_ rfl).congr ?_ rfl
  all_goals funext i; fin_cases i <;> rfl

/-- The retained payload/stream/count/template/log boundary at any actual map.
    All selected heads, including the payload, start zero; ambient heads stay. -/
theorem docked_run {B : Nat} (slots : Fin 6 → Fin B) (hi : Function.Injective slots)
    (width padding logSize resetSize : Nat) (entry : Stream.Entry) (xs : List Stream.Entry)
    (H : Fin B → Nat) (bank : Fin B → List Bool)
    (hh : ∀ i,H (slots i)=0)
    (input : ∀ i,bank (slots i)=
      CloseoutFinalC10AppendPositioning.tapes width padding logSize resetSize entry xs i)
    (hlog : 20*width+27≤logSize)
    (hreset : CloseoutFinalC10AppendPositioning.rawBudget width xs.length≤resetSize) :
    let next := CloseoutFinalC10AppendPositioning.tapes width padding logSize resetSize entry (xs++[entry])
    Step (RecoveryFocus.machine slots machine)
      (CloseoutFinalC10AppendPositioning.budget width xs.length) H bank H (install slots bank next) ∧
    (∀ i,install slots bank next (slots i)=next i) ∧
    (∀ v,(∀ i,slots i≠v) → install slots bank next v=bank v) := by
  dsimp only
  refine ⟨((run width padding logSize resetSize entry xs hlog hreset).dock
    slots hi H bank hh input).congr (dockH_existing slots H _ hh) rfl,?_,?_⟩
  · exact install_slot slots hi bank _
  · exact install_other slots bank _

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SingleAppend
