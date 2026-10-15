import Proof.Hierarchy.CompetitorCountRecord

/-! The prepared exact selected SUM is consumed directly by the record
appender. This caller derives zero and append workspace from its scalar
width; it does not repeat the table scan or SUM. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prepareSlots (i : Fin 23) : Fin 29 := i.castAdd 6
def fields : List (Fin 29) := [23,24,25,20,26,27]
noncomputable def prepare := RecoveryFocus.machine prepareSlots CompetitorCountRecordPrepare.machine
noncomputable def emit := CompetitorRawFieldEmit.listProgram (28 : Fin 29) 22 fields
noncomputable def machine := Composition.machine prepare emit

def scalarFields (b : ℕ) (q : ℚ) (count denominator : ℕ) : Fin 29 → List Bool :=
  fun i => match i.val with
    | 23 => binary (width b) (positive q)
    | 24 => binary (width b) (negative q)
    | 25 => binary (width b) q.den
    | 20 => binary (width b) 0
    | 26 => binary b denominator
    | 27 => binary b count
    | _ => []
def input (b : ℕ) (q : ℚ) (count denominator : ℕ) : Fin 29 → List Bool :=
  fun i => if i=0 then List.replicate b true else if 23 ≤ i.val ∧ i.val≤27 then
    frame (scalarFields b q count denominator i) else []
def budget (b : ℕ) := CompetitorCountRecordPrepare.budget b+1+(40*b+56)

theorem prepare_injective : Function.Injective prepareSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 29 => k.val) h)

theorem stream_eq (b : ℕ) (q : ℚ) (count denominator : ℕ) :
    CompetitorRawFieldEmit.stream (scalarFields b q count denominator) fields=
      CompetitorMonomialStream.recordWord b q count denominator := rfl

theorem emit_cost (b : ℕ) (q : ℚ) (count denominator : ℕ) :
    CompetitorRawFieldEmit.listCost (scalarFields b q count denominator) fields=40*b+56 := by
  simp [CompetitorRawFieldEmit.listCost,scalarFields,fields,width]
  omega

theorem record_run (b : ℕ) (q : ℚ) (count denominator : ℕ) :
    ∃ r,run machine (budget b) (input b q count denominator)=some r ∧ r.steps≤budget b ∧
      r.final.tapes 28=CompetitorMonomialStream.recordWord b q count denominator ∧
      r.final.heads=Function.update (fun _ => 0) 28
        (CompetitorMonomialStream.recordWord b q count denominator).length ∧
      r.final.tapes 0=List.replicate b true ∧
      r.final.tapes 27=frame (binary b count) := by
  obtain ⟨p,hp,p0,p20,p22⟩ := CompetitorCountRecordPrepare.prepare_run b
  have hprep := bounded_focus prepareSlots prepare_injective _ _ _ hp (input b q count denominator)
    (by intro i; fin_cases i <;> rfl)
  let middle := install prepareSlots (input b q count denominator) p
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := hprep
  have fresh (i : Fin 29) (hi : 23 ≤ i.val) : middle i=input b q count denominator i := by
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  have hf : ∀ j∈fields,middle j=frame (scalarFields b q count denominator j) := by
    intro j hj
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl
    · exact fresh _ (by decide)
    · exact fresh _ (by decide)
    · exact fresh _ (by decide)
    · exact (install_slot prepareSlots prepare_injective _ _ 20).trans p20
    · exact fresh _ (by decide)
    · exact fresh _ (by decide)
  have hc : ∀ j∈fields,2*(scalarFields b q count denominator j).length+1≤2*width b+1 := by
    intro j hj
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [scalarFields,width] <;> omega
  have counter : middle 22=List.replicate (2*width b+1) false :=
    (install_slot prepareSlots prepare_injective _ _ 22).trans p22
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorRawFieldEmit.list_run (28 : Fin 29) 22 fields
    (scalarFields b q count denominator) (by decide) (by decide) (by decide)
    [] (2*width b+1) (fun _ => 0) middle (by intros; rfl) rfl rfl hf (fresh _ (by decide)) counter hc
  rw [emit_cost] at hlast hls
  have he : Composition.restart first.final emit.start=
      RecoveryCalls.restarted emit (fun _ => 0) middle := by
    apply configuration_ext
    · rfl
    · exact funext hfh
    · exact hft
  have hl' : runFrom emit (40*b+56) (Composition.restart first.final emit.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join prepare emit _ _ _ first last hfirst hl'
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b
    unfold budget
    omega
  · change last.final.tapes 28=_
    rw [hlt,Function.update_self,List.nil_append,stream_eq]
  · change last.final.heads=_
    simpa only [List.nil_append,stream_eq] using hlh
  · change last.final.tapes 0=_
    rw [hlt,Function.update_of_ne (by decide)]
    exact (install_slot prepareSlots prepare_injective _ _ 0).trans p0
  · change last.final.tapes 27=_
    rw [hlt,Function.update_of_ne (by decide)]
    exact fresh _ (by decide)

end NearCubicWires.RepairOrdinary.CompetitorCountRecordAppend
