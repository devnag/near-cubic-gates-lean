import Proof.Circuits.DecompositionCachedChildPosition
import Proof.Assembly.AppendOutputLength

/-! Measure the actual native decomposition cache with its existing counted
parser. The source and measured unary mass return to head zero, while the
already decoded arity and child-count templates remain at their sentinels. -/
namespace NearCubicWires.RepairOrdinary.RowCacheMass
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.ProjectionNormalization DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_forward (keep : Bool) : CursorRestore.NoLeft (PCPPQueryField.machine keep) 0 := by
  intro q bs a ha
  fin_cases q <;> simp [PCPPQueryField.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp)
    | (cases ha; simp)

theorem signed_forward : CursorRestore.NoLeft Fields.machine 0 := by
  apply CursorRestore.composition_forward
  · intro q bs a ha
    simp only [Fields.sign,Option.some.injEq] at ha
    cases ha
    simp
  · exact field_forward true

theorem source_forward : CursorRestore.NoLeft DecompositionCachedChild.machine 0 := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.embedded_forward 2 _ 0 (field_forward false)
  · refine CursorRestore.repeat_forward Records.child (fun _ _=>true) (0 : Fin 4) ?_
    apply CursorRestore.composition_forward
    · exact CursorRestore.repeat_forward Fields.machine (fun _ _=>true) 0 signed_forward
    · exact EquationRowCuts.embedded_forward 1 _ 0 signed_forward

noncomputable def record := AppendOutputLength.record DecompositionCachedChild.machine 0
def selected (i : Fin 6) : Bool := decide (i=0 ∨ i=5)
noncomputable def machine := MaskedReset.machine record selected
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) :=
  Rewind.recording (Rewind.recording (DecompositionCachedChild.entry gs gs.length) 0) 0
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) :=
  2*DecompositionCachedChild.budget gs gs.length+2

theorem mass_run {n : ℕ} (gs : List (ExactThresholdGate n)) :
    ∃ r,runFrom machine (budget gs) (input gs)=some r ∧
      r.final.tapes 0=exactListWord gs ∧ r.final.heads 0=0 ∧
      r.final.tapes 5=List.replicate (exactListWord gs).length true ∧ r.final.heads 5=0 ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧ r.final.heads 3=1 ∧
      r.final.tapes 4=UnaryTemplate.tape gs.length ∧ r.final.heads 4=1 ∧
      r.steps=budget gs := by
  obtain ⟨base,hb,bt,bh,bn,bnh,bm,bmh,bs⟩ :=
    DecompositionCachedChild.position_run gs gs.length (by rfl)
  have bend : base.final.heads 0=(exactListWord gs).length := by
    simpa [exactListWord,List.length_append] using bh
  obtain ⟨hp,hh⟩ := prefix_of_run DecompositionCachedChild.machine _ _ base hb
  obtain ⟨delta,hd,he,ht⟩ := AppendOutputLength.recording_timed hp 0 source_forward 0
  have he' : delta=(exactListWord gs).length := by
    simpa [DecompositionCachedChild.entry,bend] using he.symm
  simp only [Nat.zero_add,he'] at ht
  obtain ⟨counted,hc,cf,cs⟩ := ht.run (by
    simp [AppendOutputLength.record,Rewind.recording,Rewind.config,hh])
  have hheads : ∀ i,selected i=true → counted.final.heads i≤counted.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run record _ _ counted hc).1 i
    have hz : (Rewind.recording (DecompositionCachedChild.entry gs gs.length) 0).heads i=0 := by
      have hi' : i=0 ∨ i=5 := by simpa only [selected,decide_eq_true_eq] using hi
      rcases hi' with rfl | rfl <;> rfl
    simpa only [hz,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.reset_run record selected _ _ counted hc hheads
  rw [cs,bs] at hr rs
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_,?_,rs⟩
  all_goals rw [rf,cf]
  · simpa [SelectiveReset.finished,Rewind.recording,Rewind.config,Fin.addCases] using bt
  · simp [SelectiveReset.finished,Rewind.recording,Rewind.config,selected,Fin.addCases]
  · simp [SelectiveReset.finished,Rewind.recording,Rewind.config,Fin.addCases]
  · simp [SelectiveReset.finished,Rewind.recording,Rewind.config,selected,Fin.addCases]
  · simpa [SelectiveReset.finished,Rewind.recording,Rewind.config,Fin.addCases] using bn
  · simpa [SelectiveReset.finished,Rewind.recording,Rewind.config,selected,Fin.addCases] using bnh
  · simpa [SelectiveReset.finished,Rewind.recording,Rewind.config,Fin.addCases] using bm
  · simpa [SelectiveReset.finished,Rewind.recording,Rewind.config,selected,Fin.addCases] using bmh

end NearCubicWires.RepairOrdinary.RowCacheMass
