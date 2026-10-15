import Proof.PCP.PCPPRequestWord
import Proof.Assembly.AppendOutputFrame
import Proof.Supplier.EquationRowForward

/-! Paid framing of the exact PCPP request suffix assembler. Its real output
cursor supplies the length; no guessed code width or supplied driver occurs. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestWordFramed
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem append_forward : CursorRestore.NoLeft CompetitorRawScalarEmit.machine 1 := by
  intro q bs a ha
  fin_cases q <;> simp [CompetitorRawScalarEmit.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp [CompetitorRawScalarEmit.action])
    | (cases ha; simp [CompetitorRawScalarEmit.action])

theorem output_forward : CursorRestore.NoLeft PCPPRequestWord.machine 3 :=
  CursorRestore.composition_forward _ _ 3
    (CursorRestore.focus_forward PCPPRequestWord.headerSlots PCPPRequestWord.header_injective
      (PCPPQueryField.machine true) 2 EquationRowRaw.header_field_forward)
    (CursorRestore.focus_forward PCPPRequestWord.codeSlots PCPPRequestWord.code_injective
      CompetitorRawScalarEmit.machine 1 append_forward)

noncomputable def machine := AppendOutputFrame.machine PCPPRequestWord.machine 3
def input (n : ℕ) (tail bits suffix : List Bool) : Fin 9 → List Bool :=
  AppendOutputFrame.input (PCPPRequestWord.input n tail bits suffix)
def budget (n : ℕ) (bits : List Bool) := 6*PCPPRequestWord.budget n bits+7

theorem framed_run (n : ℕ) (tail bits suffix : List Bool) :
    ∃ r,run machine (budget n bits) (input n tail bits suffix)=some r ∧
      r.final.tapes 7=frame (RepairRepresentation.natWord n++bits) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget n bits := by
  obtain ⟨base,hb,bt,bh,bs⟩ := PCPPRequestWord.word_run n tail bits suffix
  have hlen : (RepairRepresentation.natWord n++bits).length ≤ base.steps := by
    have h := SelectiveReset.prefix_head (prefix_of_run PCPPRequestWord.machine _ _ base hb).1 3
    rw [bh] at h
    simpa only [initialConfiguration,Nat.zero_add] using h
  obtain ⟨r,hr,rt,rh,rs⟩ := AppendOutputFrame.frame_run PCPPRequestWord.machine 3 output_forward
    _ _ base hb (RepairRepresentation.natWord n++bits) bt bh
  have le : 2*base.steps+4*(RepairRepresentation.natWord n++bits).length+7 ≤ budget n bits := by
    unfold budget
    omega
  have more := run_moreFuel machine _
    (budget n bits-(2*base.steps+4*(RepairRepresentation.natWord n++bits).length+7)) _ r hr
  rw [Nat.add_sub_of_le le] at more
  exact ⟨r,more,rt,rh,rs.trans le⟩

theorem ready (n : ℕ) (tail bits suffix : List Bool) :
    ∃ out,ClockJoin.ReadyRun machine (budget n bits) (input n tail bits suffix) out ∧
      out 7=frame (RepairRepresentation.natWord n++bits) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := framed_run n tail bits suffix
  exact ⟨r.final.tapes,⟨r,hr,rfl,rh,rs⟩,rt⟩

end NearCubicWires.RepairOrdinary.PCPPRequestWordFramed
