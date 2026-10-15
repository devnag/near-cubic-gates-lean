import Proof.Hierarchy.CompetitorSameBucketGroupArithmeticFields
import Proof.Hierarchy.CompetitorRawScalarPaddedField

/-! Flush one natural accumulator as exactly W raw bits, then reset it by
copying the physically retained zero field. The global append head stays
live throughout; both local scalar and copy logs are reset for reuse. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupFlush
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorSameBucketGroupArithmetic
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 5 → ℕ := ![0,out.length,0,0,0]
def data (cap w a : ℕ) (out : List Bool) : Fin 5 → List Bool :=
  ![scalar cap w a,out,zeros cap,scalar cap w 0,zeros cap]
def copySlots : Fin 4 → Fin 5 := ![3,0,4,2]
noncomputable def emit := CompetitorRawScalarPaddedField.program (0 : Fin 5) 1 2
noncomputable def copy := RecoveryFocus.machine copySlots copyMachine
noncomputable def machine := Composition.machine emit copy

theorem emit_run (cap w a : ℕ) (out : List Bool) (hc : 2*w+1≤cap) :
    ∃ r,runFrom emit (4*w+3) (RecoveryCalls.restarted emit (heads out) (data cap w a out))=some r ∧
      r.final.heads=heads (out++binary w a) ∧ r.final.tapes=data cap w a (out++binary w a) ∧
      r.steps=4*w+3 := by
  obtain ⟨r,hr,hh,ht,hs⟩ := CompetitorRawScalarPaddedField.field_run (0 : Fin 5) 1 2
    (by decide) (by decide) (by decide) (binary w a) out cap (heads out) (data cap w a out)
    rfl rfl rfl rfl rfl rfl (by simpa using hc)
  simp only [binary_length] at hr hs
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [hh]
    funext i; fin_cases i <;> rfl
  · rw [ht]
    funext i; fin_cases i <;> rfl

theorem copy_run (cap w a : ℕ) (out : List Bool) (hc : 4*w+3≤cap) :
    ∃ r,runFrom copy (8*w+8) (RecoveryCalls.restarted copy (heads out) (data cap w a out))=some r ∧
      r.final.heads=heads out ∧ r.final.tapes=data cap w 0 out ∧ r.steps=8*w+8 := by
  have ready := field_copy_ready cap (binary w 0) (frame (binary w a)) (by simp) (by simpa using hc)
  simp only [binary_length] at ready
  obtain ⟨r,hr,hh,ht,hs⟩ := HierarchyBinary.focused_run copySlots (by decide) copyMachine _ _ ready
    (heads out) (data cap w a out) (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨r,hr,hh,?_,hs⟩
  rw [ht]
  funext i
  fin_cases i
  all_goals first
    | exact install_slot copySlots (by decide) _ _ 0
    | exact install_slot copySlots (by decide) _ _ 1
    | exact install_slot copySlots (by decide) _ _ 2
    | exact install_slot copySlots (by decide) _ _ 3
    | exact install_other copySlots _ _ _ (by decide)

theorem flush_run (cap w a : ℕ) (out : List Bool) (hc : 4*w+3≤cap) :
    ∃ r,runFrom machine (12*w+12)
      (RecoveryCalls.restarted machine (heads out) (data cap w a out))=some r ∧
      r.final.heads=heads (out++binary w a) ∧ r.final.tapes=data cap w 0 (out++binary w a) ∧
      r.steps=12*w+12 := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := emit_run cap w a out (by omega)
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := copy_run cap w a (out++binary w a) hc
  have hdock : Composition.restart first.final copy.start=
      RecoveryCalls.restarted copy (heads (out++binary w a)) (data cap w a (out++binary w a)) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom copy (8*w+8) (Composition.restart first.final copy.start)=some last := by
    rw [hdock]
    exact hlast
  have h := Composition.run_join emit copy _ _ _ first last hfirst hl'
  have ht : (4*w+3)+1+(8*w+8)=12*w+12 := by omega
  rw [ht] at h
  refine ⟨Composition.joinedReceipt first last,h,hlh,hlt,?_⟩
  change first.steps+1+last.steps=_
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupFlush
