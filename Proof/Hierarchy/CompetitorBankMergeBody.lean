import Proof.Hierarchy.CompetitorBankMergeFields

/-! One original row-major cell merges its positive and negative fields in
order. Each field reuses local scratch, while both raw-bank cursors and the
global output cursor stream continuously. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneStream (Cell oldWord oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fieldTail := Composition.machine fieldsProgram kernelProgram
noncomputable def fieldProgram := Composition.machine clearProgram fieldTail
def fieldBudget (w : ℕ) := 2*capacity w+16*w+21

theorem field_run (w a b : ℕ) (preA suffixA preB suffixB out : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w (preA++binary w a++suffixA) (preB++binary w b++suffixB) out ambient)
    (hfit : a+b<2^w) :
    ∃ r,runFrom fieldProgram (fieldBudget w)
      (cfg fieldProgram.start preA.length preB.length out.length ambient)=some r ∧
      r.steps≤fieldBudget w ∧ r.final.heads=heads (preA.length+w) (preB.length+w) (out++binary w (a+b)).length ∧
      Store w (preA++binary w a++suffixA) (preB++binary w b++suffixB) (out++binary w (a+b)) r.final.tapes := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run w preA.length preB.length out.length _ _ out ambient h
  obtain ⟨fields,hfields,hfieldsH,hfieldsT,hfieldsS⟩ := fields_run w a b preA suffixA preB suffixB out ambient h hfit
  obtain ⟨last,hlast,hls,hlh,hlt⟩ := kernel_run w a b (preA.length+w) (preB.length+w) _ _ out
    (loaded w a b ambient) (loaded_stored w a b _ _ out ambient h) hfit (loaded_input w a b ambient)
  have heLast : Composition.restart fields.final kernelProgram.start=
      cfg kernelProgram.start (preA.length+w) (preB.length+w) out.length (loaded w a b ambient) := by
    apply configuration_ext
    · rfl
    · exact hfieldsH
    · exact hfieldsT
  have hl' : runFrom kernelProgram (8*w+8) (Composition.restart fields.final kernelProgram.start)=some last := by
    rw [heLast]
    exact hlast
  have htail := Composition.run_join fieldsProgram kernelProgram _ _ _ fields last hfields hl'
  have heFields : Composition.restart first.final fieldTail.start=
      Composition.leftConfig _ (cfg fieldsProgram.start preA.length preB.length out.length (clean w ambient)) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have ht' : runFrom fieldTail ((8*w+7)+1+(8*w+8)) (Composition.restart first.final fieldTail.start)=
      some (Composition.joinedReceipt fields last) := by rw [heFields]; exact htail
  have hall := Composition.run_join clearProgram fieldTail _ _ _ first (Composition.joinedReceipt fields last) hfirst ht'
  have htime : (2*capacity w+4)+1+((8*w+7)+1+(8*w+8))=fieldBudget w := by unfold fieldBudget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt fields last),hall,?_,hlh,hlt⟩
  change first.steps+1+(fields.steps+1+last.steps)≤fieldBudget w
  omega

def merged (a b : Cell) : Cell := ⟨0,a.positive+b.positive,a.negative+b.negative⟩
def Valid (w : ℕ) (a b : Cell) : Prop := a.positive+b.positive<2^w ∧ a.negative+b.negative<2^w
noncomputable def bodyProgram := Composition.machine fieldProgram fieldProgram
def bodyBudget (w : ℕ) := 2*fieldBudget w+1

theorem body_run (w : ℕ) (a b : Cell) (preA suffixA preB suffixB out : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w (preA++oldWord w a++suffixA) (preB++oldWord w b++suffixB) out ambient)
    (hv : Valid w a b) :
    ∃ r,runFrom bodyProgram (bodyBudget w)
      (cfg bodyProgram.start preA.length preB.length out.length ambient)=some r ∧
      r.steps≤bodyBudget w ∧ r.final.heads=heads (preA.length+2*w) (preB.length+2*w) (out++oldWord w (merged a b)).length ∧
      Store w (preA++oldWord w a++suffixA) (preB++oldWord w b++suffixB) (out++oldWord w (merged a b)) r.final.tapes := by
  obtain ⟨first,hfirst,hfs,hfh,hft⟩ := field_run w a.positive b.positive preA (binary w a.negative++suffixA)
    preB (binary w b.negative++suffixB) out ambient
    (by simpa [oldWord,CompetitorPlane.pairWord,List.append_assoc] using h) hv.1
  obtain ⟨last,hlast,hls,hlh,hlt⟩ := field_run w a.negative b.negative (preA++binary w a.positive) suffixA
    (preB++binary w b.positive) suffixB (out++binary w (a.positive+b.positive)) first.final.tapes
    (by simpa only [List.append_assoc] using hft) hv.2
  have he : Composition.restart first.final fieldProgram.start=
      cfg fieldProgram.start (preA++binary w a.positive).length (preB++binary w b.positive).length
        (out++binary w (a.positive+b.positive)).length first.final.tapes := by
    apply configuration_ext
    · rfl
    · simpa only [cfg,Composition.restart,List.length_append,binary_length] using hfh
    · rfl
  have hl' : runFrom fieldProgram (fieldBudget w) (Composition.restart first.final fieldProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join fieldProgram fieldProgram _ _ _ first last hfirst hl'
  have htime : fieldBudget w+1+fieldBudget w=bodyBudget w := by unfold bodyBudget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤bodyBudget w
    omega
  · change last.final.heads=_
    simpa [oldWord,CompetitorPlane.pairWord,merged,List.append_assoc,List.length_append,Nat.add_assoc,two_mul] using hlh
  · change Store w _ _ _ last.final.tapes
    simpa [oldWord,CompetitorPlane.pairWord,merged,List.append_assoc] using hlt

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
