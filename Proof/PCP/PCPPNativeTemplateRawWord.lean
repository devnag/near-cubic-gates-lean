import Proof.PCP.PCPPNativeTemplateRaw
import Proof.PCP.PCPPNativeTag

/-! The same physical adapters accept the shorter Compare.word returned
by binary unpair/projection decoding. Finite zero padding transports the
trace without granting a free trailing cell or assuming a different codec. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeTemplateRaw
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def wordEntry (n : ℕ) :=
  (⟨machine.start,heads,MatrixTemplateCopy.wordInput n⟩ : Configuration 5 _)

theorem padded_entry (n : ℕ) :
    ZeroPadding.config (MatrixTemplateCopy.wordCapacity n) (wordEntry n)=entry n := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,MatrixTemplateCopy.wordCapacity,wordEntry,entry,
        MatrixTemplateCopy.wordInput,MatrixTemplateCopy.resetInput,MatrixTemplateCopy.input,
        Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem word_run (n : ℕ) :
    ∃ r,runFrom machine (4*n+16) (wordEntry n)=some r ∧ r.steps=4*n+16 ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧ r.final.heads=heads := by
  obtain ⟨base,hb,bs,_,b1,b2,b3,bh⟩ := template_run n
  rw [←padded_entry] at hb
  obtain ⟨r,hr,hf,rs,_⟩ := ZeroPadding.run_unpad machine (MatrixTemplateCopy.wordCapacity n)
    _ _ base hb
  have ht (i : Fin 5) := congrArg (fun c => c.tapes i) hf
  have hh := congrArg (fun c => c.heads) hf
  refine ⟨r,hr,rs.trans bs,?_,?_,?_,hh.trans bh⟩
  · simpa [ZeroPadding.config,MatrixTemplateCopy.wordCapacity,ZeroPadding.pad,b1] using ht 1
  · simpa [ZeroPadding.config,MatrixTemplateCopy.wordCapacity,ZeroPadding.pad,b2] using ht 2
  · simpa [ZeroPadding.config,MatrixTemplateCopy.wordCapacity,ZeroPadding.pad,b3] using ht 3

def tagWordEntry (tag : Fin 5) : Configuration 1 10 :=
  ⟨0,fun _ => 1,fun _ => CompareMachine.word tag.val⟩

theorem tag_word_run (tag : Fin 5) :
    ∃ r,runFrom PCPPNativeTag.machine (tag.val+1) (tagWordEntry tag)=some r ∧
      r.steps=tag.val+1 ∧ r.final.control.val=tag.val+5 ∧
      (∀ i,r.final.heads i=tag.val+1) := by
  have padded : ZeroPadding.config (fun _ : Fin 1 => tag.val+2) (tagWordEntry tag)=PCPPNativeTag.entry tag := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      simp [ZeroPadding.config,tagWordEntry,PCPPNativeTag.entry,ZeroPadding.pad,
        CompareMachine.word,UnaryTemplate.tape]
  have hb := PCPPNativeTag.tag_run tag
  rw [←padded] at hb
  obtain ⟨r,hr,hf,rs,_⟩ := ZeroPadding.run_unpad PCPPNativeTag.machine
    (fun _ : Fin 1 => tag.val+2) _ _ (PCPPNativeTag.receipt tag) hb
  refine ⟨r,hr,rs,?_,?_⟩
  · exact congrArg (fun c => c.control.val) hf
  · intro i
    exact congrArg (fun c => c.heads i) hf

end NearCubicWires.RepairOrdinary.PCPPNativeTemplateRaw
