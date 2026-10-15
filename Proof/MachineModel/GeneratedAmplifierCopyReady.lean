import Proof.MachineModel.GeneratedAmplifierCopy
import Proof.MachineModel.OrdinaryMaskedReset

/-! A cold whole-input copy retains the raw append cursor while paying the
original source's reset. A second ordinary copy can then serve the header. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Copy
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool := decide (i=0)
def sourceReset := MaskedReset.machine machine selected
def endCopy (bits : List Bool) : Configuration 3 5 :=
  ⟨4,![0,bits.length,0],![frame bits,bits,List.replicate (2*bits.length+1) false]⟩

theorem source_reset_run (bits : List Bool) :
    ∃ r,run sourceReset (4*bits.length+4) ![frame bits,[],[]]=some r ∧
      r.final=endCopy bits ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,hf,hs⟩ := copy_run [] bits [] []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb hf
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=0 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    rw [hf,hs]
    rfl
  obtain ⟨r,hr,hrf,hrs,_⟩ := MaskedReset.reset_run machine selected _ _ base hb hh
  have ht : 2*base.steps+2=4*bits.length+4 := by rw [hs]; omega
  rw [ht] at hr hrs
  have he : Rewind.recording (cfg 0 (frame bits) 0 []) 0=
      initialConfiguration sourceReset ![frame bits,[],[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at hr
  refine ⟨r,hr,?_,hrs⟩
  rw [hrf,hf,hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,selected,cfg,endCopy,Fin.addCases]
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,endCopy,Fin.addCases]

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Copy
