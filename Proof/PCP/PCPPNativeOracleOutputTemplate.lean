import Proof.PCP.PCPPNativeOracleOutput
import Proof.MachineModel.OrdinaryMatrixRawDimension

/-! The same native footer scan accepts the physical size template from
the original raw-size decoder. Only its inert trailing false is present. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleOutput
open LocalBitMultitape SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (s : ℕ) (i : Fin 18) := if i=3 then s+2 else 0
def templateInput (bits : List Bool) (s : ℕ) (i : Fin 18) :=
  if i=0 then bits else if i=3 then UnaryTemplate.tape s else []
noncomputable def templateEntry {R : ℕ} (oracle : BooleanCircuit R) :=
  (⟨machine.start,heads,templateInput (PCPPNative.descriptor oracle) oracle.size⟩ : Configuration 18 _)

theorem padded_entry {R : ℕ} (oracle : BooleanCircuit R) :
    ZeroPadding.config (padding oracle.size) (entry oracle)=templateEntry oracle := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i=3
    · subst i
      simp [ZeroPadding.config,padding,entry,templateEntry,input,templateInput,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
    · simp only [ZeroPadding.config,padding,hi,ite_false,ZeroPadding.pad_zero,entry,templateEntry,input,templateInput]

theorem template_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ result,
    runFrom machine (budget oracle) (templateEntry oracle)=some result ∧ result.steps ≤ budget oracle ∧
    result.final.tapes 0=PCPPNative.descriptor oracle ∧
    result.final.tapes 14=List.replicate oracle.output.val true ∧
    result.final.tapes 15=List.replicate oracle.output.val true := by
  obtain ⟨base,hb,bs,b0,_,b14,_,b15,_,_,_⟩ := output_run oracle
  obtain ⟨result,hr,hf,hs,_⟩ := ZeroPadding.run_config machine (padding oracle.size) _ _ base hb
  rw [padded_entry] at hr
  refine ⟨result,hr,hs.trans_le bs,?_,?_,?_⟩
  · simpa only [hf,ZeroPadding.config,padding,show (0 : Fin 18)≠3 by decide,ite_false,ZeroPadding.pad_zero] using b0
  · simpa only [hf,ZeroPadding.config,padding,show (14 : Fin 18)≠3 by decide,ite_false,ZeroPadding.pad_zero] using b14
  · simpa only [hf,ZeroPadding.config,padding,show (15 : Fin 18)≠3 by decide,ite_false,ZeroPadding.pad_zero] using b15

end NearCubicWires.RepairOrdinary.PCPPNativeOracleOutput
