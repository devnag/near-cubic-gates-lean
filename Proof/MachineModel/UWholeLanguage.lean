import Proof.MachineModel.UWholeVerifier
import Proof.MachineModel.UEmissionLanguageComplete
import Proof.Foundations.SourceRegistry

/-! Both bounded-language directions of the fixed ordinary U, and the
literal application of the one printed projection-PCP source to this U. -/
namespace NearCubicWires.RepairOrdinary.UWhole
open LocalBitMultitape RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem language_iff (n : ℕ) (x : BitInput n) :
    verifier.language time n x ↔ UEmission.SourceAccepted (List.ofFn x) := by
  change (∃ w : BitInput (time n),verifier.accepts (List.ofFn x) (List.ofFn w)) ↔ _
  simp only [accepts_iff]
  have h := UEmission.bitInput_language_iff (List.ofFn x)
  rw [List.length_ofFn] at h
  exact h

theorem total (n : ℕ) (x : BitInput n) (w : BitInput (time n)) :
    ∃ r,run verifier.machine (time n) (verifier.inputTapes (List.ofFn x) (List.ofFn w))=some r := by
  obtain ⟨r,hr,_,_⟩ := whole_run (List.ofFn x) (List.ofFn w)
  exact ⟨r,by simpa only [List.length_ofFn] using hr⟩

noncomputable def projectionSource (source : ProjectionPCPSource) : ProjectionSourceAlgorithm verifier time :=
  Classical.choice (source verifier time UAggregateClock.input_le_time total)

noncomputable def registeredProjectionSource (sources : EightSources) : ProjectionSourceAlgorithm verifier time :=
  projectionSource sources.pcp.projection

theorem source_call (sources : EightSources) (r : InputRequest) :
    ∃ receipt,run (registeredProjectionSource sources).constructor.program.machine
      ((registeredProjectionSource sources).coefficient *
        (r.1+natBitLength (time r.1)+1)^(registeredProjectionSource sources).degrees.construction)
      ((registeredProjectionSource sources).constructor.program.inputTapes
        (frame (List.ofFn r.2)++frame (time r.1).bits))=some receipt ∧
      receipt.final.tapes (registeredProjectionSource sources).constructor.program.outputTape=
        ((registeredProjectionSource sources).output r).word :=
  projection_source_call (registeredProjectionSource sources) r

end NearCubicWires.RepairOrdinary.UWhole
