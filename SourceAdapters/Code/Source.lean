import SourceAdapters.Code.EncoderMachine
import SourceAdapters.Code.Decoder
import SourceAdapters.Code.TM2Dock
import SourceAdapters.Machine.OrdinaryToTM2
import SourceAdapters.Machine.CappedWordProof

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the complete sparse-support linear code
interface from CW19 Lemma 26. Lemma 27's three-block construction, finite patch,
strict radii, total decoder, target serializations and both machines are proved
in this adapter. Both shared machine joins, X1 and X8, are discharged by
proved ordinary-machine constructions. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Code NearCubicGates.PublishedSources.PCPP

/-- The exact complete consumer from the literal published source.
Both ordinary-machine joins are discharged by their proved implementations. -/
theorem efficientLinearCode_of_lemma26 (hsource : Lemma26) : EfficientLinearCodeLiteral := by
  have hX8 := NearCubicGates.Adapters.Machine.Capped.cappedWordRun
  obtain ⟨F, distance, fraction, onset, rate, hd, hf, hlinear, hrate, hmin, ⟨A⟩, ⟨D⟩⟩ := hsource
  obtain ⟨KE, eE, WE⟩ := EncoderMachine.wordFunction_of_source hX8 F D hlinear A
  obtain ⟨KD, eD, WD⟩ := Decoder.wordFunction_of_source hX8 F D A distance hd hmin
  exact efficientLinearCode_of_ordinary NearCubicGates.Adapters.Machine.ordinaryToTM2PolyTime
    F onset rate distance (fraction * distance) D hlinear hd (mul_pos hf hd) hmin hrate
    (fun p => KE * ((messageWord p).length + 1) ^ eE)
    (fun p => KD * ((codewordWord (patchedFamily F D) p).length + 1) ^ eD)
    WE ⟨KE, eE, fun _ => le_rfl⟩ WD ⟨KD, eD, fun _ => le_rfl⟩

end NearCubicGates.Adapters.Code
