import Proof.Assembly.Parent
import Proof.MachineModel.ClosureCompactFamily

/-! The actual normalized packets through the fixed cold header writer.
Every cache, dimension word and raw packet byte is an entry requirement.
The theorem pays the complete metadata and family writer budget, specifies
all final heads/tapes, and identifies the actual Datum header port. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace ColdHeaderWriter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open FixedLivePackets
noncomputable section

variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
  (facts : Packets.PacketFacts a F g r)

abbrev machine := CompactColdFamily.machine

abbrev radix := Packets.radix a F g layout

noncomputable def input (out pre tail : List Bool) : Fin 440 → List Bool :=
  letI := radix a F g layout
  CompactNativeInitialize.input (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r).length
    (pre++(Packets.packets a F g r).flatMap P1CompactNativeFamily.rawWord++tail) out

noncomputable def finalHeads (out pre tail : List Bool) : Fin 440 → Nat :=
  letI := radix a F g layout
  CompactColdFamily.finalHeads (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r) out pre tail

noncomputable def finalTapes (out pre tail : List Bool) : Fin 440 → List Bool :=
  letI := radix a F g layout
  CompactColdFamily.finalTapes (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r) out pre tail

noncomputable def budget : Nat :=
  letI := radix a F g layout
  CompactColdFamily.budget (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r)

theorem stream_eq :
    letI := radix a F g layout
    CloseoutRowsEstimator.Header.stream (Packets.rowInput a F g layout r hr facts) =
      (Packets.packets a F g r).flatMap
        (P1CompactNativeFamily.emit (Packets.pool a F g) ((Packets.live F).card+1) layout.w) := by
  letI := radix a F g layout
  simp only [Packets.rowInput,P1CompactInput.input,CloseoutRowsEstimator.Header.stream,
    CloseoutRows.commonInput,CloseoutRows.commonWidth]
  simp only [NativeRowInput.bank,List.flatMap_map,List.flatMap_assoc]
  rfl

theorem run (out pre tail : List Bool) :
    Step machine (budget a F g layout r) (CompactColdFamily.ambientH out pre)
      (input a F g layout r out pre tail)
      (finalHeads a F g layout r out pre tail) (finalTapes a F g layout r out pre tail) ∧
    finalTapes a F g layout r out pre tail 180 =
      out++CloseoutRowsEstimator.Header.stream (Packets.datum a F g layout r hr facts).row := by
  letI := radix a F g layout
  letI := Packets.bankDegree a F g layout r hr facts
  constructor
  · have hmask : ∀ ms∈Packets.packets a F g r,
        P1MaskDegree (Packets.pool a F g) (rawRows ms) := by
      intro ms hm
      apply P1BankDegree.bound (bank:=NativeRowInput.bank (Packets.packets a F g r))
      exact List.mem_map.mpr ⟨ms,hm,rfl⟩
    exact CompactColdFamily.family_run (Packets.pool a F g) ((Packets.live F).card+1)
      layout.w (Packets.packets a F g r) out pre tail hmask
      (Packets.width a F g layout r hr facts) (by omega)
  · change CompactColdFamily.finalTapes (Packets.pool a F g) ((Packets.live F).card+1)
      layout.w (Packets.packets a F g r) out pre tail 180 = _
    rw [CompactColdFamily.output_word]
    exact congrArg (fun x => out++x) (stream_eq a F g layout r hr facts).symm

end
end ColdHeaderWriter
