import Proof.PCP.PCPPNativeCounterNodesLayout

/-! Exact physical counter-to-node-emitter handoff. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCounterNodes
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dock_input {s R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (a : ExecutionReceipt 75 s)
    (af : ∀ j,a.final.heads (PCPPNativeColdCounters.ports j)=0 ∧
      a.final.tapes (PCPPNativeColdCounters.ports j)=PCPPNativeMetadataMass.values oracle p Q j)
    (i : Fin 363) :
    let lifted := TapeEmbedding.receipt (fun _ : Fin 363=>0) (fun _=>[]) a
    lifted.final.heads (slots i)=0 ∧
    lifted.final.tapes (slots i)=nodeInput (PCPPNative.descriptor oracle) (PCPPNativeMetadataMass.queryBytes p R Q)
      (DedupBytes.fields p) R Q oracle.size (Codec.clauses p).length
      (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length i := by
  intro lifted
  by_cases h0 : i=0
  · subst i; exact af 3
  by_cases h1 : i=1
  · subst i; exact af 1
  by_cases h2 : i=2
  · subst i; exact af 4
  by_cases h18 : i=18
  · subst i; exact af 2
  by_cases h19 : i=19
  · subst i; exact af 6
  by_cases h20 : i=20
  · subst i; exact af 8
  by_cases h95 : i=95
  · subst i; exact af 0
  by_cases h96 : i=96
  · subst i; exact af 5
  by_cases h291 : i=291
  · subst i; exact af 7
  simp [lifted,slots,nodeInput,h0,h1,h2,h18,h19,h20,h95,h96,h291]

end NearCubicWires.RepairOrdinary.PCPPNativeCounterNodes
