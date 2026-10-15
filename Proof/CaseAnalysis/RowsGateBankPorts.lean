import Proof.CaseAnalysis.RowsGateMeasuredPorts

/-! The accepted padded gate trace retains its original support bitmap.
This is a projection of that trace, with no second physical traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateBank
open LocalBitMultitape CloseoutRowsGatePairHeads CanonicalWitnessCodec SupplierPipeline
open RadixSemantics CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bitmap_retained {core : ℕ} (compressed : Bool) (cap : ℕ) (bits : List Bool)
    (g : SupportedNormalizedGate core) (hg : decodeSupportedNormalizedGate core (value bits)=some g)
    (fuel : ℕ) (out : Fin 1049→List Bool)
    (run : ReadyAt (CloseoutRowsGateMeasured.machine compressed) fuel
      CloseoutRowsGateMeasured.heads (input cap core bits) out) :
    out 994=ZeroPadding.pad cap (frame (gateMembers g.support)):=by
  obtain ⟨bank,original,_⟩:=CloseoutRowsGateMeasured.allraw compressed core bits
  have member:=CloseoutRowsGateMeasured.bitmap_retained compressed bits g hg _ bank original
  obtain ⟨base,hbase,bt,_bh,_bs⟩:=original
  obtain ⟨paddedRun,hp,pt,_ps,_⟩:=ZeroPadding.run_config
    (CloseoutRowsGateMeasured.machine compressed) (pads cap) _ _ base hbase
  obtain ⟨actual,ha,actualTapes,_ah,_as⟩:=run
  have he:=CloseoutRowsGateGuard.receipt_unique _ _ _ _ actual paddedRun ha hp
  subst paddedRun
  rw [←actualTapes,pt]
  change ZeroPadding.pad (pads cap 994) (base.final.tapes 994)=_
  rw [bt,member]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsGateBank
