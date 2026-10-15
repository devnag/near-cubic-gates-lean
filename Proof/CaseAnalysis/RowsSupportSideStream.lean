import Proof.CaseAnalysis.RowsGateBankPorts
import Proof.CaseAnalysis.RowsCircuitBottomErase
import Proof.MachineModel.Runs

namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportSideStream
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsGatePairHeads CloseoutRowsGateSupport ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bitmap_capacity {q : ℕ} (compressed : Bool) (cap : ℕ) (bits : List Bool)
    (g : SupportedNormalizedGate q)
    (hg : decodeSupportedNormalizedGate q (value bits) = some g)
    (fuel : ℕ) (out : Fin 1049 → List Bool)
    (hr : ReadyAt (CloseoutRowsGateMeasured.machine compressed) fuel
      CloseoutRowsGateMeasured.heads (CloseoutRowsGateBank.input cap q bits) out)
    (hc : (out 994).length ≤ cap) :
    out 994 = ZeroPadding.pad cap (frame (gateMembers g.support)) ∧ 2*q+1 ≤ cap := by
  have hb := CloseoutRowsGateBank.bitmap_retained compressed cap bits g hg fuel out hr
  refine ⟨hb, ?_⟩
  rw [hb, ZeroPadding.pad_length, frame_length] at hc
  simp only [gateMembers, List.length_ofFn] at hc
  omega

def slots : Fin 3 → Fin 1060 := ![994,1059,1057]
theorem slots_injective : Function.Injective slots := by decide

theorem append_run {q : ℕ} (support : Finset (Fin q)) (cap : ℕ) (out : List Bool)
    (hc : 2*q+1 ≤ cap) :
    Step CompetitorFrameAppend.machine (4*q+3)
      ![0,out.length,0]
      ![ZeroPadding.pad cap (frame (gateMembers support)),out,List.replicate cap false]
      ![0,(out++frame (gateMembers support)).length,0]
      ![ZeroPadding.pad cap (frame (gateMembers support)),out++frame (gateMembers support),
        List.replicate cap false] := by
  have hlen : (gateMembers support).length = q := List.length_ofFn
  obtain ⟨r,hr,hf,_⟩ := CloseoutRowsCircuitAppend.frame_run cap (gateMembers support) out
    (by simpa only [hlen] using hc)
  rw [hlen] at hr
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem erase_avoids (i : Fin 1050) :
    (CloseoutRowsCircuitBottom.eraseSlots i).castAdd 1 ≠ (1059 : Fin 1060) := by
  intro he
  have hv := congrArg Fin.val he
  have hi := (CloseoutRowsCircuitBottom.eraseSlots i).isLt
  change (CloseoutRowsCircuitBottom.eraseSlots i).val = 1059 at hv
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportSideStream
