import Proof.CaseAnalysis.RowsGateBank

/-! The original support bitmap survives the measured gate's SAME trace.
The threshold circuit uses this port to select original bottom requests;
no second parser or bitmap copier is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateMeasured
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads CanonicalWitnessCodec SupplierPipeline
open RadixSemantics CloseoutRowsGateSupport RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem metadata_read : NoWrite CloseoutRowsGateMetadata.machine 3 := by
  apply composition
  · apply composition
    · exact focus CloseoutRowsGateMetadata.weightSlots CloseoutRowsGateMetadata.weight_injective _ 3
        (rewind (AppendOutputLength.record (preparedMachine false) 2) (3 : Fin 7)
          (CloseoutRowsGateNativeCount.record_count _ 2 3
            (CloseoutRowsGateNativeRetained.prepared_read false 3 (Or.inr rfl))))
    · exact unselected CloseoutRowsGateMetadata.naturalSlots _ 3 (by decide)
  · apply focus CloseoutRowsGateMetadata.supportSlots CloseoutRowsGateMetadata.support_injective _ 0
    apply rewind CloseoutRowsSupportCount.machine (0 : Fin 2)
    intro q bits a ha
    simp only [CloseoutRowsSupportCount.machine] at ha
    split_ifs at ha <;> cases ha <;> rfl

theorem bitmap_retained {core : ℕ} (compressed : Bool) (bits : List Bool)
    (g : SupportedNormalizedGate core) (hg : decodeSupportedNormalizedGate core (value bits)=some g)
    (fuel : ℕ) (out : Fin 1049→List Bool)
    (run : ReadyAt (machine compressed) fuel heads (input core bits) out) :
    out 994=frame (gateMembers g.support) := by
  obtain ⟨bank,hr,_hdom,hflag,_hnative⟩ := CloseoutRowsGateGuard.guard_run compressed core bits
  obtain ⟨other,hs,_hw,_ht,_hc⟩ := second_run compressed g bits hg bank hr
  have member := (CloseoutRowsGateGuard.guard_ports compressed g bits hg _ bank hr).2.1
  have secondRead : NoWrite second 994 := focus slots slots_injective _ 3 metadata_read
  have keep : (install slots (extend bank) other) 994=bank 994 := by
    obtain ⟨r,rr,rt,_rh,_rs⟩ := hs
    rw [←rt]
    exact run_tape second 994 secondRead _ _ r rr
  have joined := CloseoutRowsGatePairHeads.joined (first compressed) second
    (fun scanned=>scanned (old 1037)) _ _ heads _ _ _ (first_run compressed core bits bank hr) hs
    (hflag.mpr (by rw [hg];rfl))
  obtain ⟨a,ha,aT,_ah,_as⟩ := run
  obtain ⟨b,hb,bt,_bh,_bs⟩ := joined
  have he := CloseoutRowsGateGuard.receipt_unique _ _ _ _ a b ha hb
  subst b
  rw [←aT,bt]
  exact keep.trans member

end NearCubicWires.RepairOrdinary.CloseoutRowsGateMeasured
