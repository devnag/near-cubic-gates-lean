import Proof.PCP.PCPPNativeResourcesLayout

/-! One paid native resource prefix computes exact counts, combines actual
stream masses, and produces C/F/G together. Every driver is physically
available for the original query/clause/header/tail consumers. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResources
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem measured_other (R Q s M Lq Lc : ℕ) (i : Fin 18)
    (hi : ∀ j,envelopeSlots j≠countSlots i) :
    measured R Q s M Lq Lc (countSlots i)=PCPPNativeCount.data Q s M 7 i := by
  rw [measured,install_other _ _ _ _ hi]
  exact counted_low R Q s M Lq Lc i

theorem resource_run (R Q s M Lq Lc : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget R Q s M Lq Lc) (input R Q s M Lq Lc) out ∧
    out 33=List.replicate (W R Q s M Lq Lc) true ∧
    out 42=List.replicate (PCPPNativeCapacityReady.C (W R Q s M Lq Lc)) true ∧
    out 62=List.replicate (PCPPNativeCapacityReady.F (W R Q s M Lq Lc)) true ∧
    out 84=List.replicate (PCPPNativeCapacityReady.G (W R Q s M Lq Lc)) true ∧
    out 0=List.replicate Q true ∧ out 1=List.replicate s true ∧ out 2=List.replicate M true ∧
    out 18=List.replicate R true ∧ out 19=List.replicate Lq true ∧ out 20=List.replicate Lc true ∧
    out 6=UnaryTemplate.tape (PCPPNativeCount.stride s) ∧
    out 8=List.replicate (PCPPNativeCount.queryEnd Q s) true ∧
    out 14=List.replicate (PCPPNativeCount.outputIndex Q s M) true ∧
    out 16=List.replicate (PCPPNativeCount.nativeSize Q s M) true := by
  have hfirst := (PCPPNativeCount.count_run Q s M).focus countSlots count_injective
    (input R Q s M Lq Lc) (count_input R Q s M Lq Lc)
  have hsecond := (PCPPNativeEnvelope.envelope_run R Q (PCPPNativeCount.nativeSize Q s M)
    (PCPPNativeCount.stride s) Lq Lc).focus envelopeSlots envelope_injective
    (counted R Q s M Lq Lc) (envelope_input R Q s M Lq Lc)
  obtain ⟨caps,hcaps,hw,hC,hF,hG⟩ := PCPPNativeCapacityReady.ready (W R Q s M Lq Lc)
  have hthird := hcaps.focus capacitySlots capacity_injective (measured R Q s M Lq Lc)
    (capacity_input R Q s M Lq Lc)
  have hall := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hfirst hsecond) hthird
  let out := install capacitySlots (measured R Q s M Lq Lc) caps
  have low (i : Fin 95) (hi : i.val<33) : out i=measured R Q s M Lq Lc i :=
    install_other _ _ _ _ (fun j => capacity_away j i hi)
  have output (i : Fin 61) : out (capacitySlots i)=caps i := install_slot _ capacity_injective _ _ _
  refine ⟨out,hall,(output 0).trans hw,(output 8).trans hC,(output 28).trans hF,(output 50).trans hG,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (low 0 (by decide)).trans (measured_slot R Q s M Lq Lc 1)
  · exact (low 1 (by decide)).trans (measured_other R Q s M Lq Lc 1 (by decide))
  · exact (low 2 (by decide)).trans (measured_other R Q s M Lq Lc 2 (by decide))
  · exact (low 18 (by decide)).trans (measured_slot R Q s M Lq Lc 0)
  · exact (low 19 (by decide)).trans (measured_slot R Q s M Lq Lc 4)
  · exact (low 20 (by decide)).trans (measured_slot R Q s M Lq Lc 5)
  · exact (low 6 (by decide)).trans (measured_other R Q s M Lq Lc 6 (by decide))
  · exact (low 8 (by decide)).trans (measured_other R Q s M Lq Lc 8 (by decide))
  · exact (low 14 (by decide)).trans (measured_other R Q s M Lq Lc 14 (by decide))
  · exact (low 16 (by decide)).trans (measured_slot R Q s M Lq Lc 2)

theorem bounds (R Q s M Lq Lc : ℕ) :
    4≤W R Q s M Lq Lc ∧ R≤W R Q s M Lq Lc ∧ Q≤W R Q s M Lq Lc ∧
    PCPPNativeCount.nativeSize Q s M≤W R Q s M Lq Lc ∧
    PCPPNativeCount.stride s≤W R Q s M Lq Lc ∧ Lq≤W R Q s M Lq Lc ∧ Lc≤W R Q s M Lq Lc := by
  obtain ⟨h4,hR,hQ,hN,hstride,hLq,hLc,_⟩ := PCPPNativeEnvelope.bounds R Q
    (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc
  exact ⟨h4,hR,hQ,hN,hstride,hLq,hLc⟩

end NearCubicWires.RepairOrdinary.PCPPNativeResources
