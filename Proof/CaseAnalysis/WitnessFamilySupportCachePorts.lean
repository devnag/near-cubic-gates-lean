import Proof.CaseAnalysis.WitnessFamilySupportLayout
import Proof.CaseAnalysis.WitnessFamilyCacheRun

/-! Every old query-cache address lifts unchanged; the one shared domain
field is still exactly the original family domain tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem domain_cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) :
    familySlots source a k D G e E 2501=cache source a k D G e E 13:=
  (family_old source a k D G e E 2501).trans
    (congrArg (fun i=>i.castAdd 1) (ColdFamily.domain_cache source a k D G e E))

theorem cache_old (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (j : Fin 19) :
    cache source a k D G e E j=
      FamilySupportCall.old (FamilyCapacity.Call.old E
        (ColdFamily.old source a k D G e (ColdLegal.cache source a k D G e j))) := rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
