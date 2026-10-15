import Proof.CaseAnalysis.WitnessBoundedFamilySupportLayout

/-! The strengthened header attachment reuses each old header and family
address, and supplies the added family tape with the empty stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem header_old (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (data : Fin 150→List Bool) (i : Fin 150) :
    SupportDock.lift (HeaderDock.input (BoundedFamily.workspace source a k D G E) data) []
      ((HeaderDock.old (BoundedFamily.workspace source a k D G E) i).castAdd 1)=data i := by
  simp only [SupportDock.lift,Fin.addCases_left,HeaderDock.input,HeaderDock.old]

theorem input_data (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool)
    (x bits : List Bool) (scratch : ℕ)
    (hvalid:readTapeBit (CompetitorWitnessBounded.output x bits scratch 147) 0=true)
    (j : Fin (BoundedFamily.localTapes source a k D G E sym+1)) :
    SupportDock.lift (HeaderDock.input (BoundedFamily.workspace source a k D G E)
      (CompetitorWitnessBounded.output x bits scratch)) [] (slots source a k D G E sym j)=
    ColdFamilySupport.input source a k D G (BoundedFamily.exponent sym) E x
      (BoundedFields.oracle bits) (BoundedFields.family bits) j :=
  SupportDock.local_fields _ _ _ [] (BoundedFamily.input_data source a k D G E sym x bits scratch hvalid) j

theorem family_flag_slot (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) :
    slots source a k D G E sym
      (ColdFamilySupport.familySlots source a k D G (BoundedFamily.exponent sym) E 724)=
        flag source a k D G E :=
  (congrArg (slots source a k D G E sym)
    (ColdFamilySupport.family_old source a k D G (BoundedFamily.exponent sym) E 724)).trans
      (flag_slot source a k D G E sym)

theorem header_flag (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (data : Fin 150→List Bool) :
    SupportDock.lift (HeaderDock.input (BoundedFamily.workspace source a k D G E) data) []
      (flag source a k D G E)=[] := by
  rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
