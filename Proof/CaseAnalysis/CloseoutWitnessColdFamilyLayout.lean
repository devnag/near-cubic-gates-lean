import Proof.CaseAnalysis.CloseoutWitnessColdFamilyResources

/-! The guarded original source path enters the whole family through the
retained policy. Only the raw family is added as one independent input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=ColdLegal.tapes source a k D G e+1
def old (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (i : Fin (ColdLegal.tapes source a k D G e)):=i.castAdd 1
def rawSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=(0 : Fin 1).natAdd (ColdLegal.tapes source a k D G e)
def lengthSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=
  old source a k D G e (ColdLegal.lengthSlot source a k D G e)
def countSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=
  old source a k D G e (ColdLegal.old source a k D G e (ColdLegal.countSlot source a k D G))
def policy (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (i : Fin (LegalTemplate.tapes e)):=
  old source a k D G e (ColdLegal.slots source a k D G e i)
def baseInput (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (x raw bits : List Bool) :
    Fin (base source a k D G e)→List Bool:=
  Fin.addCases (ColdLegal.input source a k D G e x raw) (fun _=>frame bits)
def input (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (x raw bits : List Bool):=
  FamilyFromPolicy.input E (baseInput source a k D G e x raw bits)
def fields (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=
  FamilyFromPolicy.fields e E (lengthSlot source a k D G e) (countSlot source a k D G e)
    (rawSlot source a k D G e) (policy source a k D G e)
def familySlots (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=FamilyCold.Call.slots (fields source a k D G e E)
def guardSlot (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=
  FamilyCold.Call.old (FamilyCapacity.Call.old E (old source a k D G e (ColdLegal.flagSlot source a k D G e)))
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool):=
  TapeEmbedding.machine FamilyCold.Call.extra (TapeEmbedding.machine (FamilyCapacity.Call.extra E)
    (TapeEmbedding.machine 1 (ColdLegal.machine source a k CH Cpad cutoff D G copies e den delta code sym)))
def second (a : PointwisePCPPAlgorithm) (k D G e E K km : ℕ) (q : ℚ) (sym : Bool):=
  FamilyFromPolicy.machine e E K (lengthSlot source a k D G e) (countSlot source a k D G e)
    (rawSlot source a k D G e) (policy source a k D G e) sym km q
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den km : ℕ)
    (delta q : ℚ) (code : List Bool) (sym : Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G copies e E den delta code sym)
    (second source a k D G e E K km q sym) (fun scanned=>scanned (guardSlot source a k D G e E))

private theorem separate {t u : ℕ} (i : Fin t) (j : Fin u) : i.castAdd u≠j.natAdd t:=by
  intro he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem policy_injective (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :
    Function.Injective (policy source a k D G e):=
  (Fin.castAdd_injective _ _).comp
    (LegalTemplate.Call.slots_injective e (ColdLegal.fields source a k D G)
      (ColdLegal.fields_injective source a k D G))
theorem count_ne_raw (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :
    countSlot source a k D G e≠rawSlot source a k D G e:=
  separate _ _
theorem count_outside (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :
    ∀ i,countSlot source a k D G e≠policy source a k D G e i:=by
  intro i he
  dsimp only [countSlot,policy,old] at he
  have same:=(Fin.castAdd_injective _ _) he
  exact LegalTemplate.Call.outside e (ColdLegal.fields source a k D G) (ColdLegal.countSlot source a k D G)
    (ColdLegal.fields_ne_count source a k D G) i same.symm
theorem raw_outside (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :
    ∀ i,rawSlot source a k D G e≠policy source a k D G e i:=fun _=>(separate _ _).symm

theorem verdict_fresh (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) :
    familySlots source a k D G e E 724=
      (724 : Fin 3243).natAdd (base source a k D G e+FamilyCapacity.Call.extra E):=by
  rw [familySlots,FamilyCold.Call.slots,Function.comp_apply,
    FamilyCold.Call.remap_other 724 (by decide : ∀ j,FamilySparse.port j≠724),
    FamilyCold.Call.bank,Fin.addCases_right]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
