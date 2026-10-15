import Proof.CaseAnalysis.WitnessLegalCacheRun
import Proof.CaseAnalysis.CloseoutWitnessColdFamilyRun

/-! The actual query-cache ports survive the family alias map. Only its
existing domain13 is shared with the family; the rest are outside it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
open private fresh_ne_old from Proof.CaseAnalysis.WitnessLegalCacheFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace FamilyFromPolicy
theorem fields_outside {t : ℕ} (e E : ℕ) (source count raw i : Fin t)
    (policy : Fin (LegalTemplate.tapes e)→Fin t) (hc:count≠i) (hr:raw≠i) (hp:∀j,policy j≠i) :
    ∀j,fields e E source count raw policy j≠FamilyCapacity.Call.old E i:=by
  have ext:∀j,external E source count raw j≠FamilyCapacity.Call.old E i:=by
    intro j he
    have hv:=congrArg Fin.val he
    rw [external_val] at hv
    change (![t+(5+2*E),t+(FamilyCapacity.A E+4),count.val,raw.val] : Fin 4→ℕ) j=i.val at hv
    have hi:=i.isLt
    fin_cases j
    · dsimp at hv;omega
    · dsimp at hv;omega
    · exact hc (Fin.ext hv)
    · exact hr (Fin.ext hv)
  have ins:∀j,inside e E policy j≠FamilyCapacity.Call.old E i:=by
    intro j he
    exact hp _ ((Fin.castAdd_injective _ _) he)
  intro j
  refine Fin.addCases (m:=4) (n:=100)
    (motive:=fun z=>Fin.addCases (external E source count raw) (inside e E policy) z≠
      FamilyCapacity.Call.old E i) ?_ ?_ (FamilyPolicyPorts.order j)
  · intro z;simpa only [Fin.addCases_left] using ext z
  · intro z;simpa only [Fin.addCases_right] using ins z
end FamilyFromPolicy

namespace ColdLegal
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem count_ne_cache (a : PointwisePCPPAlgorithm) (k D G : ℕ) (j : Fin 19) :
    countSlot source a k D G≠ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j):=by
  intro he
  have one:=(NativePipeline.Dock.slots_injective a D G (ColdNative.fields source k)
    (ColdNative.fields_injective source k)) he
  have two:=(NativePolicy.Call.slots_injective a D (NativePipeline.counter G) (NativeScreen.slots_injective G)) one
  have inner:SourcePolicy.Call.slots D (NativePolicy.fields a) (SourcePolicy.countSlots D 40)=
      SourcePolicy.Call.old D (NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a j)):=two
  rw [SourcePolicy.Call.slots,if_neg (by change (40:ℕ)≠0;decide),
    if_neg (by change (40:ℕ)≠42;decide)] at inner
  exact fresh_ne_old _ _ inner
theorem count_ne_originalTape (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    countSlot source a k D G ≠ ColdNative.originalTape source a k D G :=
  ColdNative.slots_ne_originalTape source a k D G _
end ColdLegal

namespace ColdFamily
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (j : Fin 19):=
  ColdFamilyLift.old E (ColdLegal.cache source a k D G e j)
theorem fields_ne_cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (j : Fin 19) (hj:j≠13) :
    ∀i,fields source a k D G e E i≠FamilyCapacity.Call.old E (old source a k D G e (ColdLegal.cache source a k D G e j)):=by
  apply FamilyFromPolicy.fields_outside
  · intro he
    have one:=(Fin.castAdd_injective _ _) he
    have two:=(Fin.castAdd_injective _ _) one
    exact ColdLegal.count_ne_cache source a k D G j two
  · exact fresh_ne_old _ _
  · intro i he
    have one:=(Fin.castAdd_injective _ _) he
    exact LegalTemplate.Call.outside e (ColdLegal.fields source a k D G)
      (ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))
      (ColdLegal.fields_ne_cache source a k D G j hj) i one

def originalTape (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :=
  old source a k D G e (ColdLegal.originalTape source a k D G e)

theorem fields_ne_originalTape (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) :
    ∀ i, fields source a k D G e E i ≠ FamilyCapacity.Call.old E (originalTape source a k D G e) := by
  apply FamilyFromPolicy.fields_outside
  · intro he
    have one := (Fin.castAdd_injective _ _) he
    have two := (Fin.castAdd_injective _ _) one
    exact ColdLegal.count_ne_originalTape source a k D G two
  · exact fresh_ne_old _ _
  · intro i he
    have one := (Fin.castAdd_injective _ _) he
    exact ColdLegal.slots_ne_originalTape source a k D G e i one

theorem domain_cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) :
    familySlots source a k D G e E 2501=cache source a k D G e E 13:=by
  have port:FamilySparse.port 1=(2501 : Fin 3243):=rfl
  rw [familySlots,←port,FamilyCold.Call.slots,Function.comp_apply,FamilyCold.Call.remap_port,
    FamilyCold.Call.bank,Fin.addCases_left]
  have header:fields source a k D G e E 1=FamilyCapacity.Call.old E
      (old source a k D G e (ColdLegal.slots source a k D G e (LegalTemplate.templateSlots e 0))):=rfl
  rw [header,ColdLegal.domain_cache]
  rfl
end ColdFamily

end
end NearCubicWires.RepairOrdinary.CloseoutWitness
