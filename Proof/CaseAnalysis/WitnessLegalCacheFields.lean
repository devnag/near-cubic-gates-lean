import Proof.CaseAnalysis.WitnessLegalRun

/-! The legal-policy input shares only cache domain13; all remaining
prepaid cache tapes lie outside its four retained input fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
open private cache_injective from Proof.CaseAnalysis.WitnessLegalFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem native_cache_injective (a : PointwisePCPPAlgorithm) :
    Function.Injective (fun j : Fin 19 => NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a j)) :=
  cache_injective a

private theorem fresh_ne_old {t u : ℕ} (i : Fin u) (j : Fin t) : i.natAdd t≠j.castAdd u:=by
  intro he
  have hv:=congrArg Fin.val he
  have hj:=j.isLt
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

private theorem local_cache (a : PointwisePCPPAlgorithm) (D : ℕ) (i : Fin 4) (j : Fin 19)
    (he:SourcePolicy.Call.slots D (NativePolicy.fields a) (localFields D i)=
      SourcePolicy.Call.old D (NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a j))) : j=13:=by
  by_cases h:i=0
  · subst i
    have eq:SourcePolicy.Call.old D (NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 13))=
      SourcePolicy.Call.old D (NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a j)):=he
    exact (cache_injective a ((Fin.castAdd_injective _ _) eq)).symm
  · have hw:36≤CorePolicy.W D:=by dsimp [CorePolicy.W,CloseoutSchedule.Width.tapes,CloseoutSchedule.Clause.tapes];omega
    have hn:(localFields D i).val≠0 ∧ (localFields D i).val≠42:=by
      rw [local_val]
      fin_cases i <;> dsimp <;> first | exact False.elim (h rfl) | omega
    rw [SourcePolicy.Call.slots,if_neg hn.1,if_neg hn.2] at he
    exact False.elim (fresh_ne_old _ _ he)

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def cache (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (j : Fin 19):=
  old source a k D G e (ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))
theorem fields_cache (a : PointwisePCPPAlgorithm) (k D G : ℕ) (i : Fin 4) (j : Fin 19)
    (he:fields source a k D G i=ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j)) : j=13:=by
  have one:=(NativePipeline.Dock.slots_injective a D G (ColdNative.fields source k)
    (ColdNative.fields_injective source k)) he
  have two:=(NativePolicy.Call.slots_injective a D (NativePipeline.counter G) (NativeScreen.slots_injective G)) one
  exact local_cache a D i j two

theorem fields_ne_cache (a : PointwisePCPPAlgorithm) (k D G : ℕ) (j : Fin 19) (hj:j≠13) :
    ∀ i,fields source a k D G i≠ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j):=
  fun i he=>hj (fields_cache source a k D G i j he)

theorem domain_cache (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :
    slots source a k D G e (LegalTemplate.templateSlots e 0)=cache source a k D G e 13:=by
  have aliasEq:LegalTemplate.Call.slots e (fields source a k D G) (LegalTemplate.templateSlots e 0)=
      LegalTemplate.Call.old e (fields source a k D G 0):=by
    simp only [LegalTemplate.Call.slots,Function.comp_apply,LegalTemplate.Call.remap,LegalTemplate.templateSlots,
      Fin.val_castAdd,Fin.val_zero,ite_true,LegalTemplate.Call.bank,Fin.addCases_left]
  exact aliasEq.trans (congrArg (LegalTemplate.Call.old e) (domain_slot source a k D G))

def originalTape (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :=
  old source a k D G e (ColdNative.originalTape source a k D G)

theorem fields_ne_originalTape (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    ∀ i, fields source a k D G i ≠ ColdNative.originalTape source a k D G :=
  fun _ => ColdNative.slots_ne_originalTape source a k D G _

theorem slots_ne_originalTape (a : PointwisePCPPAlgorithm) (k D G e : ℕ) :
    ∀ i, slots source a k D G e i ≠ originalTape source a k D G e :=
  LegalTemplate.Call.outside e (fields source a k D G) _ (fields_ne_originalTape source a k D G)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
