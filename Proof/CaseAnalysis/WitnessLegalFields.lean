import Proof.CaseAnalysis.WitnessNativeRun
import Proof.CaseAnalysis.WitnessLegalTemplateCall

/-! The four actual retained fields of the guarded source/cache path are
the direct legal-policy input. The actual V counter stays distinct. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def sourceSlots (a : PointwisePCPPAlgorithm) (k D G : ℕ) (i : Fin (SourcePolicy.tapes D)):=
  ColdNative.slots source a k D G
    (NativePipeline.localSlots a D G (NativePolicy.policySlots a D i))
def localFields (D : ℕ) : Fin 4→Fin (SourcePolicy.tapes D):=
  ![SourcePolicy.coreSlot D,SourcePolicy.q0Slot D,SourcePolicy.countSlots D 38,SourcePolicy.capSlot D]
def fields (a : PointwisePCPPAlgorithm) (k D G : ℕ):=sourceSlots source a k D G ∘ localFields D
def countSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=sourceSlots source a k D G (SourcePolicy.countSlots D 40)

private theorem cache_injective (a : PointwisePCPPAlgorithm) :
    Function.Injective (fun j : Fin 19=>NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a j)):=by
  intro i j h
  have hd:PCPPNativeClauseDescriptorConsumer.slots (363 : Fin 364) 16 14 27≠
      PCPPNativeClauseDescriptorConsumer.slots (363 : Fin 364) 16 14 10:=by
    intro he
    have he':=(PCPPNativeClauseDescriptorConsumer.slots_injective (363 : Fin 364) 16 14
      (by decide) (by decide) (by decide)) he
    exact (by decide : (27 : Fin 65)≠10) he'
  have h1:=(PCPPNativeSource.source_injective a
    (PCPPNativeClauseDescriptorConsumer.slots (363 : Fin 364) 16 14 27)
    (PCPPNativeClauseDescriptorConsumer.slots (363 : Fin 364) 16 14 10) hd) h
  have h2:=(PCPPSourceCache.cold_injective a) h1
  have h3:=(PCPPQueryCold.bank_injective (PCPPSourceCache.degree a)) h2
  exact Fin.ext (congrArg (fun z : Fin 21=>z.val) h3)
private theorem native_fields_injective (a : PointwisePCPPAlgorithm) : Function.Injective (NativePolicy.fields a):=by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · change NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 0)=
      NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 13) at h
    have he:=cache_injective a h
    exact False.elim ((by decide : (0 : Fin 19)≠13) he)
  · change NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 13)=
      NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 0) at h
    have he:=cache_injective a h
    exact False.elim ((by decide : (13 : Fin 19)≠0) he)
  · rfl

theorem source_injective (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    Function.Injective (sourceSlots source a k D G):=by
  intro i j h
  have h1:=(NativePipeline.Dock.slots_injective a D G (ColdNative.fields source k)
    (ColdNative.fields_injective source k)) h
  have h2:=(NativePolicy.Call.slots_injective a D (NativePipeline.counter G)
    (NativeScreen.slots_injective G)) h1
  exact (SourcePolicy.Call.slots_injective D (NativePolicy.fields a) (native_fields_injective a)) h2

theorem local_val (D : ℕ) (i : Fin 4) : (localFields D i).val=
    (![42,CorePolicy.W D+46,38,CorePolicy.W D+67] : Fin 4→ℕ) i:=by
  have hw:36 ≤ CorePolicy.W D:=by dsimp [CorePolicy.W,CloseoutSchedule.Width.tapes,CloseoutSchedule.Clause.tapes];omega
  fin_cases i
  · rfl
  · change (SourcePolicy.q0Slot D).val=CorePolicy.W D+46
    simp only [SourcePolicy.q0Slot,SourcePolicy.policySlots,CorePolicy.q0_val,
      if_neg (show CorePolicy.W D+3≠0 by omega),if_neg (show CorePolicy.W D+3≠5 by omega)]
    omega
  · rfl
  · have hc:(CorePolicy.capSlot D).val=CorePolicy.W D+24:=by
      change CorePolicy.W D+5+19=CorePolicy.W D+24;omega
    change (SourcePolicy.capSlot D).val=CorePolicy.W D+67
    simp only [SourcePolicy.capSlot,SourcePolicy.policySlots,hc,
      if_neg (show CorePolicy.W D+24≠0 by omega),if_neg (show CorePolicy.W D+24≠5 by omega)]
    omega

theorem local_injective (D : ℕ) : Function.Injective (localFields D):=by
  have hw:36 ≤ CorePolicy.W D:=by dsimp [CorePolicy.W,CloseoutSchedule.Width.tapes,CloseoutSchedule.Clause.tapes];omega
  intro i j h
  have hv:=congrArg Fin.val h
  rw [local_val,local_val] at hv
  fin_cases i <;> fin_cases j <;> first | rfl | (dsimp at hv;omega)
theorem fields_injective (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    Function.Injective (fields source a k D G):=
  (source_injective source a k D G).comp (local_injective D)

theorem domain_slot (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    fields source a k D G 0=ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a 13):=by
  simp only [fields,Function.comp_apply,localFields,Matrix.cons_val_zero,sourceSlots,
    ColdNative.cacheSlots,NativePipeline.cacheSlots]
  apply congrArg (ColdNative.slots source a k D G)
  apply congrArg (NativePipeline.localSlots a D G)
  simp only [NativePolicy.policySlots,SourcePolicy.Call.slots,SourcePolicy.coreSlot]
  rfl

theorem fields_ne_count (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    ∀ i,fields source a k D G i≠countSlot source a k D G:=by
  have hw:36 ≤ CorePolicy.W D:=by dsimp [CorePolicy.W,CloseoutSchedule.Width.tapes,CloseoutSchedule.Clause.tapes];omega
  intro i he
  have hl:localFields D i=SourcePolicy.countSlots D 40:=source_injective source a k D G he
  have hv:=congrArg Fin.val hl
  rw [local_val] at hv
  change (![42,CorePolicy.W D+46,38,CorePolicy.W D+67] : Fin 4→ℕ) i=40 at hv
  fin_cases i <;> dsimp at hv <;> omega

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
