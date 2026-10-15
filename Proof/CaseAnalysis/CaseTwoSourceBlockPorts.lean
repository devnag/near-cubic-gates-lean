import Proof.CaseAnalysis.CaseTwoSourceBlock

/-! The original source exposes one injective cache/request interface. Its
retained hierarchy, descriptor and address stay outside that interface. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceBlock
open LocalBitMultitape RepairSource RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def commonSlots (k : ℕ) (j : Fin (SourceCache.tapes a)):=sourceSlots source a k
  (OriginalSource.slots source a k (RequestSource.cacheSlots a j))
theorem common_injective (k : ℕ) : Function.Injective (commonSlots source a k):=by
  exact (source_injective source a k).comp
    ((NativeSourceDock.slots_injective a (RequestDescriptor.frameSlot source k)
      (RequestDescriptor.sizeSlot source k) (RequestDescriptor.aritySlot source k)
      (OriginalSource.distinct source k).1 (OriginalSource.distinct source k).2.1
      (OriginalSource.distinct source k).2.2).comp (RequestSource.cache_injective a))
theorem cache_injective (k : ℕ) : Function.Injective (cacheSlots source a k):=by
  intro i j he
  have hc:=common_injective source a k he
  have hb:=SourceCache.cold_injective a hc
  have hi:=PCPPQueryCold.bank_injective (SourceCache.degree a) hb
  exact Fin.ext (congrArg (fun x : Fin 21=>x.val) hi)
theorem cache_request (k : ℕ) (j : Fin 19) : cacheSlots source a k j≠requestSlot source a k:=by
  intro he
  exact SourceCache.cold_away a _ (common_injective source a k he)
theorem cache_away (k : ℕ) (i : Fin 3) (j : Fin 19) :
    cacheSlots source a k j≠old source a k (i.castAdd 5):=
  source_away source a k i _
theorem request_away (k : ℕ) (i : Fin 3) : requestSlot source a k≠old source a k (i.castAdd 5):=
  source_away source a k i _

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceBlock
