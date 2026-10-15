import Proof.MachineModel.OrdinaryWilliamsCallLayout

/-! Literal source input fields on the positive-power boundary, and the
one paid simultaneous move positioning the five physical crop drivers. -/
namespace NearCubicWires.RepairOrdinary.WilliamsSourceCrop
open LocalBitMultitape RepairRepresentation SourceInterfaces ExecutableInterfaces WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sentinel_core_heads (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension)
    (i : Fin (a.tapeCount+1)) : (sentinelInput a r hr).heads (i.castAdd 6)=0 := by
  have hi : i.val ≤ a.tapeCount := Nat.le_of_lt_succ i.isLt
  simp [sentinelInput,ZeroPadding.config,Composition.leftConfig,sourceInput,TapeEmbedding.config,
    Fin.addCases,hi,initialConfiguration]

theorem sentinel_core_tapes (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension)
    (i : Fin (a.tapeCount+1)) : (sentinelInput a r hr).tapes (i.castAdd 6)=
      if i.val=0 then natWord (WilliamsPaddedRequest.dimension r.dimension)++rowMajorBitMatrix (WilliamsPaddedRequest.left r)
      else if i.val=1 then rowMajorBitMatrix (WilliamsPaddedRequest.right r) else [] := by
  have hi : i.val ≤ a.tapeCount := Nat.le_of_lt_succ i.isLt
  have h3 : i.castAdd 6≠extra a 3 := by intro h; have hv := congrArg Fin.val h; simp [extra] at hv; omega
  have h5 : i.castAdd 6≠extra a 5 := by intro h; have hv := congrArg Fin.val h; simp [extra] at hv; omega
  have hcap : sentinelCapacity a r (i.castAdd 6)=0 := by
    simp [sentinelCapacity]
    exact ⟨h3,h5⟩
  change ZeroPadding.pad (sentinelCapacity a r (i.castAdd 6)) _ = _
  rw [hcap]
  simp only [ZeroPadding.pad,Nat.zero_sub,List.replicate_zero,List.append_nil]
  by_cases hc : i.val<a.tapeCount
  · simp [Composition.leftConfig,sourceInput,TapeEmbedding.config,Fin.addCases,hi,initialConfiguration,
      hc,WilliamsReplay.inputs,WilliamsPaddedRequest.request,ExactPowerRequest.dimension,WilliamsPaddedRequest.dimension]
    simp only [Fin.ext_iff,Fin.val_zero]
    rfl
  · have hn0 : i.val≠0 := by have := a.threeTapes; omega
    have hn1 : i.val≠1 := by have := a.threeTapes; omega
    simp [Composition.leftConfig,sourceInput,TapeEmbedding.config,Fin.addCases,hi,initialConfiguration,hc,hn0,hn1]

end NearCubicWires.RepairOrdinary.WilliamsSourceCrop

namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RecoveryExecution RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def marked (a : WilliamsAlgorithm) (i : Fin (tapeCount a)) : Bool :=
  decide (i.val=5 ∨ i.val=51 ∨ i.val=12 ∨ i.val=81 ∨ i.val=85)
def heads (a : WilliamsAlgorithm) : Fin (tapeCount a) → ℕ := fun i => if marked a i then 1 else 0
def bootstrap (a : WilliamsAlgorithm) : Machine (tapeCount a) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if marked a i then .right else .stay⟩ else none

theorem bootstrap_run (a : WilliamsAlgorithm) (input : Fin (tapeCount a) → List Bool) :
    ∃ r : ExecutionReceipt (tapeCount a) 2,
      run (bootstrap a) 1 input=some r ∧ r.final=⟨1,heads a,input⟩ ∧ r.steps=1 := by
  have hs : step (bootstrap a) (initialConfiguration (bootstrap a) input)=some ⟨1,heads a,input⟩ := by
    simp [step,bootstrap,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; by_cases h : marked a i=true <;> simp [applyAction,heads,h,HeadMove.apply]
    · funext i; simp [applyAction]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem heads_core (a : WilliamsAlgorithm) (i : Fin (a.tapeCount+1)) : heads a (coreSlot a i)=0 := by
  unfold coreSlot
  split_ifs with h0 h1
  · simp [heads,marked]
  · simp [heads,marked]
  · have hbig : 95 ≤ 93+i.val := by omega
    have h5 : ¬93+i.val=5 := by omega
    have h51 : ¬93+i.val=51 := by omega
    have h12 : ¬93+i.val=12 := by omega
    have h81 : ¬93+i.val=81 := by omega
    have h85 : ¬93+i.val=85 := by omega
    simp [heads,marked,h5,h51,h12,h81,h85]

theorem heads_extra (a : WilliamsAlgorithm) (i : Fin 6) : heads a (extraSlot a i)=WilliamsSourceCrop.extraHeads i := by
  have hn (k : ℕ) (hk : k<95) : ¬94+a.tapeCount=k := by have := a.threeTapes; omega
  fin_cases i <;> simp [heads,marked,extraSlot,WilliamsSourceCrop.extraHeads,
    hn 5 (by decide),hn 51 (by decide),hn 12 (by decide),hn 81 (by decide),hn 85 (by decide)]

end NearCubicWires.RepairOrdinary.WilliamsCall
