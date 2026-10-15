import Proof.MachineModel.OrdinaryMatrixBatchAllRanksBounds
import Proof.Circuits.MatrixBucketDimensionsPower

/-! The accepted ten-power program consumes the D driver physically
produced by the full raw batch caller. This is same-program finite padding;
its zero work tapes are supplied by the following caller's paid clear. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketRootPower
open LocalBitMultitape MatrixScoreBatch
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_pad (C D : ℕ) (bits : List Bool) (h : C≤D) :
    ZeroPadding.pad D (ZeroPadding.pad C bits)=ZeroPadding.pad D bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc]
  rw [←List.replicate_add]
  congr 2
  omega

theorem power_run (r : Request) (c : ℕ) (hc : 1≤c) (hroot : c≤MatrixBucketDimensions.capacity r.U) :
    ∃ actual,run MatrixBucketDimensions.Power.machine (WilliamsPower.budget 10 c+2)
      (MatrixBucketDimensions.Power.input c (D r))=some actual ∧
      actual.steps≤WilliamsPower.budget 10 c+2 ∧
      actual.final.tapes 0=UnaryTemplate.tape c ∧
      actual.final.tapes 20=ZeroPadding.pad (D r) (List.replicate (c^10) true) ∧
      (∀ i,actual.final.heads i=0) ∧ (∀ i,(actual.final.tapes i).length≤D r) := by
  have hD : MatrixBucketDimensions.scratchCapacity r.U≤D r := (MatrixBatchCapacity.request_capacity r).2
  obtain ⟨base,hb,bs,b0,b20,bh,bt⟩ := MatrixBucketDimensions.Power.power_run r.U c Nat.one_le_two_pow hc hroot
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config MatrixBucketDimensions.Power.machine
    (MatrixBucketDimensions.Power.capacities (D r)) _ _ base hb
  have hi : ZeroPadding.config (MatrixBucketDimensions.Power.capacities (D r))
      (initialConfiguration MatrixBucketDimensions.Power.machine
        (MatrixBucketDimensions.Power.input c (MatrixBucketDimensions.scratchCapacity r.U)))=
      initialConfiguration MatrixBucketDimensions.Power.machine (MatrixBucketDimensions.Power.input c (D r)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases he : i=0
      · subst i
        simp [ZeroPadding.config,MatrixBucketDimensions.Power.capacities,MatrixBucketDimensions.Power.input,initialConfiguration]
      · simp [ZeroPadding.config,MatrixBucketDimensions.Power.capacities,MatrixBucketDimensions.Power.input,initialConfiguration,
          he,ZeroPadding.pad,Nat.add_sub_of_le hD]
  rw [hi] at ha
  refine ⟨actual,ha,hs.trans_le bs,?_,?_,?_,?_⟩
  · rw [hf]
    simpa [ZeroPadding.config,MatrixBucketDimensions.Power.capacities] using b0
  · rw [hf]
    change ZeroPadding.pad (D r) (base.final.tapes 20)=_
    rw [b20,pad_pad _ _ _ hD]
  · intro i
    rw [hf]
    exact bh i
  · intro i
    rw [hf]
    have ht := (bt i).trans hD
    by_cases he : i=0
    · subst i
      simpa [ZeroPadding.config,MatrixBucketDimensions.Power.capacities] using ht
    · simp only [ZeroPadding.config,MatrixBucketDimensions.Power.capacities,he,ite_false,
        ZeroPadding.pad,List.length_append,List.length_replicate]
      omega

end NearCubicWires.RepairOrdinary.MatrixBucketRootPower
