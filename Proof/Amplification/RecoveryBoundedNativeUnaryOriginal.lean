import Proof.Amplification.RecoveryBoundedNativeUnaryMeaning

/-! Specialize the actual forward loop to the original compiler's
description-row unary-equality expression, with the same literal order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryBoundedNative BoundedOracleStructuralCircuit OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstIndex {n bound : ℕ} (row : Fin (bound+1)) (start : ℕ) := row.val*rowWidth n bound+start
theorem index_bound {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) :
    firstIndex (n:=n) row start+limit ≤ descriptionWidth n bound := by
  have hr:=Nat.mul_le_mul_right (rowWidth n bound) (Nat.succ_le_iff.mpr row.isLt)
  unfold firstIndex descriptionWidth boundedCircuitDescriptionWidth
  dsimp only [rowWidth] at hr hblock
  nlinarith

theorem items_unary {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) :
    items (firstIndex (n:=n) row start) 0 value limit (index_bound row start limit hblock)=
      unaryItems row start limit value hblock := by
  rw [items_ofFn]
  unfold unaryItems
  congr 1
  funext i
  apply Prod.ext
  · apply Fin.ext
    simp [firstIndex,descriptionIndex,Nat.add_assoc]
  · simp [RecoveryBoundedNativeUnaryFlag.negative]

def initial {n bound : ℕ} (row : Fin (bound+1)) (start base : ℕ) (out stack : List Bool) : State :=
  ⟨firstIndex (n:=n) row start,base,0,false,out,stack⟩

theorem original_prefix_run {n bound : ℕ} (row : Fin (bound+1))
    (start limit value base W C : ℕ) (out stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : firstIndex (n:=n) row start+limit ≤ W) (hp : base+2*limit ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (limit*(32*C+106)+limit+3)
      (configuration 0 C value (initial (n:=n) row start base out stack) limit 1)=some r ∧
      r.steps ≤ limit*(32*C+106)+limit+3 ∧
      r.final.tapes 20=out++(literalPrefix base (unaryItems row start limit value hblock)).flatMap PCPPRequestNodeSchema.native ∧
      r.final.tapes 31=stack++stackWords (literalReferences base (unaryItems row start limit value hblock)) ∧
      r.final.tapes 25=List.replicate (base+prefixCount (unaryItems row start limit value hblock)) true ∧
      r.final.heads 34=limit ∧ r.final.heads 35=1 := by
  let a:=initial (n:=n) row start base out stack
  obtain ⟨r,hr,rf,rs⟩:=loop_run limit W C value limit a (by simp [a,initial]) hi hp hC
  have hs:=iterate_schedule limit value a (index_bound row start limit hblock)
  have indices:=iterate_indices limit value a
  have select : items a.index a.offset value limit (index_bound row start limit hblock)=
      unaryItems row start limit value hblock := items_unary row start limit value hblock
  dsimp only at hs
  rw [select] at hs
  refine ⟨r,hr,rs,?_,?_,?_,?_,?_⟩
  · rw [rf]
    change (a.iterate value limit).out=_
    exact hs.2.1
  · rw [rf]
    change (a.iterate value limit).stack=_
    exact hs.2.2
  · rw [rf]
    change List.replicate (a.iterate value limit).position true=_
    rw [hs.1]
    rfl
  · rw [rf]
    change (a.iterate value limit).offset=limit
    simpa only [a,initial,Nat.zero_add] using indices.2
  · rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
