import Proof.Hierarchy.CompetitorCrossSchedulerBounds

/-! Fresh same-bucket workspace beside the complete cross-scheduler prefix.
Only original Request0 and raw W52 are shared; the same bank is disjoint
from every native cross-table tape and is retained during that table run. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountBanks
open LocalBitMultitape RecoveryRootRound
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := CompetitorCrossScheduler.tapes p+511
def native (p : Program) (i : Fin (CompetitorCrossScheduler.tapes p)) : Fin (tapes p) := i.castAdd 511
def extend (p : Program) (ambient : Fin (CompetitorCrossScheduler.tapes p) → List Bool) : Fin (tapes p) → List Bool :=
  Fin.addCases (m := CompetitorCrossScheduler.tapes p) (n := 511) (motive := fun _ => List Bool) ambient (fun _ => [])
def input (p : Program) (r : Request) := extend p (CompetitorCrossScheduler.input p r)
def bank (p : Program) : Fin (tapes p) := (2 : Fin 511).natAdd (CompetitorCrossScheduler.tapes p)
def sameSlots (p : Program) (i : Fin 511) : Fin (tapes p) :=
  if i.val=0 then native p (CompetitorCrossScheduler.fieldSlots p 0)
  else if i.val=1 then native p (CompetitorCrossScheduler.fieldSlots p 52)
  else i.natAdd (CompetitorCrossScheduler.tapes p)
def crossSlots (p : Program) (i : Fin 120) := native p (CompetitorCrossScheduler.crossSlots p i)

theorem extend_native (p : Program) (ambient : Fin (CompetitorCrossScheduler.tapes p) → List Bool)
    (i : Fin (CompetitorCrossScheduler.tapes p)) : extend p ambient (native p i)=ambient i := by
  simp only [extend,native,Fin.addCases_left]

theorem native_injective (p : Program) : Function.Injective (native p) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes p) => k.val) h)
theorem cross_injective (p : Program) : Function.Injective (crossSlots p) :=
  (native_injective p).comp (CompetitorCrossScheduler.cross_injective p)
theorem same_value (p : Program) (i : Fin 511) : (sameSlots p i).val=
    if i.val=0 then 0 else if i.val=1 then 52 else CompetitorCrossScheduler.tapes p+i.val := by
  unfold sameSlots
  split_ifs <;> rfl
theorem same_injective (p : Program) : Function.Injective (sameSlots p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have ht : 181 ≤ CompetitorCrossScheduler.tapes p := by unfold CompetitorCrossScheduler.tapes;omega
  rw [same_value,same_value] at hv
  split_ifs at hv <;> omega

theorem same_input (p : Program) (r : Request) (ambient : Fin (CompetitorCrossScheduler.tapes p) → List Bool)
    (h0 : ambient (CompetitorCrossScheduler.fieldSlots p 0)=MatrixScoreBatch.physicalInput r)
    (hw : ambient (CompetitorCrossScheduler.fieldSlots p 52)=List.replicate (CompetitorSameBucketColdDense.width r) true) :
    ∀ i,extend p ambient (sameSlots p i)=CompetitorSameBucketColdDense.input r i := by
  intro i
  by_cases hzero : i.val=0
  · have he : i=0 := Fin.ext hzero
    subst i
    change extend p ambient (native p (CompetitorCrossScheduler.fieldSlots p 0))=_
    rw [extend_native]
    exact h0
  by_cases hone : i.val=1
  · have he : i=1 := Fin.ext hone
    subst i
    change extend p ambient (native p (CompetitorCrossScheduler.fieldSlots p 52))=_
    rw [extend_native]
    exact hw
  · simp only [sameSlots,hzero,hone,↓reduceIte,extend,Fin.addCases_right]
    simp [CompetitorSameBucketColdDense.input,CompetitorSameBucketColdDense.publicInput,hzero,hone]

theorem same_native_keep (p : Program) (ambient : Fin (tapes p) → List Bool)
    (out : Fin 511 → List Bool) (i : Fin (CompetitorCrossScheduler.tapes p))
    (h0 : i.val≠0) (h52 : i.val≠52) :
    install (sameSlots p) ambient out (native p i)=ambient (native p i) := by
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  rw [same_value] at hv
  change (if j.val=0 then 0 else if j.val=1 then 52 else CompetitorCrossScheduler.tapes p+j.val)=i.val at hv
  split_ifs at hv <;> omega

theorem same_fields (p : Program) (r : Request) (ambient : Fin (CompetitorCrossScheduler.tapes p) → List Bool)
    (out : Fin 511 → List Bool)
    (h0 : ambient (CompetitorCrossScheduler.fieldSlots p 0)=MatrixScoreBatch.physicalInput r)
    (hw : ambient (CompetitorCrossScheduler.fieldSlots p 52)=List.replicate (CompetitorSameBucketColdDense.width r) true)
    (out0 : out 0=MatrixScoreBatch.physicalInput r)
    (out1 : out 1=List.replicate (CompetitorSameBucketColdDense.width r) true) :
    ∀ i,install (sameSlots p) (extend p ambient) out (native p i)=ambient i := by
  intro i
  by_cases hz : i.val=0
  · have he : native p i=sameSlots p 0 := Fin.ext hz
    rw [he,install_slot _ (same_injective p),out0]
    have hi : i=CompetitorCrossScheduler.fieldSlots p 0 := Fin.ext hz
    exact h0.symm.trans (congrArg ambient hi.symm)
  by_cases hw52 : i.val=52
  · have he : native p i=sameSlots p 1 := Fin.ext hw52
    rw [he,install_slot _ (same_injective p),out1]
    have hi : i=CompetitorCrossScheduler.fieldSlots p 52 := Fin.ext hw52
    exact hw.symm.trans (congrArg ambient hi.symm)
  · rw [same_native_keep _ _ _ _ hz hw52]
    exact extend_native p ambient i

theorem cross_avoids_bank (p : Program) (i : Fin 120) : crossSlots p i≠bank p := by
  intro h
  have hv := congrArg Fin.val h
  change (CompetitorCrossScheduler.crossSlots p i).val=CompetitorCrossScheduler.tapes p+2 at hv
  have hi := (CompetitorCrossScheduler.crossSlots p i).isLt
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountBanks
