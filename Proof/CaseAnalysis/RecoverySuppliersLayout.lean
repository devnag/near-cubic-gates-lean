import Proof.CaseAnalysis.RecoveryHierarchyDockCount
import Proof.CaseAnalysis.RecoveryCapacityDriversBudget
import Proof.CaseAnalysis.RecoveryProjectionBudget
import Proof.CaseAnalysis.RecoveryFullBoundResources
import Proof.CaseAnalysis.RecoveryPreparedLayout

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def base (k : ℕ):=RecoveryBoundedColdHierarchyDock.Count.tapes source k
def extra (d : ℕ):=1+49+113+RecoveryFullBound.tapes d
def tapes (k d : ℕ):=base source k+extra d
theorem base_large (k : ℕ) : 158<base source k:=by
  dsimp only [base,RecoveryBoundedColdHierarchyDock.Count.tapes,RecoveryBoundedColdHierarchyDock.tapes]
  omega
def old (k d : ℕ) (i : Fin 158) : Fin (tapes source k d):=
  ⟨i.val,by have hi:=i.isLt;have hb:=base_large source k;dsimp only [tapes];omega⟩
def countSlots (k d : ℕ) (i : Fin (base source k)) : Fin (tapes source k d):=i.castAdd (extra d)
def wPort (k d : ℕ) : Fin (tapes source k d):=
  ⟨base source k,by dsimp only [tapes,extra];omega⟩
def capacityWork (k d : ℕ) (i : Fin 49) : Fin (tapes source k d):=
  ⟨base source k+1+i.val,by have hi:=i.isLt;dsimp only [tapes,extra];omega⟩
def projectionWork (k d : ℕ) (i : Fin 113) : Fin (tapes source k d):=
  ⟨base source k+1+49+i.val,by have hi:=i.isLt;dsimp only [tapes,extra];omega⟩
def fullWork (k d : ℕ) (i : Fin (RecoveryFullBound.tapes d)) : Fin (tapes source k d):=
  ⟨base source k+1+49+113+i.val,by have hi:=i.isLt;dsimp only [tapes,extra];omega⟩
def rBitsPort (k d : ℕ):=countSlots source k d
  (RecoveryBoundedColdHierarchyDock.Count.prior source k (RecoveryBoundedColdHierarchyDock.rBitsPort source k))
def qBitsPort (k d : ℕ):=countSlots source k d
  (RecoveryBoundedColdHierarchyDock.Count.prior source k (RecoveryBoundedColdHierarchyDock.qBitsPort source k))
def hierarchyPort (k d : ℕ):=countSlots source k d
  (RecoveryBoundedColdHierarchyDock.Count.prior source k (RecoveryBoundedColdHierarchyDock.inputPort source k))

def capacitySlots (k d : ℕ) (i : Fin 49) : Fin (tapes source k d):=
  if i.val=0 then wPort source k d else if i.val=7 then old source k d 154
  else if i.val=45 then old source k d 76 else if i.val=48 then old source k d 77
  else capacityWork source k d i
def projectionSlots (k d : ℕ) (i : Fin 113) : Fin (tapes source k d):=
  if h : i.val<37 then old source k d ⟨78+i.val,by omega⟩
  else if i.val=37 then rBitsPort source k d else if i.val=65 then qBitsPort source k d
  else if i.val=104 then old source k d 76 else if i.val=106 then old source k d 115
  else if i.val=109 then old source k d 153 else if i.val=111 then old source k d 156
  else projectionWork source k d i
def fullSlots (k d : ℕ) (i : Fin (RecoveryFullBound.tapes d)) : Fin (tapes source k d):=
  if i=RecoveryFullBound.sourceSlot d then old source k d 153
  else if i=RecoveryFullBound.rawSlot d then old source k d 155
  else if i=RecoveryFullBound.compareSlot d then old source k d 152
  else fullWork source k d i
def input (k d : ℕ) (word : List Bool) (W : ℕ) (i : Fin (tapes source k d)):=
  if i.val=158 then word else if i.val=base source k then List.replicate W true else []

private theorem original_away (k : ℕ) (i : Fin (HierarchyStreams.base source k))
    (j : Fin 48) (hj0 : j≠0) (hj13 : j≠13) (hj14 : j≠14) :
    HierarchyStreams.old source k i≠HierarchyStreams.slots source k j:=by
  intro he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  simp only [HierarchyStreams.old,HierarchyStreams.slots,hj0,hj13,hj14,if_false,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
theorem original_fresh (k : ℕ) (i : Fin (HierarchyStreams.base source k)) :
    RecoveryBoundedColdHierarchyDock.slots source k (HierarchyStreams.old source k i)=
      RecoveryBoundedColdHierarchyDock.fresh source k (HierarchyStreams.old source k i):=by
  simp only [RecoveryBoundedColdHierarchyDock.slots,
    if_neg (original_away source k i 38 (by decide) (by decide) (by decide)),
    if_neg (original_away source k i 29 (by decide) (by decide) (by decide))]

theorem bits_range (k d : ℕ) :
    158≤(rBitsPort source k d).val ∧ (rBitsPort source k d).val<base source k ∧
    158≤(qBitsPort source k d).val ∧ (qBitsPort source k d).val<base source k:=by
  have hr:=(RecoveryBoundedColdHierarchyDock.Count.prior source k
    (RecoveryBoundedColdHierarchyDock.rBitsPort source k)).isLt
  have hq:=(RecoveryBoundedColdHierarchyDock.Count.prior source k
    (RecoveryBoundedColdHierarchyDock.qBitsPort source k)).isLt
  change (rBitsPort source k d).val<base source k at hr
  change (qBitsPort source k d).val<base source k at hq
  refine ⟨?_,hr,?_,hq⟩
  all_goals
    simp only [rBitsPort,qBitsPort,countSlots,RecoveryBoundedColdHierarchyDock.Count.prior,
      RecoveryBoundedColdHierarchyDock.rBitsPort,RecoveryBoundedColdHierarchyDock.qBitsPort,
      original_fresh,RecoveryBoundedColdHierarchyDock.fresh,Fin.val_castAdd,Fin.val_natAdd]
    omega

theorem bits_distinct (k d : ℕ) : (rBitsPort source k d).val≠(qBitsPort source k d).val:=by
  intro he
  have hports : RecoveryBoundedColdHierarchyDock.rBitsPort source k=
      RecoveryBoundedColdHierarchyDock.qBitsPort source k:=Fin.ext he
  have horig:=RecoveryBoundedColdHierarchyDock.slots_injective source k hports
  have hdims : HierarchyStreams.bitsR source k=HierarchyStreams.bitsQ source k:=
    Fin.ext (congrArg (fun j : Fin (HierarchyStreams.tapes source k)=>j.val) horig)
  have hd:=HierarchyStreams.dimension_injective source k hdims
  have hv:=congrArg Fin.val hd
  have hb:=HierarchyStreams.bit_values source.degrees.proofLog source.degrees.queries
  rw [hb.1,hb.2] at hv
  omega

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
