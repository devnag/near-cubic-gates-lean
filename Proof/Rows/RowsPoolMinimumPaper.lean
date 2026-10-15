import Proof.Assembly.RowProduction
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryRowLookupTapes

/-! The actual ordered coordinate loop computes the paper's minimum live
score. This is the field identity needed at the transformed native threshold,
with the original gate and the physically supplied membership order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open RepairRepresentation SupplierPipeline CloseoutRowsPoolWeight
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {q : ℕ}

def items (g : NormalizedThresholdGate q) (live : Finset (Fin q)) : List Item:=
  List.ofFn (fun i : Fin q=>(g.weight i,decide (i∈live)))

theorem items_length (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    (items g live).length=q:=by simp [items]

theorem items_word (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    word (items g live)=(List.ofFn g.weight).flatMap intWord:=by
  change (List.ofFn (fun i : Fin q=>(g.weight i,decide (i∈live)))).flatMap (fun x=>intWord x.1)=_
  rw [←List.flatMap_map]
  rw [List.map_ofFn]
  rfl

theorem items_mask (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    mask (items g live)=List.ofFn (fun i : Fin q=>decide (i∈live)):=by
  simp [mask,items,List.map_ofFn,Function.comp_def]

theorem items_emitted (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    emitted (items g live)=
      (List.ofFn (fun i : Fin q=>if i∈live then (0 : ℤ) else g.weight i)).flatMap intWord:=by
  unfold emitted items
  rw [←List.flatMap_map,List.map_ofFn]
  congr 2
  funext i
  simp [transformed]

theorem negative_nat (z : ℤ) : ((-z).toNat : ℤ)=-(if z<0 then z else 0):=by
  cases z <;> simp

theorem items_minimum (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    (liveSum (items g live) : ℤ)=-minimumLiveScore g live:=by
  have hall: (liveSum (items g live) : ℤ)=
      ∑ i : Fin q,if i∈live then ((-g.weight i).toNat : ℤ) else 0:=by
    simp [liveSum,items,List.map_ofFn,List.sum_ofFn]
  rw [hall]
  have hfilter:Finset.univ.filter (fun i : Fin q=>i∈live)=live:=by ext i;simp
  rw [←Finset.sum_filter,hfilter,minimumLiveScore,←Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _=>negative_nat (g.weight i))

theorem items_all_negative (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    negSum (items g live)=liveSum (items g Finset.univ):=by
  simp [negSum,liveSum,items,List.map_ofFn,Function.comp_def]

theorem strict_threshold (g : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    (g.threshold-1)+(liveSum (items g live) : ℤ)=g.threshold-minimumLiveScore g live-1:=by
  rw [items_minimum]
  ring

end
end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
