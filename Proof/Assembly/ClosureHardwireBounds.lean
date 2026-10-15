import Proof.Assembly.ClosureHardwireChild
import Proof.MachineModel.ClosureCompactCacheCost

/-! A.12 hardwiring at the original equation's magnitude bound. The single
bound supplies all six arithmetic premises of `HardwireChild.child_run`;
physical masks, scratch, counters, and their paid capacities remain explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireBounds
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation RepairSource RepairSource.CloseoutFinal
open SupplierPipeline SupplierEstimator
open C10NaturalHardwireScore (items positiveSum selectedSum)
open CloseoutRowsPoolMinimum (negSum liveSum)
open C10NaturalHardwireTarget (pPart nPart)
open scoped BigOperators

private theorem part_le (z : Int) : z.toNat ≤ z.natAbs := by
  cases z <;> simp

private theorem negative_part_le (z : Int) : (-z).toNat ≤ z.natAbs := by
  simpa only [Int.natAbs_neg] using part_le (-z)

theorem score_bounds {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) :
    positiveSum (items live g y) ≤ ∑ i, (g.weight i).natAbs ∧
    negSum (items live g y) ≤ ∑ i, (g.weight i).natAbs ∧
    selectedSum (items live g y) ≤ ∑ i, (g.weight i).natAbs ∧
    liveSum (items live g y) ≤ ∑ i, (g.weight i).natAbs := by
  simp only [positiveSum,negSum,selectedSum,liveSum,items,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply]
  refine ⟨?_,?_,?_,?_⟩
  · exact Finset.sum_le_sum (fun i _ => part_le (g.weight i))
  · exact Finset.sum_le_sum (fun i _ => negative_part_le (g.weight i))
  · apply Finset.sum_le_sum
    intro i _
    split
    · exact part_le (g.weight i)
    · exact Nat.zero_le _
  · apply Finset.sum_le_sum
    intro i _
    split
    · exact negative_part_le (g.weight i)
    · exact Nat.zero_le _

theorem of_magnitude {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (w : Nat) (hw : 0 < w)
    (hm : g.target.natAbs + (∑ i, (g.weight i).natAbs) < 2^w) :
    (∀ x ∈ items live g y, natBitLength x.1.natAbs ≤ w) ∧
    positiveSum (items live g y) < 2^w ∧
    negSum (items live g y) < 2^w ∧
    natBitLength g.target.natAbs ≤ w ∧
    pPart g.target (liveSum (items live g y)) < 2^w ∧
    nPart g.target (selectedSum (items live g y)) < 2^w := by
  obtain ⟨hp,hn,hsp,hsn⟩ := score_bounds live g y
  have ht : natBitLength g.target.natAbs ≤ w :=
    CompactCacheCost.bit_bound g.target w hw (by omega)
  refine ⟨?_,by omega,by omega,ht,?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (g.weight j).natAbs)
      (Finset.mem_univ i)
    exact CompactCacheCost.bit_bound (g.weight i) w hw (by omega)
  · unfold pPart
    have := part_le g.target
    omega
  · unfold nPart
    have := negative_part_le g.target
    omega

theorem child_run {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail backing out : List Bool) (w C D E : Nat)
    (hw : 0 < w)
    (hm : g.target.natAbs + (∑ i, (g.weight i).natAbs) < 2^w)
    (hc : 8*w+12 ≤ C)
    (hD : C10NaturalHardwireScore.loopBudget (items live g y) w C ≤ D)
    (hE : C10NaturalHardwireWeights.loopBudget (C10NaturalHardwireWeights.gateItems g live) ≤ E) :
    ∃ result : Fin 48 → List Bool,
      Step HardwireChild.machine (HardwireChild.budget live g y w C)
        (HardwireChild.heads out 0 0) (HardwireChild.data live g y tail backing out w C D E)
        (HardwireChild.heads (out++exactWord (C10SupplierRowInput.hardwire live g y))
          (exactWord g).length q) result ∧
      result 0 = exactWord g++tail ∧
      result 34 = out++exactWord (C10SupplierRowInput.hardwire live g y) := by
  obtain ⟨hf,hp,hn,ht,hpt,hnt⟩ := of_magnitude live g y w hw hm
  exact HardwireChild.child_run live g y tail out w C D hf hc hp hn hD ht hpt hnt backing E hE

end NearCubicWires.P1Closure.HardwireBounds
