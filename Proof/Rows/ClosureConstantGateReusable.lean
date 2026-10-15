import Proof.Rows.ClosureConstantGate
import Proof.Rows.ClosureReusable48

/-! Complete reusable X/C frozen-gate field computation with a uniform
quadratic bound derived from the original retained description. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateReusable
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline
open VerifierDecoding SignedSortKey
open scoped BigOperators

variable {q : Nat} (live : Finset (Fin q)) (g : NormalizedThresholdGate q)
def C (w : Nat) := 8*w+12
def E (B q : Nat) := B+15*q+3
def R (B q w : Nat) := 1024*(B+q+w+1)^2
def budget (B q w : Nat) := 8192*(B+q+w+1)^2
noncomputable def A (tail backing : List Bool) (B w : Nat) (out : List Bool) :=
  ConstantGate.data (CloseoutRowsPoolMinimum.items g live) (g.threshold-1)
    tail backing out w (C w) 0 (E B q)
noncomputable def fields := CloseoutRowsPoolWeight.emitted (CloseoutRowsPoolMinimum.items g live)++
  intWord (g.threshold-1+CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g live))
noncomputable def machine := Reusable48.machine ConstantGate.machine

private theorem part_le (z : Int) : z.toNat≤z.natAbs := by cases z <;>simp
private theorem neg_le (z : Int) : (-z).toNat≤z.natAbs := by
  simpa only [Int.natAbs_neg] using part_le (-z)

theorem bounds (w : Nat) (hw : 0<w)
    (hm : (g.threshold-1).natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    (∀ x∈CloseoutRowsPoolMinimum.items g live,natBitLength x.1.natAbs≤w) ∧
    CloseoutRowsPoolMinimum.negSum (CloseoutRowsPoolMinimum.items g live)<2^w ∧
    natBitLength (g.threshold-1).natAbs≤w ∧
    C10NaturalHardwireTarget.pPart (g.threshold-1)
      (CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g live))<2^w ∧
    C10NaturalHardwireTarget.nPart (g.threshold-1) 0<2^w := by
  have hn : CloseoutRowsPoolMinimum.negSum (CloseoutRowsPoolMinimum.items g live)≤
      ∑ i,(g.weight i).natAbs := by
    simp only [CloseoutRowsPoolMinimum.negSum,CloseoutRowsPoolMinimum.items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    exact Finset.sum_le_sum (fun i _=>neg_le (g.weight i))
  have hs : CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g live)≤
      ∑ i,(g.weight i).natAbs := by
    simp only [CloseoutRowsPoolMinimum.liveSum,CloseoutRowsPoolMinimum.items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    apply Finset.sum_le_sum
    intro i _
    split
    · exact neg_le (g.weight i)
    · exact Nat.zero_le _
  refine ⟨?_,by omega,CompactCacheCost.bit_bound (g.threshold-1) w hw (by omega),?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    have hi := Finset.single_le_sum (fun j _=>Nat.zero_le (g.weight j).natAbs) (Finset.mem_univ i)
    exact CompactCacheCost.bit_bound (g.weight i) w hw (by omega)
  · unfold C10NaturalHardwireTarget.pPart
    have hp := part_le (g.threshold-1)
    omega
  · unfold C10NaturalHardwireTarget.nPart
    have hp := neg_le (g.threshold-1)
    omega

theorem weight_fit (tail : List Bool) (B : Nat)
    (hb : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g live)++intWord (g.threshold-1)++tail).length≤B) :
    CloseoutRowsPoolWeight.loopBudget (CloseoutRowsPoolMinimum.items g live)≤E B q := by
  simp only [CloseoutRowsPoolWeight.loopBudget,CloseoutRowsPoolMinimum.items_length,E]
  simp only [List.length_append] at hb
  omega

theorem worker_bound (tail : List Bool) (B w : Nat)
    (hb : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g live)++intWord (g.threshold-1)++tail).length≤B)
    (ht : natBitLength (g.threshold-1).natAbs≤w) :
    ConstantGate.budget (CloseoutRowsPoolMinimum.items g live) (g.threshold-1) w (C w)≤512*(B+q+w+1)^2 := by
  have he := weight_fit live g tail B hb
  have hz := C10NaturalHardwireTarget.budget_le (g.threshold-1) w ht
  simp only [ConstantGate.budget,ConstantGate.scoreTargetBudget,ConstantGate.scoreBudget,
    CloseoutRowsPoolMinimum.loopBudget,CloseoutRowsPoolMinimum.items_length,
    CloseoutRowsPoolMinimum.uniformBudget]
  unfold C E at *
  nlinarith

theorem masters_fit (tail backing : List Bool) (B w : Nat)
    (hb : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g live)++intWord (g.threshold-1)++tail).length≤B)
    (hk : backing.length≤B) :
    ∀ j,(Reusable48.masters (A live g tail backing B w) j).length≤R B q w := by
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hB : B≤R B q w := by unfold R;omega
  have hc : C w+1≤R B q w := by unfold C R;omega
  have he : E B q≤R B q w := by unfold E R;omega
  have hq : q+1≤R B q w := by unfold R;omega
  have hw : 2*w+1≤R B q w := by unfold R;omega
  have hs := hb.trans hB
  simp at hs
  have hback := hk.trans hB
  intro j
  fin_cases j <;>
    simp [Reusable48.masters,HardwireReusable.work,A,ConstantGate.data,HardwireChild.extra,
      C10NaturalHardwireScoreInputs.data,C10NaturalHardwireScoreInputs.extra,
      C10NaturalHardwireTarget.input,C10NaturalHardwireTarget.pairInput,C10NaturalHardwireTarget.pairExtra,
      C10NaturalHardwireTarget.extra,CloseoutRowsPoolMagnitude.input,
      CloseoutRowsPoolMinimum.items_length,CloseoutRowsPoolWeight.mask,
      Fin.addCases,MatrixScoreWeight.scalar,ZeroPadding.pad_length,
      frame_length,binary_length,List.length_replicate,CompareMachine.word,List.length_cons] <;>omega

theorem run (tail backing out : List Bool) (B w : Nat)
    (hb : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g live)++intWord (g.threshold-1)++tail).length≤B)
    (hk : backing.length≤B) (hw : 0<w)
    (hm : (g.threshold-1).natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    Step machine (budget B q w) (HardwireReusable.heads out 1)
      (Reusable48.input (A live g tail backing B w) out (R B q w))
      (HardwireReusable.heads (out++fields live g) 1)
      (Reusable48.input (A live g tail backing B w) (out++fields live g) (R B q w)) := by
  obtain ⟨hweights,hn,hz,hp,hneg⟩ := bounds live g w hw hm
  obtain ⟨result,hr,_hs,ho⟩ := ConstantGate.run (CloseoutRowsPoolMinimum.items g live) (g.threshold-1)
    tail backing out w (C w) 0 (E B q) hweights le_rfl hn hz hp hneg (weight_fit live g tail B hb)
  have cost := worker_bound live g tail B w hb hz
  have one : 1≤(B+q+w+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hR : ConstantGate.budget (CloseoutRowsPoolMinimum.items g live) (g.threshold-1) w (C w)+2≤R B q w := by
    unfold R;omega
  have h := Reusable48.run ConstantGate.machine (A live g tail backing B w) out
    (out++CloseoutRowsPoolWeight.emitted (CloseoutRowsPoolMinimum.items g live)++
      intWord (g.threshold-1+CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g live)))
    _ _ _ (R B q w) result
    (by intro a j;fin_cases j <;>rfl) (by intro a;rfl) hr ho
    (masters_fit live g tail backing B w hb hk) hR
  have hcost : 2*ConstantGate.budget (CloseoutRowsPoolMinimum.items g live) (g.threshold-1) w (C w)+4*R B q w+16≤budget B q w := by
    unfold R budget;omega
  simpa only [machine,fields,List.append_assoc] using h.enlarge hcost

end NearCubicWires.P1Closure.ConstantGateReusable
