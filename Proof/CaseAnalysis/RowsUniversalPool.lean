import Proof.CaseAnalysis.RawRowsChildren

/-! Appendix A.2's universal X/C pool for the actual ordinary decomposition.
The interleaved list is independent of the frozen column: both original and
constant gates are submitted to the same physical source batch. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open SupplierPipeline RepairRepresentation ThresholdCompiler
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {q : ℕ}

def constantSupportedGate (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    SupportedNormalizedGate q where
  gate:={
    weight:=fun i=>if i∈live then 0 else g.gate.weight i
    threshold:=g.gate.threshold-minimumLiveScore g.gate live}
  support:=g.support\live
  zeroOutside:=by
    intro i hi
    change (if i∈live then 0 else g.gate.weight i)=0
    by_cases h:i∈live
    · exact if_pos h
    · rw [if_neg h]
      exact g.zeroOutside i (by intro hg; exact hi (Finset.mem_sdiff.mpr ⟨hg,h⟩))

@[simp] theorem constant_weight (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (i : Fin q) :
    (constantSupportedGate live g).gate.weight i=if i∈live then 0 else g.gate.weight i:=rfl
@[simp] theorem constant_threshold (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (constantSupportedGate live g).gate.threshold=g.gate.threshold-minimumLiveScore g.gate live:=rfl
@[simp] theorem constant_eval (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (x : BitInput q) :
    (constantSupportedGate live g).eval x=residualConstant g.gate live x:=by
  have hs : (∑ i,(constantSupportedGate live g).gate.weight i*bitInt (x i))=
      frozenScore g.gate live x:=by
    unfold frozenScore
    calc
      _=∑ i∈Finset.univ.filter (fun i : Fin q=>i∉live),g.gate.weight i*bitInt (x i):=by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi:i∈live <;> simp [constant_weight,hi]
      _=∑ i∈Finset.univ\live,g.gate.weight i*bitInt (x i):=by
        congr 1
        ext i
        simp
  unfold SupportedNormalizedGate.eval NormalizedThresholdGate.eval residualConstant
  rw [CompilerSemantics.normalizedScore_eq_bitInt,hs]
  rfl

theorem constant_wires (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (constantSupportedGate live g).wireCount≤g.wireCount:=
  Finset.card_le_card Finset.sdiff_subset

theorem constant_untouched (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    Disjoint (constantSupportedGate live g).support live:=Finset.sdiff_disjoint

def pool (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) :=
  occ.flatMap (fun g=>[g,constantSupportedGate live g])

@[simp] theorem pool_length (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) :
    (pool live occ).length=2*occ.length:=by
  induction occ with
  | nil=>rfl
  | cons g occ ih=>simp only [pool,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

theorem pool_original (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (i : ℕ) (hi : i<occ.length) :
    (pool live occ)[2*i]'(by rw [pool_length];omega)=occ[i]:=by
  induction occ generalizing i with
  | nil=>simp at hi
  | cons g occ ih=>
    cases i with
    | zero=>rfl
    | succ i=>simpa only [pool,List.flatMap_cons,List.cons_append,List.nil_append,Nat.mul_succ,List.getElem_cons_succ]
        using ih i (by simpa using hi)

theorem pool_constant (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (i : ℕ) (hi : i<occ.length) :
    (pool live occ)[2*i+1]'(by rw [pool_length];omega)=constantSupportedGate live occ[i]:=by
  induction occ generalizing i with
  | nil=>simp at hi
  | cons g occ ih=>
    cases i with
    | zero=>rfl
    | succ i=>simpa only [pool,List.flatMap_cons,List.cons_append,List.nil_append,Nat.mul_succ,Nat.add_assoc,List.getElem_cons_succ]
        using ih i (by simpa using hi)

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
