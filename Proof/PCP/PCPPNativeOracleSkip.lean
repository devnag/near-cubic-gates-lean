import Proof.PCP.PCPPNativeQueryConjunction
import Proof.PCP.PCPPQueryFieldChain

/-! Skip exactly the three native natural fields of an original oracle
node. This uses their actual native codec and preserves the source tape. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleSkip
open LocalBitMultitape PCPPQueryField RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def node := Composition.machine (pair false) (PCPPQueryField.machine false)
def savedNode {r : ℕ} (v : BooleanNode r) (backing : List Bool) :=
  saved (PCPPRequestNodeSchema.fields v 2)
    (saved (PCPPRequestNodeSchema.fields v 1) (saved (PCPPRequestNodeSchema.fields v 0) backing))

theorem node_run {r : ℕ} (v : BooleanNode r) (pre tail backing out : List Bool) : ∃ result,
    runFrom node ((PCPPRequestNodeSchema.native v).length+8)
      (store (s := 12) 0 (pre++PCPPRequestNodeSchema.native v++tail) pre.length backing out)=some result ∧
    result.final=store (s := 12) 11 (pre++PCPPRequestNodeSchema.native v++tail)
      (pre.length+(PCPPRequestNodeSchema.native v).length) (savedNode v backing) out ∧
    result.steps=(PCPPRequestNodeSchema.native v).length+8 := by
  let a := PCPPRequestNodeSchema.fields v 0
  let b := PCPPRequestNodeSchema.fields v 1
  let c := PCPPRequestNodeSchema.fields v 2
  let source := pre++PCPPRequestNodeSchema.native v++tail
  obtain ⟨first,hfirst,ff,fs⟩ := pair_run false pre (natWord c++tail) backing out a b
  have hsource : pre++pairBits a b++(natWord c++tail)=source := by
    simp only [source,PCPPRequestNodeSchema.native,pairBits,fieldBits,a,b,c,List.append_assoc]
  rw [hsource] at hfirst ff
  simp only [selected,Bool.false_eq_true,ite_false,List.append_nil] at ff
  obtain ⟨last,hl,lf,ls⟩ := nat_run false (pre++pairBits a b) tail (saved b (saved a backing)) out c
  have hsource2 : (pre++pairBits a b)++natWord c++tail=source := by
    simp only [source,PCPPRequestNodeSchema.native,pairBits,fieldBits,a,b,c,List.append_assoc]
  rw [hsource2] at hl lf
  have hmid : Composition.restart first.final (PCPPQueryField.machine false).start=
      PCPPQueryField.cfg 0 source (pre++pairBits a b).length (saved b (saved a backing)) 0 out := by
    rw [ff,List.length_append]
    rfl
  rw [←hmid] at hl
  have joined := Composition.run_join (pair false) (PCPPQueryField.machine false) _ _ _ first last hfirst hl
  have hn : PCPPRequestNodeSchema.native v=pairBits a b++natWord c := rfl
  have htime : pairCost a b+1+(2*natBitLength c+3)=(PCPPRequestNodeSchema.native v).length+8 := by
    rw [hn]
    simp only [pairCost,fieldCost,pairBits,List.length_append,fieldBits_length,DecompositionSource.natWord_length]
    omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt first last,joined,?_,?_⟩
  · change Composition.rightConfig 8 last.final=_
    rw [lf]
    have hpos : (pre++pairBits a b).length+2*natBitLength c+1=
        pre.length+(PCPPRequestNodeSchema.native v).length := by
      rw [hn]
      simp only [List.length_append,DecompositionSource.natWord_length]
      omega
    simp only [selected,Bool.false_eq_true,ite_false,List.append_nil,hpos]
    rfl
  · change first.steps+1+last.steps=_
    rw [fs,ls]
    exact htime

end NearCubicWires.RepairOrdinary.PCPPNativeOracleSkip
