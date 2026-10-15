import Proof.CaseAnalysis.RowsGateSupportLoop
import Proof.Foundations.RepresentationSourceContracts

/-! The copied weights are the same supported gate, in its existing Fin
order. Retained top weights use precisely retainedTopIndex, the sorted
support map already fixed by the corrected decomposition source. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RadixSemantics SignedSortKey SupplierPipeline
open CloseoutRowsFamilyLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def intField (z : ℤ) : Bool×List Bool:=
  (decide (z<0),binary (natBitLength z.natAbs) z.natAbs)
def gateFields {n : ℕ} (g : NormalizedThresholdGate n):=List.ofFn (fun i=>intField (g.weight i))
def gateMembers {n : ℕ} (s : Finset (Fin n)):=List.ofFn (fun i=>decide (i∈s))

theorem intField_word (z : ℤ) : fieldWord (intField z)=RepairRepresentation.intWord z:=by
  simp only [fieldWord,intField,weightWord,binary_length,RepairRepresentation.intWord,WilliamsInputHeader.natWord_eq]
theorem intField_value (z : ℤ) : value (intField z).2=z.natAbs:=
  binary_value _ _ (Nat.lt_pow_succ_log_self (by decide) _)
theorem gateFields_word {n : ℕ} (g : NormalizedThresholdGate n) :
    (gateFields g).flatMap fieldWord=(List.ofFn g.weight).flatMap RepairRepresentation.intWord:=by
  simp only [gateFields,List.ofFn_eq_map,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  exact intField_word _

theorem gate_validity {n : ℕ} (g : SupportedNormalizedGate n) :
    validity (gateFields g.gate) (gateMembers g.support) true n=true:=by
  rw [validity_iff]
  refine ⟨rfl,?_⟩
  intro k hk hm
  have hf:(gateFields g.gate).getD k (false,[])=intField (g.gate.weight ⟨k,hk⟩):=by
    simp [gateFields,hk]
  have hs:(gateMembers g.support).getD k false=decide ((⟨k,hk⟩ : Fin n)∈g.support):=by
    simp [gateMembers,hk]
  rw [hs] at hm
  rw [hf,intField_value,g.zeroOutside _ (of_decide_eq_false hm)]
  rfl

theorem gate_emission {n : ℕ} (compressed : Bool) (g : NormalizedThresholdGate n) (s : Finset (Fin n)) :
    (List.range n).flatMap (emission compressed (gateFields g) (gateMembers s))=
      (List.finRange n).flatMap (fun i=>selected compressed (decide (i∈s)) (RepairRepresentation.intWord (g.weight i))):=by
  let paired:=List.ofFn (fun i : Fin n=>(intField (g.weight i),decide (i∈s)))
  let emit:=fun x : (Bool×List Bool)×Bool=>selected compressed x.2 (fieldWord x.1)
  have hl:paired.length=n:=List.length_ofFn
  have he:(List.range n).flatMap (emission compressed (gateFields g) (gateMembers s))=
      (List.range paired.length).flatMap (fun j=>emit (paired.getD j ((false,[]),false))):=by
    rw [hl]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j hj
    have hj':j<n:=List.mem_range.mp hj
    simp only [emission]
    rw [List.getD_eq_getElem _ _ (by simpa [gateMembers] using hj'),
      List.getD_eq_getElem _ _ (by simpa [gateFields] using hj'),
      List.getD_eq_getElem _ _ (by simpa [paired] using hj')]
    simp only [gateMembers,gateFields,paired,List.getElem_ofFn,emit]
  rw [he,flatMap_index paired ((false,[]),false) emit]
  simp only [paired,List.ofFn_eq_map,List.flatMap_map,emit]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  rw [intField_word]

theorem sorted_members {n : ℕ} (s : Finset (Fin n)) :
    (List.finRange n).filter (fun i=>decide (i∈s))=s.sort:=by
  exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT.eq_of_mem_iff s.sortedLT_sort (by simp)

theorem selected_filter {α : Type} (xs : List α) (p : α→Bool) (f : α→List Bool) :
    xs.flatMap (fun x=>selected true (p x) (f x))=(xs.filter p).flatMap f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.flatMap_cons]
    rw [ih]
    cases hx:p x <;> simp [selected,keep,PCPPQueryField.selected,hx]

theorem retained_weights {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) :
    (List.range c.bottomCount).flatMap (emission true (gateFields c.top.gate) (gateMembers c.top.support))=
      (List.ofFn (retainedTopGate c).weight).flatMap RepairRepresentation.intWord:=by
  rw [gate_emission,selected_filter,sorted_members]
  rw [←Finset.listMap_orderEmbOfFin_finRange c.top.support rfl]
  simp only [List.flatMap_map,List.ofFn_eq_map,retainedTopGate,retainedTopIndex]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
