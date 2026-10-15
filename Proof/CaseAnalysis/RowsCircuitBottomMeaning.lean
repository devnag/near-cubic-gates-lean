import Proof.CaseAnalysis.RowsCircuitBottomTemplate

/-! Exact typed meanings of the executed bottom loop: all serialized
description, only retained threshold wires, and the same ordered native
requests expected by the original retained-top decomposition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
open LocalBitMultitape RadixSemantics CanonicalWitnessCodec SupplierPipeline
open CloseoutRowsCircuitBottom CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem map_range {α : Type} (f : ℕ→α) (n : ℕ) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val):=by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem total_fin (f : ℕ→ℕ) (initial n : ℕ) : total f initial n=initial+∑ i : Fin n,f i.val:=by
  rw [total,map_range,List.sum_ofFn]

theorem output_fin (f : ℕ→List Bool) (n : ℕ) :
    (List.range n).flatMap f=(List.finRange n).flatMap (fun i=>f i.val):=by
  rw [List.flatMap,map_range,List.ofFn_eq_map]
  rfl

theorem validity_true (core : ℕ) (words : List (List Bool)) :
    validity core true words words.length=true ↔
      ∀ bits∈words,(decodeSupportedNormalizedGate core (value bits)).isSome:=by
  simp only [validity,Bool.true_and,List.all_eq_true,passed,List.mem_range]
  constructor
  · intro h bits hb
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hb
    subst bits
    simpa only [List.getD_eq_getElem words [] hi] using h i hi
  · intro h i hi
    rw [List.getD_eq_getElem words [] hi]
    exact h _ (List.getElem_mem hi)

theorem choose_members {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    choose true (frame (gateMembers s)) 1 i.val=decide (i∈s):=by
  change readTapeBit (frame (gateMembers s)) (1+2*i.val)=_
  rw [Nat.add_comm 1,RecoveryColdPaddedCopy.frame_data]
  change (gateMembers s).getD i.val false=_
  simp [gateMembers,i.isLt]

theorem descriptions_typed {core n : ℕ} (g : Fin n→SupportedNormalizedGate core)
    (words : List (List Bool)) (initial : ℕ)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (g i)) :
    descriptions core words initial n=initial+2*(∑ i,(g i).descriptionBits)+n:=by
  rw [descriptions,total_fin]
  have he:∀ i : Fin n,descriptionCost core (words.getD i.val [])=2*(g i).descriptionBits+1:=by
    intro i
    simp only [descriptionCost,hd i,descriptionBytes]
    exact CloseoutRowsGateWeightLength.gate_description (g i)
  simp only [he,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,Nat.mul_one,Nat.add_assoc]

theorem symmetric_wires {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool)) (membership : List Bool) (memberPos initial : ℕ)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    wires false core memberPos membership words initial c.bottomCount=initial+c.wireCount:=by
  rw [wires,total_fin]
  simp only [wireCost,hd]
  simp [choose,kept,keptWires,NormalizedSymmetricThresholdCircuit.wireCount]

theorem threshold_wires {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool)) (initial : ℕ)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    wires true core 1 (frame (gateMembers c.top.support)) words initial c.bottomCount=initial+c.wireCount:=by
  rw [wires,total_fin]
  simp only [wireCost,hd,choose_members,keptWires,Nat.zero_add]
  simp [NormalizedThresholdThresholdCircuit.wireCount]

theorem symmetric_output {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool)) (membership : List Bool) (memberPos : ℕ)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (List.range c.bottomCount).flatMap (outputs false core memberPos membership words)=
      (List.ofFn c.bottom).flatMap (fun g=>frame (nativeWord g)):=by
  rw [output_fin,List.ofFn_eq_map,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  simp only [outputs,emitted,hd i]
  simp [choose,kept,keptOutput]

theorem threshold_output {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (List.range c.bottomCount).flatMap (outputs true core 1 (frame (gateMembers c.top.support)) words)=
      (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))).flatMap (fun g=>frame (nativeWord g)):=by
  rw [output_fin]
  have he:(List.finRange c.bottomCount).flatMap
      (fun i=>outputs true core 1 (frame (gateMembers c.top.support)) words i.val)=
      (List.finRange c.bottomCount).flatMap
        (fun i=>CloseoutRowsGateSupport.selected true (decide (i∈c.top.support)) (frame (nativeWord (c.bottom i)))):=by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _
    simp only [outputs,emitted,hd i,choose_members,keptOutput,List.nil_append]
    cases decide (i∈c.top.support) <;> simp [CloseoutRowsGateSupport.selected,keep,PCPPQueryField.selected]
  rw [he,selected_filter,sorted_members,←Finset.listMap_orderEmbOfFin_finRange c.top.support rfl]
  simp only [List.flatMap_map,List.ofFn_eq_map,retainedTopIndex]

theorem symmetric_description {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    descriptions core words 0 c.bottomCount+c.bottomCount+2=2*c.descriptionBits:=by
  rw [descriptions_typed c.bottom words 0 hd]
  simp only [NormalizedSymmetricThresholdCircuit.descriptionBits]
  omega

theorem threshold_description {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    descriptions core words 0 c.bottomCount+descriptionBytes c.top=
      2*c.descriptionBits+c.bottomCount+1:=by
  rw [descriptions_typed c.bottom words 0 hd]
  have ht:descriptionBytes c.top=2*c.top.descriptionBits+1:=CloseoutRowsGateWeightLength.gate_description c.top
  rw [ht]
  simp only [NormalizedThresholdThresholdCircuit.descriptionBits]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
