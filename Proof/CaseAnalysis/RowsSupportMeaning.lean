import Proof.CaseAnalysis.RowsSupportLoop
import Proof.CaseAnalysis.RowsCircuitBottomMeaning

/-! The retained support stream has exactly the native stream's original
carrier order, including declared zero-weight incidences and THR selection. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsGateSupport CloseoutRowsCircuitBottomLoop CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportWord {q : ℕ} (gates : List (SupportedNormalizedGate q)):=
  gates.flatMap (fun g=>frame (gateMembers g.support))

theorem supportWord_length {q : ℕ} (gates : List (SupportedNormalizedGate q)) :
    (supportWord gates).length=gates.length*(2*q+1) := by
  induction gates with
  | nil=>simp [supportWord]
  | cons g gs ih=>
    have hg:(gateMembers g.support).length=q:=List.length_ofFn
    simp only [supportWord,List.flatMap_cons,List.length_append,frame_length,hg,List.length_cons] at *
    rw [ih,Nat.add_mul,Nat.one_mul]
    omega

theorem support_symmetric {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool)) (membership : List Bool) (memberPos : ℕ)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (List.range c.bottomCount).flatMap (supportOutput false core memberPos membership words)=
      supportWord (List.ofFn c.bottom) := by
  rw [output_fin]
  simp only [supportWord,List.ofFn_eq_map,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  simp only [supportOutput,supportEmitted,hd i]
  simp [choose,kept]

theorem support_threshold {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (List.range c.bottomCount).flatMap (supportOutput true core 1 (frame (gateMembers c.top.support)) words)=
      supportWord (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))) := by
  rw [output_fin]
  have he:(List.finRange c.bottomCount).flatMap
      (fun i=>supportOutput true core 1 (frame (gateMembers c.top.support)) words i.val)=
      (List.finRange c.bottomCount).flatMap
        (fun i=>CloseoutRowsGateSupport.selected true (decide (i∈c.top.support))
          (frame (gateMembers (c.bottom i).support))):=by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _
    simp only [supportOutput,supportEmitted,hd i,choose_members]
    cases decide (i∈c.top.support) <;> simp [CloseoutRowsGateSupport.selected,keep,PCPPQueryField.selected]
  rw [he,selected_filter,sorted_members,←Finset.listMap_orderEmbOfFin_finRange c.top.support rfl]
  simp only [supportWord,List.flatMap_map,List.ofFn_eq_map,retainedTopIndex]

theorem supportEmitted_length (q : ℕ) (keep : Bool) (bits : List Bool) :
    (supportEmitted q keep bits).length≤2*q+1 := by
  unfold supportEmitted
  split
  · simp
  · rename_i g _
    have hg:(gateMembers g.support).length=q:=List.length_ofFn
    split_ifs <;> simp only [frame_length,hg,List.length_nil] <;> omega

theorem supportPrefix_length (threshold : Bool) (q memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (initial : List Bool) (j : ℕ) :
    (supportPrefix threshold q memberPos membership words initial j).length ≤ initial.length+j*(2*q+1) := by
  induction j with
  | zero=>simp [supportPrefix]
  | succ j ih=>
    rw [supportPrefix_succ,List.length_append]
    have hj:=supportEmitted_length q (choose threshold membership memberPos j) (words.getD j [])
    change (supportPrefix threshold q memberPos membership words initial j).length+
      (supportEmitted q (choose threshold membership memberPos j) (words.getD j [])).length≤_
    rw [Nat.add_mul,Nat.one_mul]
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
