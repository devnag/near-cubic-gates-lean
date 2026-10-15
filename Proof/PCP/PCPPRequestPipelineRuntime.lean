import Proof.PCP.PCPPRequestRuntime

/-! A single polynomial pays the complete native-descriptor to canonical
request pipeline. Bounds use the already-produced node stream and its paid
runtime, while preserving the literal circuit and source input. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestRuntime
open LocalBitMultitape RepairRepresentation ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def massCoefficient := coldCoefficient+1
def listCoefficient := 1000000000000*massCoefficient^12+2*coldCoefficient+3
def pairWidthCoefficient := 3*massCoefficient^5+4
def codeCoefficient := listCoefficient+1000000000000000000+4294967296*pairWidthCoefficient^2+2
def inputCoefficient := 50*codeCoefficient+100

theorem mass_bound {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    PCPSerializerMass.mass (PCPPRequestCircuitNodes.fields nodes)+1 ≤
      massCoefficient*(parameter nodes suffix)^13 := by
  have hm := (mass_le_cold nodes suffix).trans (cold_bound nodes suffix)
  have hp : 1 ≤ (parameter nodes suffix)^13 := Nat.one_le_pow _ _ (by unfold parameter; omega)
  unfold massCoefficient
  nlinarith

theorem list_bound {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    PCPPRequestCircuitNodes.budget nodes suffix ≤ listCoefficient*(parameter nodes suffix)^156 := by
  let X := parameter nodes suffix
  have hpos : 1 ≤ X := by dsimp [X,parameter]; omega
  have hm := mass_bound nodes suffix
  have hc := cold_bound nodes suffix
  have hs : PCPTraversal.budget (PCPSerializerMass.mass (PCPPRequestCircuitNodes.fields nodes)) ≤
      1000000000000*massCoefficient^12*X^156 := by
    unfold PCPTraversal.budget
    calc
      _ ≤ 1000000000000*(massCoefficient*X^13)^12 := by gcongr
      _ = _ := by ring
  have hp : X^13 ≤ X^156 := Nat.pow_le_pow_right hpos (by decide)
  have hone : 1 ≤ X^156 := Nat.one_le_pow _ _ hpos
  have hc' := Nat.mul_le_mul_left coldCoefficient hp
  change PCPPRequestCircuitNodes.budget nodes suffix ≤ listCoefficient*X^156
  unfold PCPPRequestCircuitNodes.budget listCoefficient
  nlinarith

theorem index_width {n : ℕ} (c : BooleanCircuit n) :
    natBitLength c.output.val+1 ≤ parameter c.nodes (natWord c.output.val) := by
  unfold parameter PCPPRequestNodeGlobal.payload DecompositionInputCounts.word
  rw [frame_length]
  simp only [List.length_append,DecompositionSource.natWord_length]
  omega

theorem list_bits {n : ℕ} (c : BooleanCircuit n) :
    (encodeBalancedList (c.nodes.map encodeBooleanNode)).bits.length ≤
      3*massCoefficient^5*(parameter c.nodes (natWord c.output.val))^65 := by
  have hcode := PCPSerializerMass.code_bits (PCPPRequestCircuitNodes.fields c.nodes)
  have hval : PCPSerializerMass.values (PCPPRequestCircuitNodes.fields c.nodes)=
      c.nodes.map encodeBooleanNode := by
    simp only [PCPSerializerMass.values,PCPPRequestCircuitNodes.fields,List.map_map,
      Function.comp_def,CanonicalPositiveOutput.nat_bits_value]
  rw [hval] at hcode
  have hm := mass_bound c.nodes (natWord c.output.val)
  calc
    _ ≤ 3*(PCPSerializerMass.mass (PCPPRequestCircuitNodes.fields c.nodes)+1)^5 := hcode
    _ ≤ 3*(massCoefficient*(parameter c.nodes (natWord c.output.val))^13)^5 := by gcongr
    _ = _ := by ring

theorem code_bound {n : ℕ} (c : BooleanCircuit n) :
    PCPPRequestCircuitCode.budget c ≤ codeCoefficient*(parameter c.nodes (natWord c.output.val))^156 := by
  let X := parameter c.nodes (natWord c.output.val)
  let a := encodeBalancedList (c.nodes.map encodeBooleanNode)
  let b := encodeNat c.output.val
  have hpos : 1 ≤ X := by dsimp [X,parameter]; omega
  have hl := list_bound c.nodes (natWord c.output.val)
  have hi := index_width c
  have hn : PCPPRequestNatural.budget c.output.val ≤ 1000000000000000000*X^156 := by
    calc
      _ ≤ 1000000000000000000*(natBitLength c.output.val+1)^12 := PCPPRequestNatural.budget_envelope _
      _ ≤ 1000000000000000000*X^12 := by gcongr
      _ ≤ _ := Nat.mul_le_mul_left 1000000000000000000 (Nat.pow_le_pow_right hpos (show 12 ≤ 156 by decide))
  have ha : a.bits.length ≤ 3*massCoefficient^5*X^65 := list_bits c
  have hb : b.bits.length ≤ 3*X^65 := by
    calc
      _ ≤ 3*(natBitLength c.output.val+1)^5 := DecompositionAtom.magnitude_bits _
      _ ≤ 3*X^5 := by gcongr
      _ ≤ _ := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right hpos (show 5 ≤ 65 by decide))
  have hone : 1 ≤ X^65 := Nat.one_le_pow _ _ hpos
  have hw : a.bits.length+b.bits.length+1 ≤ pairWidthCoefficient*X^65 := by
    unfold pairWidthCoefficient
    nlinarith
  have ht : PCPPRequestCircuitTag.budget a b ≤ 4294967296*pairWidthCoefficient^2*X^156 := by
    have ht := PCPPRequestNodeDispatch.budget_quadratic a b 0 false
    change PCPPRequestNodeCode.unaryBudget a b+2 ≤ 4294967296*(a.bits.length+b.bits.length+0+1)^2 at ht
    calc
      _ ≤ 4294967296*(a.bits.length+b.bits.length+1)^2 := by
        unfold PCPPRequestCircuitTag.budget
        simpa only [Nat.add_zero,Nat.zero_add,Nat.add_comm] using ht
      _ ≤ 4294967296*(pairWidthCoefficient*X^65)^2 := by gcongr
      _ = 4294967296*pairWidthCoefficient^2*X^130 := by ring
      _ ≤ _ := Nat.mul_le_mul_left (4294967296*pairWidthCoefficient^2) (Nat.pow_le_pow_right hpos (show 130 ≤ 156 by decide))
  have hone' : 1 ≤ X^156 := Nat.one_le_pow _ _ hpos
  change PCPPRequestCircuitNodes.budget c.nodes (natWord c.output.val)+1+
    PCPPRequestNatural.budget c.output.val+1+PCPPRequestCircuitTag.budget a b ≤ codeCoefficient*X^156
  unfold codeCoefficient
  nlinarith

theorem code_bits_le_budget {n : ℕ} (c : BooleanCircuit n) :
    (encodeBooleanCircuit c).bits.length ≤ PCPPRequestCircuitCode.budget c := by
  obtain ⟨r,hr,_,_,hout,_,_,_,hs⟩ := PCPPRequestCircuitCode.code_run c
  have h := DecompositionSource.one_tape_support PCPPRequestCircuitCode.machine _ _ r
    PCPPRequestCircuitCode.rawSlot 0 hr (by rfl) (by rfl)
  rw [hout,Nat.zero_add] at h
  exact h.trans hs

theorem input_bound {n : ℕ} (c : BooleanCircuit n) :
    PCPPRequestInput.budget c ≤ inputCoefficient*(parameter c.nodes (natWord c.output.val))^156 := by
  let X := parameter c.nodes (natWord c.output.val)
  have hc := code_bound c
  have hb := (code_bits_le_budget c).trans hc
  have hn : natBitLength n ≤ X := by
    have hn : natBitLength n ≤ n+1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
    dsimp [X,parameter]
    omega
  have hpos : 1 ≤ X := by dsimp [X,parameter]; omega
  have hx : X ≤ X^156 := by simpa only [pow_one] using Nat.pow_le_pow_right hpos (show 1 ≤ 156 by decide)
  have hone : 1 ≤ X^156 := Nat.one_le_pow _ _ hpos
  change _ ≤ inputCoefficient*X^156
  unfold PCPPRequestInput.budget PCPPRequestCircuitReady.budget PCPPRequestWordFramed.budget PCPPRequestWord.budget inputCoefficient
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPRequestRuntime
