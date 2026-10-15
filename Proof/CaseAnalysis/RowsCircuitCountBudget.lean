import Proof.CaseAnalysis.RowsCircuitCount

/-! The complete list/count guard agrees with the public decoders on all
raw inputs. Its driver is bounded by the original field widths. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCount
open LocalBitMultitape RadixSemantics CloseoutWitness PCPPNativeCanonicalTree
open CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (bottom declared : List Bool):=
  34000000000000000000*(bottom.length+declared.length+2)^24

theorem count_bound (bits : List Bool) : count bits ≤ bits.length+1:=by
  simpa only [count,TraversalCounted.count] using Reencode.count_bound bits

theorem bits_bound (n : ℕ) : (CloseoutRowsCountBinary.bits n).length ≤ n+1:=by
  by_cases hn:n=0
  · simp [CloseoutRowsCountBinary.bits,hn]
  · simp only [CloseoutRowsCountBinary.bits,if_neg hn,SignedSortKey.binary_length]
    exact Nat.add_le_add_right (Nat.log_le_self _ _) 1

theorem time_bound (bottom declared : List Bool) : time bottom declared ≤ budget bottom declared:=by
  let X:=bottom.length+declared.length+2
  have hcount:=count_bound bottom
  have hpayload:(BitFields.payload declared).length ≤ declared.length+1:=by
    simpa only [BitFields.payload,Reencode.fields,List.length_map,TraversalCounted.count]
      using Reencode.count_bound declared
  have hbits:=bits_bound (count bottom)
  have hc:count bottom ≤ X:=by dsimp [X];omega
  have hm:max (BitFields.payload declared).length (CloseoutRowsCountBinary.bits (count bottom)).length ≤ X:=by
    dsimp [X];omega
  have h1:1 ≤ X^24:=Nat.one_le_pow _ _ (by dsimp [X];omega)
  have hx:X ≤ X^24:=Nat.le_self_pow (by decide) _
  have hsq:(count bottom)^2 ≤ X^24:=(Nat.pow_le_pow_left hc 2).trans
    (Nat.pow_le_pow_right (by dsimp [X];omega) (by decide : 2 ≤ 24))
  have hb:(bottom.length+1)^24 ≤ X^24:=Nat.pow_le_pow_left (by dsimp [X];omega) 24
  have hd:(declared.length+1)^24 ≤ X^24:=Nat.pow_le_pow_left (by dsimp [X];omega) 24
  change time bottom declared ≤ 34000000000000000000*X^24
  unfold time CanonicalTest.budget Reencode.polynomialBudget NatCold.budget CloseoutRowsCountWord.budget
  omega

theorem decision_exact (bottom declared : List Bool) :
    ((∃ values,encodeBalancedList values=value bottom) ∧ decodeNat (value declared)=some (count bottom)) ↔
      ∃ values,decodeBalancedList (value bottom)=some values ∧
        decodeNat (value declared)=some values.length:=by
  constructor
  · rintro ⟨⟨values,hv⟩,hn⟩
    refine ⟨values,?_,?_⟩
    · rw [←hv,decodeBalancedList_encode]
    · simpa only [count,←hv,tree_atoms] using hn
  · rintro ⟨values,hv,hn⟩
    have he:=encodeBalancedList_of_decode hv
    refine ⟨⟨values,he⟩,?_⟩
    simpa only [count,←he,tree_atoms] using hn

theorem public_run (bottom declared : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget bottom declared) (input bottom declared) out ∧
      out 30=PCPPNativeCanonicalWalk.atomStream bottom.length (tree (value bottom)).atoms ∧
      out 356=List.replicate (count bottom) true ∧ out 358=UnaryTemplate.tape (count bottom) ∧
      (readTapeBit (out 367) 0=true ↔ ∃ values,
        decodeBalancedList (value bottom)=some values ∧ decodeNat (value declared)=some values.length):=by
  obtain ⟨out,h,hs,hr,ht,hf⟩:=count_run bottom declared
  exact ⟨out,ClockJoin.enlarge machine _ _ _ _ h (time_bound bottom declared),hs,hr,ht,
    hf.trans (decision_exact bottom declared)⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCount
