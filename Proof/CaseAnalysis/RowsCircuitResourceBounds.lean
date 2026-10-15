import Proof.CaseAnalysis.RowsCircuitSymmetricTop

/-! Actual metadata sizes, independent of the expensive parser clock.
These cubic bounds pay the two final cursor returns with the same capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceBounds
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsCircuitBottom CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counterBound (N : ℕ) := 64*(N+2)^2+1

theorem gate_counters {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (hd : decodeSupportedNormalizedGate n (value bits)=some g) :
    ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length ≤ counterBound bits.length ∧
      (RepairRepresentation.natWord g.gate.threshold.natAbs).length ≤ counterBound bits.length ∧
      g.wireCount ≤ counterBound bits.length := by
  obtain ⟨out,⟨r,hr,rt,_rh,rs⟩,hw,ht,hc⟩ := CloseoutRowsGateMetadata.gate_run g bits hd
  have bound (i : Fin 15) (hi : i=6 ∨ i=11 ∨ i=13) : (out i).length ≤ counterBound bits.length := by
    have h := PCPSerializerReuse.tape_support CloseoutRowsGateMetadata.machine _ _ r hr i 0 0 (by rfl)
      (by rcases hi with rfl|rfl|rfl <;> change 0 ≤ 1 <;> decide)
    rw [rt] at h
    unfold counterBound
    exact h.trans (by omega)
  have w := bound 6 (Or.inl rfl)
  have t := bound 11 (Or.inr (Or.inl rfl))
  have c := bound 13 (Or.inr (Or.inr rfl))
  rw [hw,List.length_replicate] at w
  rw [ht,List.length_replicate] at t
  rw [hc,List.length_replicate] at c
  exact ⟨w,t,c⟩

theorem costs_bound (core N : ℕ) (keep : Bool) (bits : List Bool) (hn : bits.length ≤ N) :
    descriptionCost core bits ≤ 2*counterBound N ∧ wireCost core keep bits ≤ counterBound N+1 := by
  have mono : counterBound bits.length ≤ counterBound N := by
    unfold counterBound
    have h := Nat.pow_le_pow_left (by omega : bits.length+2 ≤ N+2) 2
    omega
  cases hd : decodeSupportedNormalizedGate core (value bits) with
  | none => simp [descriptionCost,wireCost,hd]
  | some g =>
    obtain ⟨hw,ht,hc⟩ := gate_counters g bits hd
    simp only [descriptionCost,wireCost,hd,descriptionBytes]
    constructor
    · simpa only [two_mul] using Nat.add_le_add (hw.trans mono) (ht.trans mono)
    · cases keep
      · exact Nat.zero_le _
      · simpa [keptWires] using Nat.add_le_add_right (hc.trans mono) 1

theorem total_bound (cost : ℕ→ℕ) (initial count B : ℕ) (hb : ∀ j<count,cost j ≤ B) :
    total cost initial count ≤ initial+count*B := by
  induction count with
  | zero => simp [total]
  | succ count ih =>
    rw [total_succ]
    have h := ih (fun j hj => hb j (by omega))
    have hn := hb count (by omega)
    nlinarith

theorem cubic (N : ℕ) : (N+2)*(2*counterBound N+2) ≤ 132*(N+2)^3 := by
  unfold counterBound
  nlinarith

theorem allraw_totals (threshold : Bool) (core N memberPos initial count : ℕ)
    (membership : List Bool) (words : List (List Bool))
    (hlen : words.length ≤ N+1) (hwords : ∀ bits∈words,bits.length ≤ N)
    (hi : initial ≤ 2*counterBound N) (hc : count ≤ words.length) :
    descriptions core words initial count ≤ 132*(N+2)^3 ∧
      wires threshold core memberPos membership words 0 count ≤ 132*(N+2)^3 := by
  have each (j : ℕ) (hj : j<count) := costs_bound core N (choose threshold membership memberPos j)
    (words.getD j []) (hwords _ (by rw [List.getD_eq_getElem words [] (by omega)];exact List.getElem_mem _))
  have hd := total_bound (fun j=>descriptionCost core (words.getD j [])) initial count (2*counterBound N)
    (fun j hj => (each j hj).1)
  have hw := total_bound (fun j=>wireCost core (choose threshold membership memberPos j) (words.getD j []))
    0 count (counterBound N+1) (fun j hj => (each j hj).2)
  have hbound := cubic N
  have hcount : count ≤ N+1 := hc.trans hlen
  have pd := Nat.mul_le_mul_right (2*counterBound N) hcount
  have pw := Nat.mul_le_mul_right (counterBound N+1) hcount
  change total _ initial count ≤ _ ∧ total _ 0 count ≤ _
  constructor <;> nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceBounds
