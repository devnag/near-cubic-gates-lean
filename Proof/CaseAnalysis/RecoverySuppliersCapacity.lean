import Proof.CaseAnalysis.RecoverySuppliersCount

/-! The existing W-driven capacity worker writes C, B and its log directly
to the literal prepared-bank ports. Its other work remains in the fresh bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def capacityMachine (k d : ℕ):=RecoveryFocus.machine (capacitySlots source k d) RecoveryCapacityDrivers.machine

theorem capacity_input (k d : ℕ) (word : List Bool) (W : ℕ) (A : Fin (tapes source k d)→List Bool)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→A (old source k d i)=[])
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→A i=input source k d word W i)
    (j : Fin 49) : A (capacitySlots source k d j)=RecoveryCapacityDrivers.input W j:=by
  by_cases h0 : j.val=0
  · simp only [capacitySlots,if_pos h0,RecoveryCapacityDrivers.input]
    exact (hfar (wPort source k d) (by rfl)).trans (input_w source k d word W)
  by_cases h7 : j.val=7
  · simp only [capacitySlots,if_neg h0,if_pos h7,RecoveryCapacityDrivers.input]
    exact hblank 154 (by decide) (by decide) (by decide)
  by_cases h45 : j.val=45
  · simp only [capacitySlots,if_neg h0,if_neg h7,if_pos h45,RecoveryCapacityDrivers.input]
    exact hblank 76 (by decide) (by decide) (by decide)
  by_cases h48 : j.val=48
  · simp only [capacitySlots,if_neg h0,if_neg h7,if_neg h45,if_pos h48,RecoveryCapacityDrivers.input]
    exact hblank 77 (by decide) (by decide) (by decide)
  · simp only [capacitySlots,if_neg h0,if_neg h7,if_neg h45,if_neg h48,RecoveryCapacityDrivers.input]
    have hj : base source k < (capacityWork source k d j).val:=by
      change base source k<base source k+1+j.val
      omega
    exact (hfar _ (Nat.le_of_lt hj)).trans (input_fresh source k d word W _ hj)

theorem capacity_heads (k d : ℕ) (H : Fin (tapes source k d)→ℕ)
    (hold : ∀ i : Fin 158,H (old source k d i)=0)
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→H i=0)
    (j : Fin 49) : H (capacitySlots source k d j)=0:=by
  dsimp only [capacitySlots]
  split_ifs
  · exact hfar (wPort source k d) (by rfl)
  · exact hold 154
  · exact hold 76
  · exact hold 77
  · exact hfar _ (by change base source k≤base source k+1+j.val;omega)

theorem capacity_run (k d : ℕ) (word : List Bool) (W : ℕ)
    (A : Fin (tapes source k d)→List Bool) (H : Fin (tapes source k d)→ℕ)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→A (old source k d i)=[])
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→A i=input source k d word W i)
    (hheads : ∀ i : Fin 158,H (old source k d i)=0)
    (hfarHeads : ∀ i : Fin (tapes source k d),base source k ≤ i.val→H i=0) :
    ∃ O r,runFrom (capacityMachine source k d) (RecoveryCapacityDrivers.budget W)
      ⟨(capacityMachine source k d).start,H,A⟩=some r ∧
      r.steps≤RecoveryCapacityDrivers.budget W ∧ r.final.heads=H ∧
      r.final.tapes=install (capacitySlots source k d) A O ∧
      O 0=List.replicate W true ∧ O 7=List.replicate (RecoveryCapacityDrivers.capacityC W) true ∧
      O 45=List.replicate (RecoveryCapacityDrivers.capacityB W) true ∧
      O 48=List.replicate (RecoveryCapacityDrivers.capacityB W+1) false:=by
  obtain ⟨O,ho,hW,hC,hB,_hScratch,hLog⟩:=RecoveryCapacityDrivers.run W
  obtain ⟨r,hr,hh,ht,hs⟩:=ho.focus_at (capacitySlots source k d) (capacity_injective source k d) H A
    (capacity_input source k d word W A hblank hfar) (capacity_heads source k d H hheads hfarHeads)
  exact ⟨O,r,hr,hs,hh,ht,hW,hC,hB,hLog⟩

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
