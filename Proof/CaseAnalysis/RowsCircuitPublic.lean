import Proof.CaseAnalysis.RowsCircuitSupport

/-! Original cold public fields at the common circuit ABI. Domain and
policy words are retained; the two literal guards come from the paid seed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem unchanged (C core W L : ℕ) (bits out : List Bool) (bank : Fin 639 → List Bool)
    (i : Fin 1703) (hi : 639 ≤ i.val) (ht : i≠640)
    (hs : ∀ j,seedSlots j≠i) (ha : ∀ j,CloseoutRowsCircuitAllocate.slots j≠i) :
    output C core W L bits out bank i=input C core W L bits out i:=by
  rw [output,Function.update_of_ne ht,framed_other _ _ _ _ _ _ _ _ hi,
    seeded_other _ _ _ _ _ _ _ hs,allocated_other _ _ _ _ _ _ _ ha]

theorem verdict_unallocated : ∀ j,CloseoutRowsCircuitAllocate.slots j≠(1700 : Fin 1703):=by
  intro j
  refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ j
  · intro k
    rw [CloseoutRowsCircuitAllocate.slots_old]
    refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ k
    · intro h he
      rw [CloseoutRowsCircuitAllocate.scratch_old] at he
      have hv:=congrArg Fin.val he
      have range:=CloseoutRowsCircuitAllocate.gate_range h
      change (CloseoutRowsCircuitAllocate.gate h).val=1700 at hv
      omega
    · intro h
      rw [CloseoutRowsCircuitAllocate.scratch_new]
      fin_cases h <;> decide
  · intro k
    rw [CloseoutRowsCircuitAllocate.slots_new]
    fin_cases k <;> decide

theorem public_fields (C core W L : ℕ) (bits out : List Bool) (bank : Fin 639 → List Bool) :
    ∀ i : Fin 8,output C core W L bits out bank (![1674,1688,1690,1693,1697,1698,1699,1700] i)=
      (![UnaryTemplate.tape core,out,[],[true],ZeroPadding.pad C [true],List.replicate W true,
        List.replicate L true,[]] : Fin 8 → List Bool) i:=by
  intro i;fin_cases i
  · exact unchanged C core W L bits out bank 1674 (by decide) (by decide) (by decide)
      (untouched 1674 (by decide))
  · exact unchanged C core W L bits out bank 1688 (by decide) (by decide) (by decide)
      (untouched 1688 (by decide))
  · exact unchanged C core W L bits out bank 1690 (by decide) (by decide) (by decide)
      (untouched 1690 (by decide))
  · change output C core W L bits out bank 1693=[true]
    rw [output,Function.update_of_ne (by decide),framed_other _ _ _ _ _ _ _ _ (by decide)]
    exact install_slot seedSlots (by decide) _ _ 1
  · change output C core W L bits out bank 1697=ZeroPadding.pad C [true]
    rw [output,Function.update_of_ne (by decide),framed_other _ _ _ _ _ _ _ _ (by decide)]
    exact install_slot seedSlots (by decide) _ _ 2
  · exact unchanged C core W L bits out bank 1698 (by decide) (by decide) (by decide)
      (untouched 1698 (by decide))
  · exact unchanged C core W L bits out bank 1699 (by decide) (by decide) (by decide)
      (untouched 1699 (by decide))
  · exact unchanged C core W L bits out bank 1700 (by decide) (by decide) (by decide) verdict_unallocated

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
