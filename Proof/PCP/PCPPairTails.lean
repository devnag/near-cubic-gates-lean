import Proof.PCP.PCPPairStages

/-! The actual add/return tails after the selected square. Both branches
write the same designated pair-result tape, with no unexecuted arithmetic. -/
namespace NearCubicWires.RepairOrdinary.PCPPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem left_tail (left right : List Bool) (tapes : Fin 30 → List Bool)
    (h0 : tapes 0=input left right 0) (h1 : tapes 1=input left right 1)
    (h10 : tapes 10=frame (binary (width left right) (value left*value left)))
    (hfresh : ∀ i : Fin 30,21 ≤ i.val → tapes i=[])
    (hbranch : value right ≤ value left) :
    ∃ out : Fin 30 → List Bool,
      Timed machine (8*width left right+10)
        (controlConfig (RecoveryCalls.code sizes 3) (initialConfiguration (programs 3) tapes))
        (RecoveryCalls.stopped sizes (fun _ => 0) out) ∧
      out 26=frame (binary (width left right) (Nat.pair (value left) (value right))) := by
  have hfit := (square_bounds left right).2.2.1
  have hfirst := HierarchyBinary.add_ready (width left right) (value left*value left)
    (value left) 0 [] (by omega) (by simp)
  simp only [max_eq_right (Nat.zero_le _)] at hfirst
  let middle := install firstAddSlots tapes
    ![frame (binary (width left right) (value left*value left)),
      frame (binary (width left right) (value left)),
      frame (binary (width left right) (value left*value left+value left)),
      List.replicate (2*width left right+1) false]
  have hfirstRun : ReadyRun (programs 3) (4*width left right+4) tapes middle :=
    hfirst.focus firstAddSlots firstAdd_injective tapes (by
      intro j
      fin_cases j
      · exact h10
      · exact h0
      · exact hfresh 21 (by decide)
      · exact hfresh 22 (by decide))
  have hsecond := HierarchyBinary.add_ready (width left right)
    (value left*value left+value left) (value right) 0 [] hfit (by simp)
  simp only [max_eq_right (Nat.zero_le _)] at hsecond
  have hsecondRun := hsecond.focus secondAddSlots secondAdd_injective middle (by
    intro j
    fin_cases j
    · exact install_slot firstAddSlots firstAdd_injective _ _ 2
    · exact (install_other firstAddSlots _ _ 1 (by decide)).trans h1
    · exact (install_other firstAddSlots _ _ 26 (by decide)).trans (hfresh 26 (by decide))
    · exact (install_other firstAddSlots _ _ 27 (by decide)).trans (hfresh 27 (by decide)))
  have hsecondRun' : ReadyRun (programs 4) (4*width left right+4) middle _ := hsecondRun
  have ht := (hfirstRun.call sizes programs 0 next 3 4 (by intro q; rfl)).trans
    (hsecondRun'.stop sizes programs 0 next 4 (by intro q; rfl))
  have he : 4*width left right+4+1+(4*width left right+4+1)=8*width left right+10 := by omega
  rw [he] at ht
  refine ⟨_,ht,?_⟩
  have ho := install_slot secondAddSlots secondAdd_injective middle
    ![frame (binary (width left right) (value left*value left+value left)),
      frame (binary (width left right) (value right)),
      frame (binary (width left right) (value left*value left+value left+value right)),
      List.replicate (2*width left right+1) false] 2
  rw [pair_formula,if_pos hbranch]
  exact ho

theorem right_tail (left right : List Bool) (tapes : Fin 30 → List Bool)
    (h0 : tapes 0=input left right 0)
    (h10 : tapes 10=frame (binary (width left right) (value right*value right)))
    (hfresh : ∀ i : Fin 30,21 ≤ i.val → tapes i=[])
    (hbranch : ¬value right ≤ value left) :
    ∃ out : Fin 30 → List Bool,
      Timed machine (4*width left right+5)
        (controlConfig (RecoveryCalls.code sizes 6) (initialConfiguration (programs 6) tapes))
        (RecoveryCalls.stopped sizes (fun _ => 0) out) ∧
      out 26=frame (binary (width left right) (Nat.pair (value left) (value right))) := by
  have hfit := (square_bounds left right).2.2.2
  have hadd := HierarchyBinary.add_ready (width left right) (value right*value right)
    (value left) 0 [] (by omega) (by simp)
  simp only [max_eq_right (Nat.zero_le _)] at hadd
  have hrun : ReadyRun (programs 6) (4*width left right+4) tapes _ :=
    hadd.focus rightAddSlots rightAdd_injective tapes (by
      intro j
      fin_cases j
      · exact h10
      · exact h0
      · exact hfresh 26 (by decide)
      · exact hfresh 27 (by decide))
  have ht := hrun.stop sizes programs 0 next 6 (by intro q; rfl)
  refine ⟨_,ht,?_⟩
  have ho := install_slot rightAddSlots rightAdd_injective tapes
    ![frame (binary (width left right) (value right*value right)),
      frame (binary (width left right) (value left)),
      frame (binary (width left right) (value right*value right+value left)),
      List.replicate (2*width left right+1) false] 2
  rw [pair_formula,if_neg hbranch]
  exact ho

end NearCubicWires.RepairOrdinary.PCPPair
