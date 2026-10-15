import Proof.PCP.PCPTraversalTagLoad

/-! The two actual canonical pair calls after both recursive children have
returned. These are nodes21→9 of the one fixed traversal controller. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem working_bank_heads {heads : Fin 128 → ℕ} (hh : WorkingHeads heads) : ∀ i,heads (bank i)=0 := by
  intro i
  apply hh
  · simp only [bank]; omega
  · exact bank_ne i 80 (by decide)
  · exact bank_ne i 81 (by decide)
  · exact bank_ne i 82 (by decide)
theorem working_pair_heads {heads : Fin 128 → ℕ} (hh : WorkingHeads heads) : ∀ i,heads (pairSlots i)=0 := by
  intro i
  apply hh
  · simp only [pairSlots]; split; decide; split; decide; simp only [bank]; omega
  · exact pair_ne i 80 (by decide) (by decide) (by decide)
  · exact pair_ne i 81 (by decide) (by decide) (by decide)
  · exact pair_ne i 82 (by decide) (by decide) (by decide)
theorem working_result_heads {heads : Fin 128 → ℕ} (hh : WorkingHeads heads) : ∀ i,heads (resultCopySlots i)=0 := by
  intro i
  fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide)

noncomputable def combinedInner (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first : Fin 38 → List Bool) :=
  pairResult cap (max log (cap+1)) (Nat.pair (value left) (value right)).bits
    (combineLoaded left right pre cap z log ambient) first
noncomputable def combinedTag (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first : Fin 38 → List Bool) :=
  tagLoaded (Nat.pair (value left) (value right)).bits cap (max log (cap+1))
    (combinedInner left right pre cap z log ambient first)
noncomputable def combinedOutput (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first second : Fin 38 → List Bool) :=
  pairResult cap (max log (cap+1)) (Nat.pair 2 (Nat.pair (value left) (value right))).bits
    (combinedTag left right pre cap z log ambient first) second

theorem combine_path (left right pre : List Bool) (cap z log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 5≤cap) (hl : 2*left.length+2≤cap) (hr : 2*right.length+1≤cap)
    (hpos : 0<Nat.pair (value left) (value right))
    (hpair : PCPPairCanonical.budget left right+1≤cap)
    (htag : PCPPairCanonical.budget (2 : ℕ).bits (Nat.pair (value left) (value right)).bits+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hstack : ambient 82=pre++(frame left).reverse++List.replicate z false)
    (hstackHead : heads 82=pre.length+2*left.length+1)
    (hright : ambient 77=ZeroPadding.pad cap (frame right)) (hhd : heads 28=0) :
    ∃ first second : Fin 38 → List Bool,
      Path 21 9 (24*cap+72) heads ambient (installedHeads leftPopSlots heads ![pre.length,0,0])
        (combinedOutput left right pre cap z log ambient first second) ∧
      WorkBound cap (combinedOutput left right pre cap z log ambient first second) ∧
      WorkingHeads (installedHeads leftPopSlots heads ![pre.length,0,0]) := by
  let loaded := combineLoaded left right pre cap z log ambient
  let moved := installedHeads leftPopSlots heads ![pre.length,0,0]
  let code := Nat.pair (value left) (value right)
  obtain ⟨hload,loadBound,loadHeads⟩ := combine_load_path left right pre cap z log heads ambient
    hl hr hb hh hdriver hlog hstack hstackHead hright hhd
  have moved_driver : moved 28=0 := (installedHeads_other leftPopSlots heads _ 28 (by decide)).trans hhd
  obtain ⟨first,hinner,_,_,innerBound⟩ := pair_result_calls 24 25 26 27 28 rfl rfl rfl rfl
    (by intro q scanned; simp [next]) (by intro q scanned; simp [next])
    (by intro q scanned; simp [next]) (by intro q scanned; simp [next])
    cap (max log (cap+1)) left right moved loaded hpos hpair loadBound
    (combine_loaded_driver left right pre cap z log ambient) (combine_loaded_log left right pre cap z log ambient)
    (combine_loaded_operands left right pre cap z log ambient).1
    (combine_loaded_operands left right pre cap z log ambient).2
    (working_bank_heads loadHeads) (working_pair_heads loadHeads) (working_result_heads loadHeads)
    moved_driver (loadHeads 127 (by decide) (by decide) (by decide) (by decide))
  let inner := combinedInner left right pre cap z log ambient first
  have inner_field : inner 77=ZeroPadding.pad cap (frame code.bits) :=
    copiedResult_result cap (max (max log (cap+1)) (cap+1)) code.bits
      (paired cap (max log (cap+1)) loaded first)
  have inner_width : 2*code.bits.length+1≤cap := by
    have h := innerBound 77 (by decide) (by decide)
    change (inner 77).length≤cap at h
    rw [inner_field,ZeroPadding.pad_length,frame_length] at h
    omega
  have inner_log : inner 127=List.replicate (max log (cap+1)) false := by
    have h := pairResult_log cap (max log (cap+1)) code.bits loaded first
    rw [max_eq_left (le_max_right log (cap+1))] at h
    exact h
  obtain ⟨htagload,tagBound⟩ := tag_load_path code.bits cap (max log (cap+1)) moved inner hc inner_width
    innerBound loadHeads (pairResult_driver cap (max log (cap+1)) code.bits loaded first)
    inner_log inner_field moved_driver
  let tagged := combinedTag left right pre cap z log ambient first
  have tag_log : tagged 127=List.replicate (max log (cap+1)) false := by
    have h := tag_loaded_log code.bits cap (max log (cap+1)) inner
    rw [max_eq_left (le_max_right log (cap+1))] at h
    exact h
  have htagpos : 0<Nat.pair (value (2 : ℕ).bits) (value code.bits) := by
    change 0<Nat.pair 2 (value code.bits)
    unfold Nat.pair
    split <;> omega
  obtain ⟨second,hfinish,_,_,finishBound⟩ := pair_result_calls 31 32 33 34 9 rfl rfl rfl rfl
    (by intro q scanned; simp [next]) (by intro q scanned; simp [next])
    (by intro q scanned; simp [next]) (by intro q scanned; simp [next])
    cap (max log (cap+1)) (2 : ℕ).bits code.bits moved tagged htagpos htag tagBound
    (tag_loaded_driver code.bits cap (max log (cap+1)) inner) tag_log
    (tag_loaded_operands code.bits cap (max log (cap+1)) inner).1
    (tag_loaded_operands code.bits cap (max log (cap+1)) inner).2
    (working_bank_heads loadHeads) (working_pair_heads loadHeads) (working_result_heads loadHeads)
    moved_driver (loadHeads 127 (by decide) (by decide) (by decide) (by decide))
  rw [CanonicalPositiveOutput.nat_bits_value,CanonicalPositiveOutput.nat_bits_value] at hfinish finishBound
  have hpath := ((hload.trans hinner).trans htagload).trans hfinish
  refine ⟨first,second,hpath.mono ?_,finishBound,loadHeads⟩
  omega

theorem combined_result (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first second : Fin 38 → List Bool) :
    combinedOutput left right pre cap z log ambient first second 77=
      ZeroPadding.pad cap (frame (Nat.pair 2 (Nat.pair (value left) (value right))).bits) :=
  copiedResult_result cap (max (max log (cap+1)) (cap+1)) _
    (paired cap (max log (cap+1)) (combinedTag left right pre cap z log ambient first) second)

end NearCubicWires.RepairOrdinary.PCPTraversal
