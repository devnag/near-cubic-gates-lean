import Proof.Amplification.RecoveryProjectionEval

/-! The same concrete projection evaluator in a cleared reusable bank.
Only the two copied source fields differ from the physical false backing;
the result and all workspace lengths stay inside that backing. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionEval
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reusableInput (cap : Nat) (bits randomness : List Bool) (i : Fin 28) :=
  if i=0 then ZeroPadding.pad cap (frame bits)
  else if i=21 then ZeroPadding.pad cap (frame randomness) else List.replicate cap false

theorem pad_false (cap : Nat) (hc : 1 ≤ cap) : ZeroPadding.pad cap [false]=List.replicate cap false := by
  simp only [ZeroPadding.pad,List.length_singleton,List.singleton_append]
  rw [←List.replicate_succ]
  congr 1
  omega

theorem reusable_input (cap : Nat) (bits randomness : List Bool) (hc : 1 ≤ cap) :
    (fun i=>ZeroPadding.pad cap (input bits randomness false false false cap i))=
      reusableInput cap bits randomness := by
  funext i
  have hempty : ZeroPadding.pad cap [] = List.replicate cap false := by simp [ZeroPadding.pad]
  have hback : ZeroPadding.pad cap (List.replicate cap false) = List.replicate cap false := by simp [ZeroPadding.pad]
  fin_cases i
  · rfl
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · exact hempty
  · rfl
  · exact pad_false cap hc
  · exact hback
  · exact pad_false cap hc
  · exact hback
  · exact pad_false cap hc
  · exact hempty

theorem frame_fits (bits randomness : List Bool) (cap : Nat) (hc : budget bits randomness+1 ≤ cap) :
    (frame bits).length ≤ cap ∧ (frame randomness).length ≤ cap := by
  have hsize : bits.length+randomness.length+1 ≤ (bits.length+randomness.length+1)^2 :=
    Nat.le_self_pow (by decide) _
  simp only [budget] at hc
  rw [frame_length,frame_length]
  constructor <;> nlinarith

theorem reusable_ready (cap : Nat) (bits randomness : List Bool)
    (hc : budget bits randomness+1 ≤ cap) : ∃ out,
    ClockJoin.ReadyRun machine (budget bits randomness) (reusableInput cap bits randomness) out ∧
      out 26=ZeroPadding.pad cap [outputBit bits randomness] ∧ ∀ i,(out i).length ≤ cap := by
  have hpos : 1 ≤ cap := by omega
  obtain ⟨cold,hcold,hbit⟩ := bounded_ready bits randomness false false false cap (by omega)
  have h := PCPPairReusable.padded_ready machine _ _ hcold (fun _=>cap)
  rw [reusable_input cap bits randomness hpos] at h
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  obtain ⟨hbits,hrandom⟩ := frame_fits bits randomness cap hc
  have hi : ∀ i,(reusableInput cap bits randomness i).length ≤ max cap (0+1) := by
    intro i
    simp only [reusableInput]
    split_ifs <;> simp only [ZeroPadding.pad_length,List.length_replicate]
    · exact (max_eq_left hbits).le.trans (Nat.le_max_left _ _)
    · exact (max_eq_left hrandom).le.trans (Nat.le_max_left _ _)
    · exact Nat.le_max_left _ _
  have support := RecoveryTapeSupport.run_support machine _ _ r hr cap 0
    (by intro i; exact Nat.zero_le _) hi
  refine ⟨_,⟨r,hr,ht,hh,hs⟩,?_,?_⟩
  · rw [hbit]
  · intro i
    have hsupp := support i
    rw [ht] at hsupp
    exact hsupp.trans (max_le (Nat.le_refl cap) (by omega))

theorem reusable_projection {n : Nat} (cap : Nat) (p : ProjectedRandomBit n) (randomness : BitInput n)
    (hc : budget (projectionCode p).bits (List.ofFn randomness)+1 ≤ cap) : ∃ out,
    ClockJoin.ReadyRun machine (budget (projectionCode p).bits (List.ofFn randomness))
      (reusableInput cap (projectionCode p).bits (List.ofFn randomness)) out ∧
      out 26=ZeroPadding.pad cap [p.eval randomness] ∧ ∀ i,(out i).length ≤ cap := by
  obtain ⟨out,hr,hbit,hbound⟩ := reusable_ready cap (projectionCode p).bits (List.ofFn randomness) hc
  rw [projection_bit] at hbit
  exact ⟨out,hr,hbit,hbound⟩

end NearCubicWires.RepairSource.RecoveryProjectionEval
