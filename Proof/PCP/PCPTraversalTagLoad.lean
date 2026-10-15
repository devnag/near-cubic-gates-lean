import Proof.PCP.PCPTraversalCombineLoad

/-! The internal tag2 is physically printed and its canonical inner-pair
operand copied in controller28→31, after an actual operand/log sweep. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagPrintLocal (cap : ℕ) : Fin 2 → List Bool :=
  ![ZeroPadding.pad cap (frame (2 : ℕ).bits),List.replicate cap false]
noncomputable def tagPrinted (cap log : ℕ) (ambient : Fin 128 → List Bool) :=
  install leafPrintSlots (cleared leafSlots cap log ambient) (tagPrintLocal cap)
noncomputable def tagLoaded (bits : List Bool) (cap log : ℕ) (ambient : Fin 128 → List Bool) :=
  install rightCopySlots (tagPrinted cap log ambient) (resultLocal cap bits)

theorem tag_load_path (bits : List Bool) (cap log : ℕ) (heads : Fin 128 → ℕ)
    (ambient : Fin 128 → List Bool) (hc : 5≤cap) (hbits : 2*bits.length+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hsource : ambient 77=ZeroPadding.pad cap (frame bits)) (hhd : heads 28=0) :
    Path 28 31 (4*cap+23) heads ambient heads (tagLoaded bits cap log ambient) ∧
    WorkBound cap (tagLoaded bits cap log ambient) := by
  have hclear := clear_path 28 29 leafSlots rfl (by intro q scanned; simp [next])
    leafSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i <;> exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  have hprint := literal_print_path 29 30 leafPrintSlots leafPrintSlots_injective
    (frame (2 : ℕ).bits) rfl (by intro q scanned; simp [next]) cap heads (cleared leafSlots cap log ambient) hc
    (by intro i; fin_cases i
        · exact cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 0
        · exact cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 2)
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
  have hpbound : WorkBound cap (tagPrinted cap log ambient) := by
    apply (hb.clear leafSlots leafSlots_injective (by decide) (by decide)).install leafPrintSlots
    intro i _ _
    fin_cases i
    · change (ZeroPadding.pad cap (frame (2 : ℕ).bits)).length≤cap
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl hc
    · change (List.replicate cap false).length≤cap
      simp only [List.length_replicate,le_refl]
  have hcopy := field_copy_path 30 31 rightCopySlots rightCopySlots_injective rfl
    (by intro q scanned; simp [next]) bits cap heads (tagPrinted cap log ambient) hbits
    (by intro i; fin_cases i
        · exact (install_cleared_other leafPrintSlots leafSlots cap log ambient
            (tagPrintLocal cap) 77 (by decide) (by decide) (by decide) (by decide)).trans hsource
        · exact (install_other leafPrintSlots (cleared leafSlots cap log ambient)
            (tagPrintLocal cap) 84 (by decide)).trans
            (cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 1)
        · exact (install_other leafPrintSlots (cleared leafSlots cap log ambient)
            (tagPrintLocal cap) 90 (by decide)).trans
            (cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 3))
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
  have hpath := (hclear.trans hprint).trans hcopy
  refine ⟨hpath.mono ?_,hpbound.fieldCopied rightCopySlots bits hbits⟩
  have he : (frame (2 : ℕ).bits).length=5 := by rfl
  rw [he]
  omega

theorem tag_loaded_operands (bits : List Bool) (cap log : ℕ) (ambient : Fin 128 → List Bool) :
    tagLoaded bits cap log ambient 83=ZeroPadding.pad cap (frame (2 : ℕ).bits) ∧
    tagLoaded bits cap log ambient 84=ZeroPadding.pad cap (frame bits) := by
  constructor
  · exact (install_other rightCopySlots (tagPrinted cap log ambient) (resultLocal cap bits) 83 (by decide)).trans
      (install_slot leafPrintSlots leafPrintSlots_injective (cleared leafSlots cap log ambient) (tagPrintLocal cap) 0)
  · exact install_slot rightCopySlots rightCopySlots_injective _ (resultLocal cap bits) 1
theorem tag_loaded_driver (bits : List Bool) (cap log : ℕ) (ambient : Fin 128 → List Bool) :
    tagLoaded bits cap log ambient 28=List.replicate cap true :=
  (install_other rightCopySlots (tagPrinted cap log ambient) (resultLocal cap bits) 28 (by decide)).trans
    (install_cleared_driver leafPrintSlots leafSlots leafSlots_injective (by decide) (by decide)
      cap log ambient (tagPrintLocal cap) (by decide))
theorem tag_loaded_log (bits : List Bool) (cap log : ℕ) (ambient : Fin 128 → List Bool) :
    tagLoaded bits cap log ambient 127=List.replicate (max log (cap+1)) false :=
  (install_other rightCopySlots (tagPrinted cap log ambient) (resultLocal cap bits) 127 (by decide)).trans
    (install_cleared_log leafPrintSlots leafSlots leafSlots_injective (by decide) (by decide)
      cap log ambient (tagPrintLocal cap) (by decide))

end NearCubicWires.RepairOrdinary.PCPTraversal
