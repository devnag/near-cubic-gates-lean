import Proof.PCP.PCPTraversalMoves

namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leafSlots : Fin 4 → Fin 128 := ![83,84,89,90]
def leafPrintSlots : Fin 2 → Fin 128 := ![83,89]
theorem leafSlots_injective : Function.Injective leafSlots := by decide
theorem leafPrintSlots_injective : Function.Injective leafPrintSlots := by decide

theorem padded_printer_ready (bits : List Bool) (cap : ℕ) (hc : bits.length≤cap) :
    ReadyRun (HierarchyFixedWord.machine bits) (2*bits.length+2)
      (fun _ => List.replicate cap false)
      ![ZeroPadding.pad cap bits,List.replicate cap false] := by
  obtain ⟨base,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready bits
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config (HierarchyFixedWord.machine bits)
    (fun _ => cap) _ _ base hr
  refine ⟨r,?_,?_,?_,hsteps.trans hs⟩
  · exact hrun
  · rw [hf]
    funext i
    change ZeroPadding.pad cap (base.final.tapes i)=_
    rw [ht]
    fin_cases i
    · rfl
    · change ZeroPadding.pad cap (List.replicate bits.length false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · intro i
    rw [hf]
    exact hh i

def leafPrintLocal (cap : ℕ) : Fin 2 → List Bool :=
  ![ZeroPadding.pad cap (frame (1 : ℕ).bits),List.replicate cap false]
noncomputable def leafPrinted (cap log : ℕ) (ambient : Fin 128 → List Bool) :=
  install leafPrintSlots (cleared leafSlots cap log ambient) (leafPrintLocal cap)
noncomputable def leafLoaded (pre bits suffix : List Bool) (cap log : ℕ)
    (ambient : Fin 128 → List Bool) :=
  install advanceSlots (leafPrinted cap log ambient) (PCPFieldMoves.output pre bits suffix cap cap)

theorem leaf_printed_slot (cap log : ℕ) (ambient : Fin 128 → List Bool) :
    leafPrinted cap log ambient 83=ZeroPadding.pad cap (frame (1 : ℕ).bits) :=
  install_slot leafPrintSlots leafPrintSlots_injective _ (leafPrintLocal cap) 0

theorem leaf_printed_zeros (cap log : ℕ) (ambient : Fin 128 → List Bool)
    (i : Fin 128) (hi : i=84 ∨ i=90) :
    leafPrinted cap log ambient i=List.replicate cap false := by
  rcases hi with rfl|rfl
  · exact (install_other leafPrintSlots _ _ 84 (by decide)).trans
      (cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 1)
  · exact (install_other leafPrintSlots _ _ 90 (by decide)).trans
      (cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 3)

theorem leaf_printed_other (cap log : ℕ) (ambient : Fin 128 → List Bool)
    (i : Fin 128) (hi : ∀ j,leafSlots j≠i) (hd : 28≠i) (hl : 127≠i) :
    leafPrinted cap log ambient i=ambient i := by
  apply Eq.trans (install_other leafPrintSlots _ _ i ?_)
    (cleared_other leafSlots cap log ambient i hi hd hl)
  intro j
  fin_cases j
  · exact hi 0
  · exact hi 2

theorem leaf_load_path (pre bits suffix : List Bool) (cap log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hcap : 3≤cap)
    (hb : ∀ i,(ambient (leafSlots i)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hsource : ambient 0=pre++frame bits++suffix)
    (hh : ∀ i,heads (leafSlots i)=0) (hhd : heads 28=0) (hhl : heads 127=0)
    (hhsource : heads 0=pre.length) :
    Path 2 5 (2*cap+4*bits.length+19) heads ambient
      (installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0])
      (leafLoaded pre bits suffix cap log ambient) := by
  have hclear := clear_path 2 3 leafSlots rfl (by intro q scanned; simp [next])
    leafSlots_injective (by decide) (by decide) cap log heads ambient hb hdriver hlog hh hhd hhl
  have hp := padded_printer_ready (frame (1 : ℕ).bits) cap hcap
  obtain ⟨r,hr,hrh,hrt,_⟩ := hp.focus_at leafPrintSlots leafPrintSlots_injective heads
    (cleared leafSlots cap log ambient)
    (by intro i; fin_cases i
        · exact cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 0
        · exact cleared_slot leafSlots leafSlots_injective (by decide) (by decide) cap log ambient 2)
    (by intro i; fin_cases i; exact hh 0; exact hh 2)
  have hprint := packed_path 3 4 (printer (frame (1 : ℕ).bits) 83 89) rfl 8 heads
    (cleared leafSlots cap log ambient) _ ⟨r,hr,hrh,hrt⟩ (by intro q scanned; simp [next])
  have hmove := advance_leaf_path pre bits suffix cap heads (leafPrinted cap log ambient)
    ((leaf_printed_other cap log ambient 0 (by decide) (by decide) (by decide)).trans hsource)
    (leaf_printed_zeros cap log ambient 84 (Or.inl rfl))
    (leaf_printed_zeros cap log ambient 90 (Or.inr rfl)) hhsource (hh 1) (hh 3)
  have hpath := (hclear.trans hprint).trans hmove
  have he : ((2*cap+5)+(8+1))+(4*bits.length+5)=2*cap+4*bits.length+19 := by omega
  rw [he] at hpath
  exact hpath

theorem leaf_loaded_operands (pre bits suffix : List Bool) (cap log : ℕ)
    (ambient : Fin 128 → List Bool) :
    leafLoaded pre bits suffix cap log ambient 83=ZeroPadding.pad cap (frame (1 : ℕ).bits) ∧
    leafLoaded pre bits suffix cap log ambient 84=ZeroPadding.pad cap (frame bits) := by
  constructor
  · exact (install_other advanceSlots _ _ 83 (by decide)).trans (leaf_printed_slot cap log ambient)
  · exact install_slot advanceSlots advanceSlots_injective _ (PCPFieldMoves.output pre bits suffix cap cap) 1

end NearCubicWires.RepairOrdinary.PCPTraversal
