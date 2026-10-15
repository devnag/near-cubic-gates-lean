import Proof.PCP.PCPPQueryLayout

/-! Cold setup of the SAME shared PCPP source bank. Only the cached object
and actual raw native size/arity counters are supplied; all workspace is paid. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCold
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cacheSlots (D : ℕ) (j : Fin 19) := bankSlots D (j.castAdd 2)
def sizeSlot (D : ℕ) : Fin (tapes D) := ⟨21,by simp [tapes,PCPPQueryCapacity.tapes,RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]⟩

theorem cold_run (D K : ℕ) (source : List Bool) (size arity : ℕ)
    (hC : 2≤K*(size+arity+1)^D) : ∃ r,
    run (machine D K) (budget D K size arity) (input D source size arity)=some r ∧
      (∀ j : Fin 19,r.final.tapes (cacheSlots D j)=
        PCPPQueryIndexPadding.clauseData source arity 0 (K*(size+arity+1)^D) [] j) ∧
      (∀ j : Fin 19,r.final.heads (cacheSlots D j)=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (sizeSlot D)=List.replicate size true ∧ r.final.heads (sizeSlot D)=0 ∧
      r.steps≤budget D K size arity := by
  obtain ⟨capOut,hcap,hsize,harity,hvalue⟩:=PCPPQueryCapacity.capacity_run D K size arity
  have capFocused:=hcap.focus (capacitySlots D) (capacity_injective D) (input D source size arity)
    (input_capacity D source size arity)
  obtain ⟨first,hf,ft,fh,fs⟩:=capFocused
  obtain ⟨base,hb,bt,bh,_,_,bs⟩:=PCPPQueryClauseBank.start_run source arity (K*(size+arity+1)^D) hC
  obtain ⟨last,hl,_,ls,lh,lt,lkeep⟩:=RecoveryFocus.dock (bankSlots D) (bank_injective D)
    PCPPQueryClauseBank.startMachine _ first.final.heads first.final.tapes
    (initialConfiguration PCPPQueryClauseBank.startMachine (PCPPQueryClauseBank.input source arity (K*(size+arity+1)^D)))
    (by intro j; exact fh (bankSlots D j))
    (by intro j; rw [ft]; exact powered_bank D K source size arity capOut harity hvalue j)
    base hb
  have he : (⟨PCPPQueryClauseBank.startMachine.start,first.final.heads,first.final.tapes⟩ : Configuration (tapes D) _)=
      Composition.restart first.final (bankMachine D).start := rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (capacityMachine D K) (bankMachine D) _ _ _ first last hf hl
  have hc : PCPPQueryCapacity.budget D K size arity+1+(2*arity+2*(K*(size+arity+1)^D)+15)=budget D K size arity := by
    unfold budget
    omega
  rw [hc] at whole
  have hn : ∀ j,bankSlots D j≠sizeSlot D := by
    intro j he
    have hv:=congrArg Fin.val he
    have hj:=j.isLt
    dsimp [bankSlots,sizeSlot] at hv
    omega
  have size_eq : sizeSlot D=capacitySlots D (PCPPQueryCapacity.sumSlots D 0) := by
    apply Fin.ext
    simp [sizeSlot,capacitySlots,PCPPQueryCapacity.sumSlots]
    omega
  refine ⟨Composition.joinedReceipt first last,whole,?_,?_,?_,?_,?_⟩
  · intro j
    change last.final.tapes (bankSlots D (j.castAdd 2))=_
    exact (lt (j.castAdd 2)).trans (bt j)
  · intro j
    change last.final.heads (bankSlots D (j.castAdd 2))=_
    exact (lh (j.castAdd 2)).trans (bh j)
  · change last.final.tapes (sizeSlot D)=_
    rw [(lkeep (sizeSlot D) hn).2,ft,size_eq,install_slot _ (capacity_injective D)]
    exact hsize
  · change last.final.heads (sizeSlot D)=0
    exact (lkeep (sizeSlot D) hn).1.trans (fh _)
  · change first.steps+1+last.steps≤_
    rw [ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPQueryCold
