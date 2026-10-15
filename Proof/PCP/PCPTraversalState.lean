import Proof.PCP.PCPTraversalLeafLoad

/-! The workspace bound used by the executed subtree induction. Global
source tape0 and the capacity sweep log127 have their separate contracts. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def WorkBound (cap : ℕ) (tapes : Fin 128 → List Bool) : Prop :=
  ∀ i,39 ≤ i.val → i≠127 → (tapes i).length≤cap

theorem WorkBound.install {t cap : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (slot : Fin t → Fin 128)
    (out : Fin t → List Bool)
    (ho : ∀ j,39 ≤ (slot j).val → slot j≠127 → (out j).length≤cap) :
    WorkBound cap (install slot ambient out) := by
  intro i hi hx
  cases hp : RecoveryFocus.pick slot i with
  | none => simpa only [RecoveryRootRound.install,hp] using hb i hi hx
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simpa only [RecoveryRootRound.install,hp] using ho j (he ▸ hi) (he ▸ hx)

theorem WorkBound.clear {t cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (hd : ∀ j,slot j≠28) (hl : ∀ j,slot j≠127) :
    WorkBound cap (cleared slot cap log ambient) := by
  classical
  intro i hlow hlast
  by_cases hs : ∃ j,slot j=i
  · obtain ⟨j,rfl⟩ := hs
    rw [cleared_slot slot hi hd hl]
    simp
  · rw [cleared_other slot cap log ambient i (by simpa using hs)
      (by intro he; subst i; contradiction) (Ne.symm hlast)]
    exact hb i hlow hlast

theorem WorkBound.leafPrinted {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (hc : 3≤cap) : WorkBound cap (leafPrinted cap log ambient) := by
  apply (hb.clear leafSlots leafSlots_injective (by decide) (by decide)).install leafPrintSlots
  intro j _ _
  fin_cases j
  · change (ZeroPadding.pad cap (frame (1 : ℕ).bits)).length≤cap
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (by simpa using hc)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

theorem WorkBound.leafLoaded {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (hc : 3≤cap)
    (pre bits suffix : List Bool) (hbits : 2*bits.length+1≤cap) :
    WorkBound cap (leafLoaded pre bits suffix cap log ambient) := by
  apply (hb.leafPrinted hc).install advanceSlots
  intro j hj _
  fin_cases j
  · contradiction
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl hbits
  · change (List.replicate (max cap (2*bits.length+1)) false).length≤cap
    simpa only [List.length_replicate] using max_le le_rfl hbits

theorem installedHeads_slot {t : ℕ} (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (ambient : Fin 128 → ℕ) (localHeads : Fin t → ℕ)
    (j : Fin t) : installedHeads slot ambient localHeads (slot j)=localHeads j := by
  simp only [installedHeads,RecoveryFocus.pick_slot slot hi]
theorem installedHeads_other {t : ℕ} (slot : Fin t → Fin 128)
    (ambient : Fin 128 → ℕ) (localHeads : Fin t → ℕ) (i : Fin 128)
    (hi : ∀ j,slot j≠i) : installedHeads slot ambient localHeads i=ambient i := by
  cases hp : RecoveryFocus.pick slot i with
  | none => simp only [installedHeads,hp]
  | some j => exact False.elim (hi j (RecoveryFocus.slot_of_pick slot hp))

theorem pair_ne (j : Fin 38) (i : Fin 128)
    (hb : 77 ≤ i.val ∨ i.val<39) (hl : 83≠i) (hr : 84≠i) : pairSlots j≠i := by
  unfold pairSlots
  split
  · exact hl
  · split
    · exact hr
    · exact bank_ne j i hb

theorem Path.mono {j k : Fin 39} {a b : ℕ} {h₁ h₂ : Fin 128 → ℕ}
    {t₁ t₂ : Fin 128 → List Bool} (h : Path j k a h₁ t₁ h₂ t₂) (hab : a≤b) :
    Path j k b h₁ t₁ h₂ t₂ := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn.trans hab,ht⟩

end NearCubicWires.RepairOrdinary.PCPTraversal
