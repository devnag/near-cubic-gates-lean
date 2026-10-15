import Proof.PCP.PCPPRequestNaturalFocus

/-! Three native descriptor fields share only their streaming source tape;
each actual natural-code call gets a distinct finite cold bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeFields
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 3) (j : Fin 136) : Fin 406 :=
  if j=0 then 0 else ⟨j.val+135*i.val,by omega⟩
def outputSlot (i : Fin 3) : Fin 406 := slots i 85
noncomputable def field (i : Fin 3) := RecoveryFocus.machine (slots i) PCPPRequestNatural.machine
noncomputable def firstTwo := Composition.machine (field 0) (field 1)
noncomputable def machine := Composition.machine firstTwo (field 2)
def inputHeads (pos : ℕ) (i : Fin 406) := if i=0 then pos else 0
def inputTapes (source : List Bool) (i : Fin 406) := if i=0 then source else []
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  (⟨machine.start,inputHeads pos,inputTapes source⟩ : Configuration 406 _)

theorem slots_injective (i : Fin 3) : Function.Injective (slots i) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega

theorem slots_nonzero (i : Fin 3) (j : Fin 136) (hj : j≠0) : slots i j≠0 := by
  intro h
  have hv := congrArg Fin.val h
  have hjv : j.val≠0 := fun he => hj (Fin.ext he)
  simp only [slots,hj,ite_false] at hv
  change j.val+135*i.val=0 at hv
  omega

theorem other_bank (i k : Fin 3) (hik : i≠k) (j : Fin 136) (hj : j≠0) :
    RecoveryFocus.pick (slots i) (slots k j)=none := by
  have hn : ¬∃ l,slots i l=slots k j := by
    rintro ⟨l,hl⟩
    have hjv : j.val≠0 := fun h => hj (Fin.ext h)
    have hikv : i.val≠k.val := fun h => hik (Fin.ext h)
    have hv := congrArg Fin.val hl
    by_cases hl0 : l=0
    · subst l
      have h0 : slots i 0=0 := rfl
      rw [h0] at hl
      exact slots_nonzero k j hj hl.symm
    · have hlv : l.val≠0 := fun h => hl0 (Fin.ext h)
      simp only [slots,hl0,hj,ite_false] at hv
      change l.val+135*i.val=j.val+135*k.val at hv
      have hlt := l.isLt
      have hjt := j.isLt
      omega
  simp [RecoveryFocus.pick,hn]

theorem stage_run {z : ℕ} (ambient : Configuration 406 z) (i : Fin 3)
    (pre tail : List Bool) (n : ℕ)
    (hsource : ambient.tapes 0=pre++natWord n++tail) (hpos : ambient.heads 0=pre.length)
    (hfresh : ∀ j : Fin 136,j≠0 → ambient.tapes (slots i j)=[] ∧ ambient.heads (slots i j)=0) :
    ∃ r,runFrom (field i) (PCPPRequestNatural.budget n)
      (Composition.restart ambient (field i).start)=some r ∧
      r.steps≤PCPPRequestNatural.budget n ∧
      (∃ padding,r.final.tapes (outputSlot i)=frame (CanonicalBinary.encodeNat n).bits++List.replicate padding false) ∧
      r.final.heads (outputSlot i)=0 ∧ r.final.tapes 0=pre++natWord n++tail ∧
      r.final.heads 0=pre.length+(natWord n).length ∧
      (∀ (k : Fin 3),i≠k → ∀ (j : Fin 136),j≠0 →
        r.final.tapes (slots k j)=ambient.tapes (slots k j) ∧
        r.final.heads (slots k j)=ambient.heads (slots k j)) := by
  obtain ⟨r,hr,hs,hout,hhout,_,h0,hh0,hkeep⟩ :=
    PCPPRequestNatural.focus_run (slots i) (slots_injective i) ambient pre tail n
      (by intro j; by_cases hj : j=0
          · subst j; exact hsource
          · rw [if_neg hj]; exact (hfresh j hj).1)
      (by intro j; by_cases hj : j=0
          · subst j; exact hpos
          · rw [if_neg hj]; exact (hfresh j hj).2)
  refine ⟨r,hr,hs,hout,hhout,h0,hh0,?_⟩
  intro k hik j hj
  exact hkeep _ (other_bank i k hik j hj)

end NearCubicWires.RepairOrdinary.PCPPRequestNodeFields
