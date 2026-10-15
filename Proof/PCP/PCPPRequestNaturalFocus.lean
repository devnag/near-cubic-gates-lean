import Proof.PCP.PCPPRequestNatural

/-! The total natural-code atom at a caller's real streaming source cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNatural
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_heads (source : List Bool) (pos : ℕ) (j : Fin 136) :
    (entry source pos).heads j=if j=0 then pos else 0 := by
  refine Fin.addCases (m:=10) (n:=126) (fun k => ?_) (fun k => ?_) j
  · fin_cases k <;> rfl
  · simp only [entry,controlConfig,initial,TapeEmbedding.config,Fin.addCases_right]
    have hn : k.natAdd 10≠(0 : Fin 136) := by
      intro h
      have hv := congrArg Fin.val h
      change 10+k.val=0 at hv
      omega
    rw [if_neg hn]

theorem input_tapes (source : List Bool) (pos : ℕ) (j : Fin 136) :
    (entry source pos).tapes j=if j=0 then source else [] := by
  refine Fin.addCases (m:=10) (n:=126) (fun k => ?_) (fun k => ?_) j
  · fin_cases k <;> rfl
  · simp only [entry,controlConfig,initial,TapeEmbedding.config,Fin.addCases_right]
    have hn : k.natAdd 10≠(0 : Fin 136) := by
      intro h
      have hv := congrArg Fin.val h
      change 10+k.val=0 at hv
      omega
    rw [if_neg hn]

theorem focus_run {u z : ℕ} (slots : Fin 136 → Fin u) (hinj : Function.Injective slots)
    (ambient : Configuration u z) (pre tail : List Bool) (n : ℕ)
    (ht : ∀ j,ambient.tapes (slots j)=if j=0 then pre++natWord n++tail else [])
    (hh : ∀ j,ambient.heads (slots j)=if j=0 then pre.length else 0) :
    ∃ r,runFrom (RecoveryFocus.machine slots machine) (budget n)
      (Composition.restart ambient (RecoveryFocus.machine slots machine).start)=some r ∧
      r.steps≤budget n ∧
      (∃ padding,r.final.tapes (slots 85)=frame (CanonicalBinary.encodeNat n).bits++List.replicate padding false) ∧
      r.final.heads (slots 85)=0 ∧ r.final.tapes (slots 86)=(CanonicalBinary.encodeNat n).bits ∧
      r.final.tapes (slots 0)=pre++natWord n++tail ∧
      r.final.heads (slots 0)=pre.length+(natWord n).length ∧
      (∀ i,RecoveryFocus.pick slots i=none →
        r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨base,hb,⟨padding,bt⟩,braw,bh,b0,bh0,bs⟩ := natural_run pre tail n
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots hinj machine ambient.heads ambient.tapes _ _ base hb
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes
      (entry (pre++natWord n++tail) pre.length)=
      Composition.restart ambient (RecoveryFocus.machine slots machine).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [input_heads]; exact hh i
    · intro i; rw [input_tapes]; exact ht i
  rw [hi] at hr
  have localT (j : Fin 136) : r.final.tapes (slots j)=base.final.tapes j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  have localH (j : Fin 136) : r.final.heads (slots j)=base.final.heads j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  refine ⟨r,hr,by omega,⟨padding,(localT 85).trans bt⟩,(localH 85).trans bh,
    (localT 86).trans braw,(localT 0).trans b0,(localH 0).trans bh0,?_⟩
  intro i hi
  simp [rf,RecoveryFocus.config,hi]

end NearCubicWires.RepairOrdinary.PCPPRequestNatural
