import Proof.CaseAnalysis.RowsCircuitBottomMeaning

/-! Changed-coordinate projection for the already paid bounded copier.
This keeps the concrete circuit bank opaque at each retained-field copy. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCopy
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_focus {u : ℕ} (slots : Fin 4→Fin u) (hinj : Function.Injective slots)
    (cap : ℕ) (source : List Bool) (hc : source.length≤cap)
    (heads : Fin u→ℕ) (tapes : Fin u→List Bool)
    (hh : ∀ i,heads (slots i)=0)
    (ht : ∀ i,tapes (slots i)=CloseoutRowsMetadataCopy.input source cap i) :
    PCPOuter.Exact (RecoveryFocus.machine slots RecoveryBoundedTapeCopy.machine) (2*cap+4)
      heads tapes heads (Function.update tapes (slots 1) (ZeroPadding.pad cap source)):=by
  obtain ⟨base,hb,bt,bh,bs⟩:=CloseoutRowsMetadataCopy.copy_ready source cap hc
  obtain ⟨r,hr,rh,rt,rs⟩:=CloseoutRowsCircuitAppend.focused_one RecoveryBoundedTapeCopy.machine slots hinj 1 _ _ base hb rfl
    (by intro i _;exact bh i)
    (by
      intro i hi
      rw [bt]
      fin_cases i <;> first | rfl | exact False.elim (hi rfl)) heads tapes hh ht
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [bh 1] at rh
    rw [←hh 1,Function.update_eq_self] at rh
    exact rh
  · rw [bt] at rt
    exact rt

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCopy
