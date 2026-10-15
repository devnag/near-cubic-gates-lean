import Proof.PCP.PCPPNativeTripleMassLayout

/-! Actual compact-clause byte mass from raw M and the original triple
fields. The M*3 driver is constructed, the existing counted measurement
is executed, and the original source cursor and raw M are preserved. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeTripleMass
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem mass_run (rows : List (Fin 3 → List Bool)) : ∃ result,
    run machine (budget rows) (data (source rows) rows.length 0)=some result ∧ result.steps ≤ budget rows ∧
    result.final.heads 4=0 ∧ result.final.tapes 4=source rows ∧
    result.final.heads 5=0 ∧ result.final.tapes 5=List.replicate (source rows).length true ∧
    result.final.heads 0=0 ∧ result.final.tapes 0=List.replicate rows.length true := by
  obtain ⟨a,ha,adata,ah,as⟩ := prepare_run (source rows) rows.length
  obtain ⟨dimensionResult,hd,_,_,dtemplate,dh,ds⟩ := MatrixRawDimension.raw_run (rows.length*3)
  obtain ⟨b,hb,_,bs,bh,bt,baway⟩ := RecoveryFocus.dock dimensionSlots dimension_injective MatrixDimensionHeader.machine _
    a.final.heads a.final.tapes (initialConfiguration MatrixDimensionHeader.machine (MatrixRawDimension.input (rows.length*3)))
    (by intro i; exact ah (dimensionSlots i))
    (by intro i; rw [adata]; fin_cases i <;> rfl) dimensionResult hd
  obtain ⟨measured,sl,ml,hm,ms,mf⟩ := PCPPNativeMass.template_run (fields rows)
  have ht := (PCPPNativeMass.template_input (fields rows)).1
  have hh := (PCPPNativeMass.template_input (fields rows)).2
  rw [field_count rows] at ht hh
  have hOutside (i : Fin 12) (hi : ∀ j,dimensionSlots j≠i) :
      b.final.heads i=0 ∧ b.final.tapes i=data (source rows) rows.length 2 i :=
    ⟨(baway i hi).1.trans (ah i),(baway i hi).2.trans (congrFun adata i)⟩
  obtain ⟨c,hc,_,cs,ch,ct,caway⟩ := RecoveryFocus.dock massSlots mass_injective PCPSerializerCapacity.MassReady.machine _
    b.final.heads b.final.tapes
    (PCPPNativeMass.templateCfg PCPSerializerCapacity.MassReady.machine.start (FieldList.stream (fields rows))
      0 (fields rows).length 0 0)
    (by
      intro i
      rw [field_count rows,hh]
      fin_cases i
      · exact (hOutside 4 (by decide)).1
      · exact (hOutside 5 (by decide)).1
      · exact (bh 3).trans (congrFun dh 3)
      · exact (hOutside 9 (by decide)).1
      · exact (hOutside 10 (by decide)).1)
    (by
      intro i
      rw [field_count rows,ht]
      fin_cases i
      · exact (hOutside 4 (by decide)).2
      · exact (hOutside 5 (by decide)).2
      · exact (bt 3).trans dtemplate
      · exact (hOutside 9 (by decide)).2
      · exact (hOutside 10 (by decide)).2) measured hm
  have hab := Composition.run_join prepare dimension _ _ _ a b ha hb
  have joined := Composition.run_join (Composition.machine prepare dimension) measure _ _ _
    (Composition.joinedReceipt a b) c hab hc
  have mh0 : measured.final.heads 0=0 := by rw [mf]; rfl
  have mh1 : measured.final.heads 1=0 := by rw [mf]; rfl
  have mt0 : measured.final.tapes 0=source rows := by
    rw [mf]
    simp [PCPPNativeMass.templateCfg,PCPPNativeMass.padding,PCPSerializerCapacity.MassReady.cfg,ZeroPadding.config,source]
  have mt1 : measured.final.tapes 1=List.replicate (source rows).length true := by
    rw [mf]
    simp [PCPPNativeMass.templateCfg,PCPPNativeMass.padding,PCPSerializerCapacity.MassReady.cfg,ZeroPadding.config,source]
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ budget rows
    rw [bs,ds,cs]
    unfold budget source
    omega
  · exact (ch 0).trans mh0
  · exact (ct 0).trans mt0
  · exact (ch 1).trans mh1
  · exact (ct 1).trans mt1
  · exact (caway 0 (by decide)).1.trans (hOutside 0 (by decide)).1
  · exact (caway 0 (by decide)).2.trans (hOutside 0 (by decide)).2

end NearCubicWires.RepairOrdinary.PCPPNativeTripleMass
