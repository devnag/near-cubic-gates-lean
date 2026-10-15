import Proof.Hierarchy.CompetitorResidueTablePadding

/-! Physical dock from the actual retained 35-tape plane-table bank. Only
Q is a new supplied dimension; the native W and n fields are actually used. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTableDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWords)
open CompetitorResidueTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 47) : Fin 86 :=
  if i=19 then 19 else if i=27 then 27 else if i=4 then 35 else if i=9 then 36
  else ⟨i.val+37,by omega⟩
def widthSlots : Fin 4 → Fin 86 := ![9,84,36,85]
def input (ambient : Fin 35 → List Bool) (q : ℕ) : Fin 86 → List Bool :=
  Fin.addCases (m := 35) (n := 51) (motive := fun _ => List Bool) ambient
    (fun i => if i=0 then List.replicate q true else [])
def heads (pos : ℕ) : Fin 86 → ℕ := fun i => if i=32 then pos else 0
noncomputable def widthProgram := RecoveryFocus.machine widthSlots ClockUnarySum.machine
noncomputable def tableProgram := RecoveryFocus.machine nativeSlots CompetitorResidueTable.machine
noncomputable def machine := Composition.machine widthProgram tableProgram
def budget (w q n : ℕ) := 2*w+7+CompetitorResidueTable.budget w q n

theorem native_injective : Function.Injective nativeSlots := by decide
theorem native_avoids (j : Fin 35) (h19 : j≠19) (h27 : j≠27) :
    ∀ i,nativeSlots i≠j.castAdd 51 := by
  exact (show ∀ j : Fin 35,j≠19 → j≠27 → ∀ i,nativeSlots i≠j.castAdd 51 by decide) j h19 h27

theorem dock_run (d w q pos : ℕ) (xs : List Cell) (suffix : List Bool) (ambient : Fin 35 → List Bool)
    (hw : ambient 9=ZeroPadding.pad d (List.replicate w true))
    (hn : ambient 27=ZeroPadding.pad d (CompareMachine.word xs.length))
    (hsource : ambient 19=oldWords w xs++suffix)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a) :
    ∃ r,runFrom machine (budget w q xs.length)
      (RecoveryCalls.restarted machine (heads pos) (input ambient q))=some r ∧
      r.steps≤budget w q xs.length ∧ r.final.heads=heads pos ∧
      r.final.tapes 45=residueWords w q xs ∧
      r.final.tapes 35=List.replicate q true ∧ r.final.tapes 36=List.replicate w true ∧
      (∀ i : Fin 35,r.final.tapes (i.castAdd 51)=ambient i) := by
  have hwi : ∀ i,input ambient q (widthSlots i)=widthInput d w i := by
    intro i
    fin_cases i
    · exact hw
    · rfl
    · rfl
    · rfl
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorReusableDecision.bounded_focused_run widthSlots (by decide)
    _ _ _ (width_copy_run d w) (heads pos) (input ambient q)
    (by intro i; fin_cases i <;> rfl) hwi
  let middle := install widthSlots (input ambient q) (widthOutput d w)
  have middleOriginal (i : Fin 35) : middle (i.castAdd 51)=ambient i := by
    by_cases hi : i=9
    · subst i
      exact (install_slot widthSlots (by decide) _ (widthOutput d w) 0).trans hw.symm
    · have hn9 : i.val≠9 := fun h => hi (Fin.ext h)
      have hk : ∀ j,widthSlots j≠i.castAdd 51 := by
        intro j hj
        have hv' := congrArg (fun a : Fin 86 => a.val) hj
        fin_cases j <;> simp [widthSlots] at hv' <;> omega
      have he := install_other widthSlots (input ambient q) (widthOutput d w) (i.castAdd 51) hk
      simpa only [middle,input,Fin.addCases_left] using he
  have middleLocal (i : Fin 47) : middle (nativeSlots i)=
      if i=9 then List.replicate w true else input ambient q (nativeSlots i) := by
    by_cases hi : i=9
    · subst i
      exact install_slot widthSlots (by decide) _ (widthOutput d w) 2
    · rw [if_neg hi]
      apply install_other
      intro j hj
      fin_cases j
      · exact (show ∀ i,nativeSlots i≠9 by decide) i hj.symm
      · exact (show ∀ i,nativeSlots i≠84 by decide) i hj.symm
      · exact hi ((show ∀ i,nativeSlots i=36 → i=9 by decide) i hj.symm)
      · exact (show ∀ i,nativeSlots i≠85 by decide) i hj.symm
  obtain ⟨produced,hready,h8,h19,h9,h4,h27⟩ := padded_driver_run d w q xs suffix hq hv
  have hti : ∀ i,middle (nativeSlots i)=paddedReadyInput d w q xs.length (oldWords w xs++suffix) i := by
    intro i
    rw [middleLocal]
    fin_cases i <;> simp [nativeSlots,input,paddedReadyInput,driverPadding,readyInput,
      CompetitorResidueTable.input,Fin.addCases,hn,hsource]
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorReusableDecision.bounded_focused_run nativeSlots native_injective
    _ _ _ hready (heads pos) middle (by
      intro i
      have hn32 : nativeSlots i≠32 := (show ∀ i,nativeSlots i≠32 by decide) i
      simp [heads,hn32]) hti
  have he : Composition.restart first.final tableProgram.start=
      RecoveryCalls.restarted tableProgram (heads pos) middle := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom tableProgram (CompetitorResidueTable.budget w q xs.length)
      (Composition.restart first.final tableProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join widthProgram tableProgram _ _ _ first last hfirst hl'
  have hc : (2*w+6)+1+CompetitorResidueTable.budget w q xs.length=budget w q xs.length := by
    unfold budget
    omega
  rw [hc] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget w q xs.length
    omega
  · change last.final.tapes 45=residueWords w q xs
    rw [hlt]
    exact (install_slot nativeSlots native_injective middle produced 8).trans h8
  · change last.final.tapes 35=List.replicate q true
    rw [hlt]
    exact (install_slot nativeSlots native_injective middle produced 4).trans h4
  · change last.final.tapes 36=List.replicate w true
    rw [hlt]
    exact (install_slot nativeSlots native_injective middle produced 9).trans h9
  · intro i
    change last.final.tapes (i.castAdd 51)=ambient i
    rw [hlt]
    by_cases h19' : i=19
    · subst i
      exact (install_slot nativeSlots native_injective middle produced 19).trans (h19.trans hsource.symm)
    · by_cases h27' : i=27
      · subst i
        exact (install_slot nativeSlots native_injective middle produced 27).trans (h27.trans hn.symm)
      · exact (install_other nativeSlots middle produced (i.castAdd 51) (native_avoids i h19' h27')).trans (middleOriginal i)

theorem budget_bound (w q n : ℕ) (hq : q≤w) : budget w q n≤121000*(n+1)*(w+1)^2 := by
  have hb := CompetitorResidueTable.budget_bound w q n hq
  have hu : 1≤(w+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left n hu
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorResidueTableDock
