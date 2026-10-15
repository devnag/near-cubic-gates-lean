import Proof.MachineModel.OrdinaryMatrixBucketScalars

/-! The already produced Buckets sentinel is physically copied into the
actual bucket-controller driver. All prepared scalar fields are retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketTemplate
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 34 := ![27,28,29,22,30]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots MatrixTemplateCopy.resetMachine

theorem template_ready (D H M B count : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (4*count+12) (MatrixBucketScalars.data D H M B count 6) out ∧
      (∀ i : Fin 34,i≠22 → i≠28 → i≠29 → i≠30 → out i=MatrixBucketScalars.data D H M B count 6 i) ∧
      out 22=ZeroPadding.pad D (UnaryTemplate.tape count) := by
  obtain ⟨base,hb,b0,b1,b2,b3,bh,bs⟩ := MatrixTemplateCopy.reset_run count
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config MatrixTemplateCopy.resetMachine (![0,D,D,D,D] : Fin 5 → ℕ)
    _ _ base hb
  let localInput : Fin 5 → List Bool :=
    ![UnaryTemplate.tape count,List.replicate D false,List.replicate D false,List.replicate D false,List.replicate D false]
  have hi : ZeroPadding.config (![0,D,D,D,D] : Fin 5 → ℕ)
      (initialConfiguration MatrixTemplateCopy.resetMachine (MatrixTemplateCopy.resetInput count))=
      initialConfiguration MatrixTemplateCopy.resetMachine localInput := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,ZeroPadding.pad,MatrixTemplateCopy.resetInput,
        MatrixTemplateCopy.input,initialConfiguration,localInput,Fin.addCases]
  rw [hi] at hp
  have ready : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*count+12) localInput padded.final.tapes :=
    ⟨padded,hp,rfl,by intro i; rw [pf]; exact bh i,(ps.trans bs).le⟩
  have p0 : padded.final.tapes 0=UnaryTemplate.tape count := by
    rw [pf]
    change ZeroPadding.pad 0 (base.final.tapes 0)=_
    rw [b0,ZeroPadding.pad_zero]
  have p3 : padded.final.tapes 3=ZeroPadding.pad D (UnaryTemplate.tape count) := by
    rw [pf]
    change ZeroPadding.pad D (base.final.tapes 3)=_
    rw [b3]
  let out := install slots (MatrixBucketScalars.data D H M B count 6) padded.final.tapes
  have focused := CompetitorRationalProducts.bounded_focus slots slots_injective _ _ _ ready
    (MatrixBucketScalars.data D H M B count 6) (by
      intro i
      fin_cases i <;> simp [slots,MatrixBucketScalars.data,MatrixBucketWorkspace.output,localInput])
  refine ⟨out,focused,?_,(install_slot slots slots_injective _ _ 3).trans p3⟩
  intro i h22 h28 h29 h30
  by_cases h27 : i=27
  · subst i
    exact (install_slot slots slots_injective _ _ 0).trans p0
  apply install_other
  intro j
  fin_cases j
  all_goals first | exact Ne.symm h27 | exact Ne.symm h28 | exact Ne.symm h29 | exact Ne.symm h22 | exact Ne.symm h30

noncomputable def preparation :=  Composition.machine MatrixBucketWorkspace.machine MatrixBucketScalars.machine
noncomputable def bank := Composition.machine preparation machine
def budget (D H M count : ℕ) := (2*D+4)+1+(24*H+24*M+53)+1+(4*count+12)

theorem bank_ready (D H M B count : ℕ) (hH : 4*H+3 ≤ D) (hM : 4*M+3 ≤ D) : ∃ out,
    ClockJoin.ReadyRun bank (budget D H M count) (MatrixBucketWorkspace.input D H M B count) out ∧
      (∀ i : Fin 34,i≠22 → i≠28 → i≠29 → i≠30 → out i=MatrixBucketScalars.data D H M B count 6 i) ∧
      out 22=ZeroPadding.pad D (UnaryTemplate.tape count) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixBucketWorkspace.workspace_ready D H M B count
  have first : ClockJoin.ReadyRun MatrixBucketWorkspace.machine (2*D+4)
      (MatrixBucketWorkspace.input D H M B count) (MatrixBucketWorkspace.output D H M B count) := ⟨base,hb,bt,bh,bs.le⟩
  have second := MatrixBucketScalars.scalars_ready D H M B count hH hM
  have joined := ClockJoin.join MatrixBucketWorkspace.machine MatrixBucketScalars.machine _ _ _ _ _ first second
  obtain ⟨out,last,old,o22⟩ := template_ready D H M B count
  have whole := ClockJoin.join preparation machine _ _ _ _ _ joined last
  exact ⟨out,whole,old,o22⟩

end NearCubicWires.RepairOrdinary.MatrixBucketTemplate
