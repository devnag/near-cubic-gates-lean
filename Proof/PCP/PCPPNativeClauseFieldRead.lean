import Proof.PCP.PCPPNativeClauseDecode

/-! The original framed literal is copied, decoded and converted to its
native reference by one fixed machine, retaining the live source cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseField
open LocalBitMultitape RadixSemantics RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readMachine := Composition.machine copyMachine decodeMachine
noncomputable def machine := Composition.machine readMachine refMachine
def readBudget (bits : List Bool) := 4*bits.length+Unary.budget bits+7
def budget (bits : List Bool) (index : ℕ) (sign : Bool) (stride p n : ℕ) :=
  readBudget bits+1+PCPPNativeClauseReference.budget index sign stride p n

theorem read_run (pre bits tail : List Bool) (index : ℕ) (sign : Bool)
    (stride p n : ℕ) (hv : value bits=2*index+sign.toNat) : ∃ r,
    runFrom readMachine (readBudget bits)
      (entry readMachine pre.length (input (pre++frame bits++tail) stride p n))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      (∀ j : Fin 13,r.final.tapes (refSlots j)=
        PCPPNativeClauseReference.wordInput index sign stride p n j) ∧
      r.final.tapes 13=pre++frame bits++tail ∧ r.steps ≤ readBudget bits := by
  obtain ⟨a,ha,ah,atapes,astep⟩ := copy_run pre bits tail stride p n
  obtain ⟨b,hb,bh,bt,bsrc,bs⟩ := decode_run (pre++frame bits++tail) bits
    (pre.length+2*bits.length+1) index sign stride p n hv
  have mid : Composition.restart a.final decodeMachine.start=
      entry decodeMachine (pre.length+2*bits.length+1)
        (copied (pre++frame bits++tail) bits stride p n) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←mid] at hb
  have h := Composition.run_join copyMachine decodeMachine _ _ _ a b ha hb
  have he : (4*bits.length+4)+1+(Unary.budget bits+2)=readBudget bits := by
    unfold readBudget
    omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt a b,h,bh,bt,bsrc,?_⟩
  change a.steps+1+b.steps ≤ readBudget bits
  unfold readBudget
  omega

theorem field_run (pre bits tail : List Bool) (index : ℕ) (sign : Bool)
    (stride p n : ℕ) (hv : value bits=2*index+sign.toNat) : ∃ r,
    runFrom machine (budget bits index sign stride p n)
      (entry machine pre.length (input (pre++frame bits++tail) stride p n))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes 11=List.replicate
        (index*stride+PCPPNativeClauseReference.offset sign p n) true ∧
      r.final.tapes 13=pre++frame bits++tail ∧
      r.final.tapes 4=UnaryTemplate.tape stride ∧
      r.final.tapes 5=List.replicate p true ∧
      r.final.tapes 6=List.replicate n true ∧
      r.steps ≤ budget bits index sign stride p n := by
  obtain ⟨a,ha,ah,atapes,asrc,astep⟩ := read_run pre bits tail index sign stride p n hv
  obtain ⟨base,hb,bt,bh,bs⟩ := PCPPNativeClauseReference.word_run index sign stride p n
  obtain ⟨b,hb,_,bsteps,bheads,btapes,keep⟩ := RecoveryFocus.dock refSlots ref_injective
    PCPPNativeClauseReference.machine _ a.final.heads a.final.tapes
    (initialConfiguration PCPPNativeClauseReference.machine
      (PCPPNativeClauseReference.wordInput index sign stride p n))
    (by intro j; rw [ah]; simp [heads,refSlots,Fin.ext_iff,initialConfiguration]; omega) atapes base hb
  have h := Composition.run_join readMachine refMachine _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_,?_,?_,?_⟩
  · change b.final.heads=_
    funext i
    by_cases hi : ∃ j,refSlots j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [bheads j,bh j]
      simp [heads,refSlots,Fin.ext_iff]
      omega
    · rw [(keep i (by intro j hj; exact hi ⟨j,hj⟩)).1,ah]
  · exact (btapes 11).trans ((bt 11 (by decide)).trans (by rfl))
  · exact (keep 13 (by intro j; simp [refSlots,Fin.ext_iff]; omega)).2.trans asrc
  · exact (btapes 4).trans ((bt 4 (by decide)).trans (by rfl))
  · exact (btapes 5).trans ((bt 5 (by decide)).trans (by rfl))
  · exact (btapes 6).trans ((bt 6 (by decide)).trans (by rfl))
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPNativeClauseField
