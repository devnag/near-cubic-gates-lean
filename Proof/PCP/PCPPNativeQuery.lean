import Proof.PCP.PCPPNativeQueryColdLayout

/-! Cold allocation and the two physically generated R/Q drivers enter the
actual accepted 174-tape query bank, including its real sentinel heads. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryCold
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loopSlots (i : Fin 174) : Fin 178 := i.castAdd 4
theorem loop_injective : Function.Injective loopSlots := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 178 => i.val) h
noncomputable def target (bits fields : List Bool) (R Q C F G : ℕ) :=
  PCPPNativeQueryLoop.templateConfiguration 0 bits fields 0 0 C F G [] R Q 1

theorem low_data (bits fields : List Bool) (R Q C F G : ℕ) (i : Fin 174) :
    data bits fields R Q C F G 3 (loopSlots i)=(target bits fields R Q C F G).tapes i := by
  refine Fin.addCases (m := 171) (n := 3) (fun j => ?_) (fun j => ?_) i
  · have hl := (PCPPNativeQueryLoop.template_lower 0 bits fields 0 0 C F G [] R Q 1 j).2
    change data bits fields R Q C F G 3 (j.castAdd 7)=_
    simpa only [target,data,Fin.addCases_left,show ¬(3 : ℕ)=0 by decide,ite_false] using hl.symm
  · fin_cases j
    · change fields=ZeroPadding.pad 0 fields
      rw [ZeroPadding.pad_zero]
    · change UnaryTemplate.tape R=ZeroPadding.pad 0 (UnaryTemplate.tape R)
      rw [ZeroPadding.pad_zero]
    · exact (PCPPNativeQueryLoop.template_count 0 bits fields 0 0 C F G [] R Q 1).1.symm

theorem low_heads (bits fields : List Bool) (R Q C F G : ℕ) (i : Fin 174) :
    (directions (loopSlots i)).apply 0=(target bits fields R Q C F G).heads i := by
  refine Fin.addCases (m := 171) (n := 3) (fun j => ?_) (fun j => ?_) i
  · have hl := (PCPPNativeQueryLoop.template_lower 0 bits fields 0 0 C F G [] R Q 1 j).1
    have h172 : loopSlots (j.castAdd 3)≠172 := by
      apply Fin.ne_of_val_ne
      change j.val≠172
      omega
    have h173 : loopSlots (j.castAdd 3)≠173 := by
      apply Fin.ne_of_val_ne
      change j.val≠173
      omega
    unfold target
    rw [hl]
    simp [directions,h172,h173,HeadMove.apply,PCPPNativeQueryReusable.heads]
  · fin_cases j <;> rfl

theorem cold_run (bits fields : List Bool) (R Q C F G : ℕ) : ∃ result,
    run machine (budget R Q G) (data bits fields R Q C F G 0)=some result ∧
    result.steps≤budget R Q G ∧
    (∀ i : Fin 174,result.final.heads (loopSlots i)=(target bits fields R Q C F G).heads i ∧
      result.final.tapes (loopSlots i)=(target bits fields R Q C F G).tapes i) := by
  obtain ⟨a,ha,adata,ah,as⟩ := prepare_run bits fields R Q C F G
  obtain ⟨b,hb,bf,bs⟩ := DecompositionCountPosition.move_run directions (fun _ => 0)
    (data bits fields R Q C F G 3)
  have he : Composition.restart a.final position.start=
      (⟨0,(fun _ => 0),data bits fields R Q C F G 3⟩ : Configuration 178 2) := by
    apply configuration_ext
    · rfl
    · exact funext ah
    · exact adata
  rw [←he] at hb
  have joined := Composition.run_join prepare position _ _ _ a b ha hb
  have hbgt : (2*G+2*R+2*Q+22)+1+1=budget R Q G := by unfold budget; omega
  rw [hbgt] at joined
  refine ⟨Composition.joinedReceipt a b,joined,?_,?_⟩
  · change a.steps+1+b.steps≤budget R Q G
    rw [bs]
    unfold budget
    omega
  · intro i
    change b.final.heads (loopSlots i)=_ ∧ b.final.tapes (loopSlots i)=_
    rw [bf]
    exact ⟨low_heads bits fields R Q C F G i,low_data bits fields R Q C F G i⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQueryCold
