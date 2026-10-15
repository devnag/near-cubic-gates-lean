import Proof.PCP.PCPPNativeMetadataPrefix

/-! The actual final query counter becomes the initial conjunction
accumulator. A paid successor gives the first clause base, and the real
constant-true node is appended at the existing native output cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeConjunctionStart
open LocalBitMultitape SourceInterfaces RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def trueBits := PCPPRequestNodeSchema.native (.const true : BooleanNode 0)
def outputSlot : Fin 1 → Fin 5 := fun _ => 4
noncomputable def first := TapeEmbedding.machine 1 PCPPNativeAddress.machine
noncomputable def second := RecoveryFocus.machine outputSlot (HierarchyFixedWord.raw trueBits)
noncomputable def machine := Composition.machine first second
def heads (out : List Bool) : Fin 5 → ℕ := ![0,0,0,0,out.length]
def input (base : ℕ) (out : List Bool) : Fin 5 → List Bool := ![List.replicate base true,[],[],[],out]
def output (base : ℕ) (out : List Bool) : Fin 5 → List Bool :=
  ![List.replicate base true,[],List.replicate (base+1) true,List.replicate (base+2) false,out++trueBits]
noncomputable def entry (base : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,input base out⟩ : Configuration 5 _)
def budget (base : ℕ) := 2*base+7+trueBits.length

theorem start_run (base : ℕ) (out : List Bool) : ∃ result,
    runFrom machine (budget base) (entry base out)=some result ∧ result.steps ≤ budget base ∧
    result.final.heads=heads (out++trueBits) ∧ result.final.tapes=output base out := by
  obtain ⟨a,ha,atapes,ah,as⟩ := PCPPNativeAddress.address_ready base 0
  let lifted := TapeEmbedding.receipt (fun _ : Fin 1 => out.length) (fun _ => out) a
  have firstRun := TapeEmbedding.run_embed PCPPNativeAddress.machine (fun _ : Fin 1 => out.length)
    (fun _ => out) _ _ a ha
  obtain ⟨b,hb,bf,bs⟩ := Constants.write_run trueBits out
  obtain ⟨c,hc,_,cs,ch,ct,other⟩ := RecoveryFocus.dock outputSlot (by decide) (HierarchyFixedWord.raw trueBits) _
    lifted.final.heads lifted.final.tapes (Constants.cfg trueBits out 0 (by omega))
    (by intro i; fin_cases i; rfl)
    (by intro i; fin_cases i; simp [lifted,outputSlot,Constants.cfg,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]) b hb
  have joined := Composition.run_join first second _ _ _ lifted c firstRun hc
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => out.length) (fun _ => out)
      (initialConfiguration PCPPNativeAddress.machine ![List.replicate base true,List.replicate 0 true,[],[]]))=
      entry base out := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at joined
  have ht : (2*base+4*0+6)+1+trueBits.length=budget base := by unfold budget; omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt lifted c,joined,?_,?_,?_⟩
  · change a.steps+1+c.steps ≤ budget base
    rw [cs,bs]
    unfold budget
    omega
  · funext i
    change c.final.heads i=heads (out++trueBits) i
    refine Fin.addCases (m := 4) (n := 1) (fun j => ?_) (fun j => ?_) i
    · rw [(other (j.castAdd 1) (by intro k; fin_cases k; apply Fin.ne_of_val_ne; change 4≠j.val; omega)).1]
      dsimp only [lifted]
      rw [TapeEmbedding.receipt_heads_old]
      rw [ah]
      fin_cases j <;> rfl
    · fin_cases j
      have he := ch 0
      rw [bf] at he
      simpa [outputSlot,Constants.cfg,heads] using he
  · funext i
    change c.final.tapes i=output base out i
    refine Fin.addCases (m := 4) (n := 1) (fun j => ?_) (fun j => ?_) i
    · rw [(other (j.castAdd 1) (by intro k; fin_cases k; apply Fin.ne_of_val_ne; change 4≠j.val; omega)).2]
      dsimp only [lifted]
      rw [TapeEmbedding.receipt_tapes_old]
      rw [atapes]
      fin_cases j <;> simp [output,PCPPSubstitution.address]
    · fin_cases j
      have he := ct 0
      rw [bf] at he
      simpa [outputSlot,Constants.cfg,output] using he

end NearCubicWires.RepairOrdinary.PCPPNativeConjunctionStart
