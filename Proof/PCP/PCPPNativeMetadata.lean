import Proof.PCP.PCPPNativeConjunctionStart
import Proof.PCP.PCPPNativeTemplateRawWord

/-! Literal hierarchy Q and clause-count fields plus the same native
oracle descriptor produce every raw count needed by the resource caller.
The actual M sentinel is copied, and a real M template is retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeMetadata
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauseSlots (i : Fin 5) : Fin 52 := i.natAdd 47
theorem clause_injective : Function.Injective clauseSlots := by decide
def heads : Fin 52 → ℕ := Fin.addCases (m := 47) (n := 5) (motive := fun _ => ℕ)
  (fun _ : Fin 47 => 0) PCPPNativeTemplateRaw.heads
def input (bits : List Bool) (Q M : ℕ) : Fin 52 → List Bool :=
  Fin.addCases (m := 47) (n := 5) (motive := fun _ => List Bool)
    (PCPPNativeMetadataPrefix.input bits Q) (MatrixTemplateCopy.wordInput M)
noncomputable def first := TapeEmbedding.machine 5 PCPPNativeMetadataPrefix.machine
noncomputable def second := RecoveryFocus.machine clauseSlots PCPPNativeTemplateRaw.machine
noncomputable def machine := Composition.machine first second
noncomputable def entry (bits : List Bool) (Q M : ℕ) := (⟨machine.start,heads,input bits Q M⟩ : Configuration 52 _)
def budget (R Q s M : ℕ) := PCPPNativeMetadataPrefix.budget R Q s+1+(4*M+16)

theorem metadata_run {R : ℕ} (oracle : BooleanCircuit R) (Q M : ℕ) : ∃ result,
    runFrom machine (budget R Q oracle.size M) (entry (PCPPNative.descriptor oracle) Q M)=some result ∧
    result.steps ≤ budget R Q oracle.size M ∧ result.final.heads=heads ∧
    result.final.tapes 0=PCPPNative.descriptor oracle ∧ result.final.tapes 32=List.replicate oracle.size true ∧
    result.final.tapes 36=List.replicate R true ∧ result.final.tapes 45=List.replicate Q true ∧
    result.final.tapes 48=List.replicate M true ∧ result.final.tapes 50=UnaryTemplate.tape M := by
  obtain ⟨out,⟨a,ha,adata,ah,as⟩,a0,a32,a36,a45,_⟩ := PCPPNativeMetadataPrefix.metadata_run oracle Q
  let lifted := TapeEmbedding.receipt PCPPNativeTemplateRaw.heads (MatrixTemplateCopy.wordInput M) a
  have firstRun := TapeEmbedding.run_embed PCPPNativeMetadataPrefix.machine PCPPNativeTemplateRaw.heads
    (MatrixTemplateCopy.wordInput M) _ _ a ha
  obtain ⟨b,hb,bs,b1,_,b3,bh⟩ := PCPPNativeTemplateRaw.word_run M
  obtain ⟨c,hc,_,cs,ch,ct,other⟩ := RecoveryFocus.dock clauseSlots clause_injective PCPPNativeTemplateRaw.machine _
    lifted.final.heads lifted.final.tapes (PCPPNativeTemplateRaw.wordEntry M)
    (by intro i; simp [lifted,clauseSlots,PCPPNativeTemplateRaw.wordEntry])
    (by intro i; simp [lifted,clauseSlots,PCPPNativeTemplateRaw.wordEntry]) b hb
  have joined := Composition.run_join first second _ _ _ lifted c firstRun hc
  refine ⟨Composition.joinedReceipt lifted c,joined,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps ≤ budget R Q oracle.size M
    rw [cs,bs]
    unfold budget
    omega
  · funext i
    change c.final.heads i=heads i
    refine Fin.addCases (m := 47) (n := 5) (fun j => ?_) (fun j => ?_) i
    · rw [(other (j.castAdd 5) (by
        intro k he
        have hv := congrArg (fun i : Fin 52 => i.val) he
        change 47+k.val=j.val at hv
        omega)).1]
      dsimp only [lifted]
      rw [TapeEmbedding.receipt_heads_old,ah]
      simp [heads]
    · change c.final.heads (clauseSlots j)=heads (j.natAdd 47)
      rw [ch,bh]
      simp [heads]
  · change c.final.tapes 0=_
    rw [(other 0 (by decide)).2]
    exact (congrFun adata 0).trans a0
  · change c.final.tapes 32=_
    rw [(other 32 (by decide)).2]
    exact (congrFun adata 32).trans a32
  · change c.final.tapes 36=_
    rw [(other 36 (by decide)).2]
    exact (congrFun adata 36).trans a36
  · change c.final.tapes 45=_
    rw [(other 45 (by decide)).2]
    exact (congrFun adata 45).trans a45
  · change c.final.tapes (clauseSlots 1)=_
    exact (ct 1).trans b1
  · change c.final.tapes (clauseSlots 3)=_
    exact (ct 3).trans b3

end NearCubicWires.RepairOrdinary.PCPPNativeMetadata
