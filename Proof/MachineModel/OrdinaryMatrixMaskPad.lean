import Proof.MachineModel.OrdinaryMatrixMaskExpand

/-! Whole native mask expansion, capacity padding, and one paid output
rewind. The three physical dimensions are retained at head one; source gate
bits are consumed once and the padded mask is returned at head zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskPad
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (B pad : ℕ) (bits : List Bool) (pos : ℕ) (out : List Bool) : Configuration 5 s :=
  ⟨q,![1,pos,out.length,1,1],![UnaryTemplate.tape B,bits,out,UnaryTemplate.tape bits.length,UnaryTemplate.tape pad]⟩
def slots : Fin 2 → Fin 5 := ![4,2]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 1 MatrixMaskExpand.machine
noncomputable def last := RecoveryFocus.machine slots ZeroBlock.machine
noncomputable def forward := Composition.machine first last
def selected (i : Fin 5) := decide (i=2)
noncomputable def machine := MaskedReset.machine forward selected
def output (B pad : ℕ) (bits : List Bool) := MatrixMaskExpand.output B bits++List.replicate pad false
def forwardBudget (B pad count : ℕ) := MatrixMaskExpand.nativeBudget B count+1+(2*pad+4)
def budget (B pad count : ℕ) := 2*forwardBudget B pad count+2
noncomputable def input (B pad : ℕ) (bits : List Bool) := Rewind.recording (cfg forward.start B pad bits 0 []) 0

theorem forward_run (B pad : ℕ) (bits : List Bool) : ∃ actual,
    runFrom forward (forwardBudget B pad bits.length) (cfg forward.start B pad bits 0 [])=some actual ∧
    actual.final=cfg actual.final.control B pad bits bits.length (output B pad bits) ∧
    actual.steps≤forwardBudget B pad bits.length := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixMaskExpand.all_run B bits []
  have he := TapeEmbedding.run_embed MatrixMaskExpand.machine (![1] : Fin 1 → ℕ)
    ![UnaryTemplate.tape pad] _ _ base hb
  let prepared := TapeEmbedding.receipt (![1] : Fin 1 → ℕ) ![UnaryTemplate.tape pad] base
  obtain ⟨body,hbody,outF,bodyS,_⟩ := ZeroBlock.block_run pad (MatrixMaskExpand.output B bits)
  let entry : Configuration 2 5 := ZeroBlock.config 0 (UnaryTemplate.tape pad) 1 (MatrixMaskExpand.output B bits)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      dsimp only [prepared,TapeEmbedding.receipt]
      rw [bf]
      fin_cases j <;> simp [TapeEmbedding.config,MatrixMaskExpand.cfg_heads,slots,entry,ZeroBlock.config,Fin.addCases]
    · intro j
      dsimp only [prepared,TapeEmbedding.receipt]
      rw [bf]
      fin_cases j <;> simp [TapeEmbedding.config,MatrixMaskExpand.cfg_tapes,slots,entry,ZeroBlock.config,Fin.addCases]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective ZeroBlock.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (![1] : Fin 1 → ℕ) ![UnaryTemplate.tape pad]
      (MatrixMaskExpand.cfg B bits 0 0 []))=cfg forward.start B pad bits 0 [] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,MatrixMaskExpand.cfg_heads,cfg,Fin.addCases]
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,MatrixMaskExpand.cfg_tapes,cfg,Fin.addCases]
  rw [hin] at hj
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_⟩
  · change Composition.rightConfig _ focused.final=_
    dsimp only [Composition.joinedReceipt]
    rw [ff,outF]
    have hp (i : Fin 5) : RecoveryFocus.pick slots i=(![none,none,some 1,none,some 0] : Fin 5 → Option (Fin 2)) i := by
      fin_cases i
      · decide
      · decide
      · exact RecoveryFocus.pick_slot slots slots_injective 1
      · decide
      · exact RecoveryFocus.pick_slot slots slots_injective 0
    apply configuration_ext
    · rfl
    · funext i
      simp only [Composition.rightConfig,RecoveryFocus.config,hp]
      dsimp only [prepared,TapeEmbedding.receipt]
      rw [bf]
      fin_cases i <;> simp [TapeEmbedding.config,MatrixMaskExpand.cfg_heads,cfg,ZeroBlock.config,Fin.addCases,output]
    · funext i
      simp only [Composition.rightConfig,RecoveryFocus.config,hp]
      dsimp only [prepared,TapeEmbedding.receipt]
      rw [bf]
      fin_cases i <;> simp [TapeEmbedding.config,MatrixMaskExpand.cfg_tapes,cfg,ZeroBlock.config,Fin.addCases,output]
  · change base.steps+1+focused.steps≤forwardBudget B pad bits.length
    rw [fs,bodyS]
    unfold forwardBudget
    omega

theorem mask_run (B pad : ℕ) (bits : List Bool) : ∃ actual,
    runFrom machine (budget B pad bits.length) (input B pad bits)=some actual ∧
    (∀ i : Fin 5,actual.final.tapes (i.castAdd 1)=(cfg forward.start B pad bits bits.length (output B pad bits)).tapes i) ∧
    (∀ i : Fin 5,actual.final.heads (i.castAdd 1)=(![1,bits.length,0,1,1] : Fin 5 → ℕ) i) ∧
    actual.final.heads 5=0 ∧ (∃ n,actual.final.tapes 5=List.replicate n false ∧ n≤forwardBudget B pad bits.length) ∧
    actual.steps≤budget B pad bits.length := by
  obtain ⟨base,hb,bf,bs⟩ := forward_run B pad bits
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have hi2 : i=2 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    obtain ⟨hp,_⟩ := prefix_of_run forward (forwardBudget B pad bits.length) (cfg forward.start B pad bits 0 []) base hb
    have h := SelectiveReset.prefix_head hp 2
    simpa [cfg] using h
  obtain ⟨actual,ha,af,as,_⟩ := MaskedReset.reset_run forward selected _ _ base hb hh
  have hs : 2*base.steps+2≤budget B pad bits.length := by unfold budget; omega
  have he := runFrom_moreFuel machine _ (budget B pad bits.length-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hs] at he
  refine ⟨actual,he,?_,?_,?_,?_,as.trans_le hs⟩
  · intro i
    rw [af,bf]
    simp [SelectiveReset.finished,Rewind.config,Fin.addCases_left,cfg]
  · intro i
    rw [af,bf]
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,Fin.addCases,cfg,selected]
  · rw [af]
    rfl
  · exact ⟨base.steps,by rw [af]; rfl,bs⟩

end NearCubicWires.RepairOrdinary.MatrixMaskPad
