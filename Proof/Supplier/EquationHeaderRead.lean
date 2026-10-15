import Proof.MachineModel.OrdinaryMatrixCoefficientHeaders

/-! The same cold three-header parser, specialized to a generic equation
stream suffix. No weak-cut Request or prepared unary dimension is needed. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderRead
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def header (d p g : ℕ) := natWord d++natWord p++natWord g
def word (d p g : ℕ) (suffix : List Bool) := header d p g++suffix
def input (d p g : ℕ) (suffix : List Bool) : Fin 33 → List Bool :=
  fun i => if i=0 then frame (word d p g suffix) else []
noncomputable def machine := MatrixCoefficientHeaders.machine
def budget (d p g : ℕ) (suffix : List Bool) :=
  MatrixScoreHeaders.budget d p (natWord g++suffix)+1+
    MatrixDimensionPrepare.budget (natBitLength g) g

theorem headers_run (d p g : ℕ) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g suffix) (input d p g suffix)=some actual ∧
    actual.final.tapes 0=frame (word d p g suffix) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=word d p g suffix ∧ actual.final.heads 1=(header d p g).length ∧
    actual.final.tapes 12=UnaryTemplate.tape d ∧ actual.final.heads 12=1 ∧
    actual.final.tapes 22=UnaryTemplate.tape p ∧ actual.final.heads 22=1 ∧
    actual.final.tapes 32=UnaryTemplate.tape g ∧ actual.final.heads 32=1 ∧
    actual.steps ≤ budget d p g suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,_,_,_,_,bd,bdh,_,_,_,_,bp,bph,bs⟩ :=
    MatrixScoreHeaders.headers_run d p (natWord g++suffix)
  have he := TapeEmbedding.run_embed MatrixScoreHeaders.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base
  obtain ⟨body,hbody,sourceT,sourceH,_,_,_,_,_,_,gateT,gateH,bodyS⟩ := MatrixDimensionPrepare.prepare_run
    (natWord d++natWord p) suffix (natBitLength g) g (Nat.lt_pow_succ_log_self (by decide) g)
  have hsource : (natWord d++natWord p)++List.replicate (natBitLength g) true++
      false::(binary (natBitLength g) g++suffix)=word d p g suffix := by
    simp [word,header,WilliamsInputHeader.natWord_eq,List.append_assoc]
  have hpre : (natWord d++natWord p).length=2*natBitLength d+1+(2*natBitLength p+1) := by
    simp [WilliamsInputHeader.natWord_eq,Nat.add_assoc]
    omega
  rw [hsource] at hbody sourceT
  let entry : Configuration 11 WilliamsInputHeader.dimensionStates := Composition.leftConfig _
    (MatrixDimensionPrepare.input (word d p g suffix) (natWord d++natWord p).length)
  have hi : RecoveryFocus.config MatrixCoefficientHeaders.slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final MatrixCoefficientHeaders.last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,MatrixCoefficientHeaders.slots,
          entry,Composition.leftConfig,MatrixDimensionPrepare.input,MatrixDimensionField.input,
          MatrixDimensionHeader.input,hpre,Fin.addCases] using bh1
      all_goals simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,MatrixCoefficientHeaders.slots,
        entry,Composition.leftConfig,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Fin.addCases]
    · intro j; fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,MatrixCoefficientHeaders.slots,
          entry,Composition.leftConfig,MatrixDimensionPrepare.input,MatrixDimensionField.input,
          MatrixDimensionHeader.input,Fin.addCases,word,header,List.append_assoc] using bt1
      all_goals simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,MatrixCoefficientHeaders.slots,
        entry,Composition.leftConfig,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Fin.addCases]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config MatrixCoefficientHeaders.slots
    MatrixCoefficientHeaders.slots_injective MatrixDimensionPrepare.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have hj := Composition.run_join MatrixCoefficientHeaders.first MatrixCoefficientHeaders.last
    _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration MatrixScoreHeaders.machine (MatrixScoreHeaders.input
        (natWord d++natWord p++(natWord g++suffix)))))=initialConfiguration machine (input d p g suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,
        MatrixScoreHeaders.input,input,word,header,List.append_assoc,Fin.addCases]
  rw [hin] at hj
  have otherT (i : Fin 23) (hn : RecoveryFocus.pick MatrixCoefficientHeaders.slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 23) (hn : RecoveryFocus.pick MatrixCoefficientHeaders.slots (i.castAdd 10)=none) :
      focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have pick (j : Fin 11) : RecoveryFocus.pick MatrixCoefficientHeaders.slots
      (MatrixCoefficientHeaders.slots j)=some j :=
    RecoveryFocus.pick_slot MatrixCoefficientHeaders.slots MatrixCoefficientHeaders.slots_injective j
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,(otherH 0 (by decide)).trans bh0,?_,?_,
    (otherT 12 (by decide)).trans bd,(otherH 12 (by decide)).trans bdh,
    (otherT 22 (by decide)).trans bp,(otherH 22 (by decide)).trans bph,?_,?_,?_⟩
  · exact (otherT 0 (by decide)).trans (by simpa only [word,header,List.append_assoc] using bt0)
  · change focused.final.tapes (MatrixCoefficientHeaders.slots 0)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using sourceT
  · change focused.final.heads (MatrixCoefficientHeaders.slots 0)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    simp [header,WilliamsInputHeader.natWord_eq,List.length_append,Nat.add_assoc] at sourceH ⊢
    omega
  · change focused.final.tapes (MatrixCoefficientHeaders.slots 10)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using gateT
  · change focused.final.heads (MatrixCoefficientHeaders.slots 10)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using gateH
  · change base.steps+1+focused.steps ≤ budget d p g suffix
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationHeaderRead
