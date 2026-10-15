import Proof.MachineModel.OrdinaryMatrixWilliamsHeaderEntry

/-! Produce the actual raw-matrix bit count U*Capacity from the two
retained sentinels, paying their head adjustment and the complete product. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsDimensions
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def retreat : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if i=0 ∨ i=5 then .left else .stay⟩ else none
noncomputable def countMachine := Composition.machine retreat MatrixTemplateProduct.machine
noncomputable def countEntry (d e : ℕ) : Configuration 12 23 :=
  ⟨countMachine.start,fun i => if i=0 ∨ i=5 then 1 else 0,MatrixTemplateProduct.input d e⟩

theorem count_run (d e : ℕ) : ∃ actual,
    runFrom countMachine (8*d*e+10*d+30) (countEntry d e)=some actual ∧
    actual.final.tapes 0=UnaryTemplate.tape d ∧ actual.final.tapes 5=UnaryTemplate.tape e ∧
    actual.final.tapes 10=UnaryTemplate.tape (d*e) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps=8*d*e+10*d+30 := by
  let entry : Configuration 12 2 := ⟨0,fun i => if i=0 ∨ i=5 then 1 else 0,MatrixTemplateProduct.input d e⟩
  let done : Configuration 12 2 := ⟨1,fun _ => 0,MatrixTemplateProduct.input d e⟩
  have hstep : step retreat entry=some done := by
    simp [step,retreat,entry]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨base,hb,bf,bs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨body,hr,b0,b5,b10,bh,bt⟩ := MatrixTemplateProduct.product_run d e
  have hi : initialConfiguration MatrixTemplateProduct.machine (MatrixTemplateProduct.input d e)=
      Composition.restart base.final MatrixTemplateProduct.machine.start := by rw [bf]; rfl
  unfold run at hr
  rw [hi] at hr
  have hj := Composition.run_join retreat MatrixTemplateProduct.machine _ _ _ base body hb hr
  have ht : 1+1+(8*d*e+10*d+28)=8*d*e+10*d+30 := by omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt base body,hj,b0,b5,b10,bh,?_⟩
  change base.steps+1+body.steps=_
  omega

def slots : Fin 12 → Fin 422 := ![400,412,413,414,415,200,416,417,418,419,420,421]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 10 MatrixWilliamsHeaderEntry.machine
noncomputable def last := RecoveryFocus.machine slots countMachine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 422 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixWilliamsHeaderEntry.budget r+1+(8*r.U*r.Capacity+10*r.U+30)
def selected : Fin 7 → Fin 422 := ![400,200,407,394,409,410,420]
noncomputable def values (r : Request) : Fin 7 → List Bool :=
  ![UnaryTemplate.tape r.U,UnaryTemplate.tape r.Capacity,MatrixSignedPlane.plane r false 0,
    MatrixRightPlaneNative.plane r,RepairRepresentation.natWord r.U,UnaryTemplate.tape (2*r.d+3),
    UnaryTemplate.tape (r.U*r.Capacity)]

theorem raw_run (r : Request) (hp : 0<r.p) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (selected j)=values r j) ∧
    (∀ j,actual.final.heads (selected j)=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixWilliamsHeaderEntry.raw_run r hp
  have hemb := TapeEmbedding.run_embed MatrixWilliamsHeaderEntry.machine (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base
  obtain ⟨body,hr,b0,b5,b10,bodyH,bodyS⟩ := count_run r.U r.Capacity
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes (countEntry r.U r.Capacity)=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact bh 0
      · rfl
      · rfl
      · rfl
      · rfl
      · exact bh 1
      all_goals rfl
    · intro j; fin_cases j
      · exact bt 0
      · rfl
      · rfl
      · rfl
      · rfl
      · exact bt 1
      all_goals rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective countMachine
    prepared.final.heads prepared.final.tapes _ (countEntry r.U r.Capacity) body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused hemb hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration MatrixWilliamsHeaderEntry.machine (MatrixWilliamsHeaderEntry.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 12) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 12) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have retained (i : Fin 412) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i ∧ focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (localT 0).trans b0
    · exact (localT 5).trans b5
    · exact (retained 407 (by decide)).1.trans (bt 2)
    · exact (retained 394 (by decide)).1.trans (bt 3)
    · exact (retained 409 (by decide)).1.trans (bt 4)
    · exact (retained 410 (by decide)).1.trans (bt 5)
    · exact (localT 10).trans b10
  · intro j; fin_cases j
    · exact (localH 0).trans (bodyH 0)
    · exact (localH 5).trans (bodyH 5)
    · exact (retained 407 (by decide)).2.trans (bh 2)
    · exact (retained 394 (by decide)).2.trans (bh 3)
    · exact (retained 409 (by decide)).2.trans (bh 4)
    · exact (retained 410 (by decide)).2.trans (bh 5)
    · exact (localH 10).trans (bodyH 10)
  · change base.steps+1+focused.steps≤budget r
    rw [fs,bodyS]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixWilliamsDimensions
