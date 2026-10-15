import Proof.MachineModel.OrdinaryMatrixScoreHeaders

/-! The assignment count U=2^d is produced from a physical unary d. Clock
fields print its one-hot binary word; normalizing and unary expansion are
executed calls. No numerical exponentiation is a machine instruction. -/
namespace NearCubicWires.RepairOrdinary.MatrixScorePower
open LocalBitMultitape SignedSortKey RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def normSlots : Fin 5 → Fin 14 := ![2,1,6,7,8]
def unarySlots : Fin 7 → Fin 14 := ![2,9,10,11,12,6,13]
def fields : Machine 14 14 := TapeEmbedding.machine 8 ClockFields.machine
noncomputable def normalize : Machine 14 6 := RecoveryFocus.machine normSlots ClockNormalize.machine
noncomputable def prepare : Machine 14 20 := Composition.machine fields normalize
noncomputable def unary := RecoveryFocus.machine unarySlots MatrixUnaryTemplate.machine
noncomputable def machine := Composition.machine prepare unary
def input (d : ℕ) : Fin 14 → List Bool := fun i => if i.val=0 then List.replicate d true else []
def budget (d : ℕ) := 8*d+40+MatrixUnaryTemplate.budget (d+3) (2^d)

theorem power_run (d : ℕ) :
    ∃ actual : ExecutionReceipt 14 (20+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))),
      run machine (budget d) (input d)=some actual ∧
      actual.final.tapes 0=List.replicate d true ∧
      actual.final.tapes 2=List.replicate (d+3) true ∧
      actual.final.tapes 6=frame (binary (d+3) (2^d)) ∧
      actual.final.tapes 13=UnaryTemplate.tape (2^d) ∧ actual.final.heads 13=1 ∧
      (∀ i,i≠13 → actual.final.heads i=0) ∧ actual.steps≤budget d := by
  obtain ⟨base,hb,ht0,ht1,ht2,_,_,_,hbh,hbs⟩ := ClockFields.fields_run d
  have he := TapeEmbedding.run_embed ClockFields.machine (fun _ : Fin 8 => 0)
    (fun _ : Fin 8 => []) _ _ base hb
  let first := TapeEmbedding.receipt (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) base
  have hh : ∀ i,first.final.heads i=0 := by
    intro i
    fin_cases i <;> simp [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hbh]
  obtain ⟨norm,hn,hn0,_,hn2,_,_,hnh,hns⟩ := ClockScalarFields.scalar_run (d+3)
    (List.replicate d false++[true]) (by simp)
  have hp : RadixSemantics.value (List.replicate d false++[true])=2^d := by
    simp [RadixSemantics.value_append,RadixSemantics.value]
  rw [hp] at hn2
  let normEntry := initialConfiguration ClockNormalize.machine
    (ClockNormalize.input (d+3) (List.replicate d false++[true]))
  have hnorm : RecoveryFocus.config normSlots first.final.heads first.final.tapes normEntry=
      Composition.restart first.final normalize.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [hh,normEntry,initialConfiguration]
    · intro i
      fin_cases i
      · exact ht2
      · exact ht1
      all_goals rfl
  obtain ⟨middle,hm,hmf,hms⟩ := RecoveryFocus.run_config normSlots (by decide) ClockNormalize.machine
    first.final.heads first.final.tapes _ normEntry norm hn
  rw [hnorm] at hm
  have hj := Composition.run_join fields normalize (4*d+22) (4*(d+3)+4) _ first middle he hm
  let prepared := Composition.joinedReceipt first middle
  have mh : ∀ i,prepared.final.heads i=0 := by
    intro i
    change middle.final.heads i=0
    rw [hmf]
    cases h : RecoveryFocus.pick normSlots i <;> simp [RecoveryFocus.config,h,hh,hnh]
  have pickN (i : Fin 5) : RecoveryFocus.pick normSlots (normSlots i)=some i :=
    RecoveryFocus.pick_slot normSlots (by decide) i
  have m2 : prepared.final.tapes 2=List.replicate (d+3) true := by
    change middle.final.tapes (normSlots 0)=_
    rw [hmf]; simpa only [RecoveryFocus.config,pickN] using hn0
  have m6 : prepared.final.tapes 6=frame (binary (d+3) (2^d)) := by
    change middle.final.tapes (normSlots 2)=_
    rw [hmf]; simpa only [RecoveryFocus.config,pickN] using hn2
  have m0 : prepared.final.tapes 0=List.replicate d true := by
    change middle.final.tapes 0=_
    rw [hmf]
    simpa [RecoveryFocus.config,show RecoveryFocus.pick normSlots 0=none by decide,
      first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using ht0
  have blank (i : Fin 14) (hi : (9 : ℕ) ≤ i.val) : prepared.final.tapes i=[] := by
    change middle.final.tapes i=[]
    rw [hmf]
    have hn' : RecoveryFocus.pick normSlots i=none := by
      fin_cases i <;> simp at hi
      all_goals decide
    simp only [RecoveryFocus.config,hn']
    fin_cases i <;> simp at hi
    all_goals simp [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  obtain ⟨last,hl,hl0,hl5,hl6,hlh,hlheads,hls⟩ := MatrixUnaryTemplate.template_run (d+3) (2^d)
    (by exact Nat.pow_lt_pow_right (by decide) (by omega))
  let entry := initialConfiguration MatrixUnaryTemplate.machine (MatrixUnaryTemplate.input (d+3) (2^d))
  have hentry : RecoveryFocus.config unarySlots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final unary.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [mh,entry,initialConfiguration]
    · intro i
      fin_cases i
      · exact m2
      · exact blank 9 (by decide)
      · exact blank 10 (by decide)
      · exact blank 11 (by decide)
      · exact blank 12 (by decide)
      · exact m6
      · exact blank 13 (by decide)
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config unarySlots (by decide) MatrixUnaryTemplate.machine
    prepared.final.heads prepared.final.tapes _ entry last hl
  rw [hentry] at hf
  have hall := Composition.run_join prepare unary ((4*d+22)+1+(4*(d+3)+4))
    (MatrixUnaryTemplate.budget (d+3) (2^d)) _ prepared focused hj hf
  have hin : Composition.leftConfig _ (Composition.leftConfig 6
      (TapeEmbedding.config (fun _ : Fin 8 => 0) (fun _ : Fin 8 => [])
        (initialConfiguration ClockFields.machine (Fin.addCases
          (motive := fun _ : Fin (5+1) => List Bool) ![List.replicate d true,[],[],[],[]]
          (fun _ : Fin 1 => [])))))=initialConfiguration machine (input d) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases,input]
  rw [hin] at hall
  have htime : (4*d+22)+1+(4*(d+3)+4)+1+MatrixUnaryTemplate.budget (d+3) (2^d)=budget d := by
    unfold budget; omega
  rw [htime] at hall
  have pickU (i : Fin 7) : RecoveryFocus.pick unarySlots (unarySlots i)=some i :=
    RecoveryFocus.pick_slot unarySlots (by decide) i
  refine ⟨Composition.joinedReceipt prepared focused,hall,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simpa only [RecoveryFocus.config,show RecoveryFocus.pick unarySlots 0=none by decide] using m0
  · change focused.final.tapes (unarySlots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickU] using hl0
  · change focused.final.tapes (unarySlots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickU] using hl5
  · change focused.final.tapes (unarySlots 6)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickU] using hl6
  · change focused.final.heads (unarySlots 6)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickU] using hlh
  · intro i hi
    change focused.final.heads i=0
    rw [hff]
    cases h : RecoveryFocus.pick unarySlots i with
    | none => simp [RecoveryFocus.config,h,mh]
    | some j =>
      have hj6 : j≠6 := by
        intro hj
        subst j
        exact hi (RecoveryFocus.slot_of_pick unarySlots h).symm
      simpa only [RecoveryFocus.config,h] using hlheads j hj6
  · change first.steps+1+middle.steps+1+focused.steps≤_
    rw [hms,hfs]
    have hfsteps : first.steps=4*d+22 := hbs
    rw [hfsteps,hns]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScorePower
