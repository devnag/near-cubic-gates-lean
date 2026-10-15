import Proof.MachineModel.OrdinaryMatrixWilliamsProduct

/-! The all-plane loop supplies its actual unary bit offset outside cold
workspace. This ordinary body reruns the explicit request preparation and
produces the requested sign/bit plane, retaining the offset for repetition. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePlane
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 15 → Fin 425 := ![33,424,402,403,32,404,256,321,200,400,376,405,406,407,408]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 16 MatrixSignedEntry.machine
noncomputable def last (negative : Bool) := RecoveryFocus.machine slots (MatrixSignedMaskPass.machine negative)
noncomputable def machine (negative : Bool) := Composition.machine first (last negative)
def extraHeads : Fin 16 → ℕ := fun i => if i=15 then 1 else 0
def extraTapes (bit : ℕ) : Fin 16 → List Bool := fun i => if i=15 then UnaryTemplate.tape (2*bit) else []
noncomputable def input (r : Request) (bit : ℕ) :=
  Composition.leftConfig (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (3+5+3+3))+2+
    (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (2+3))+5+2)+
    (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (2+3))+2))
    (TapeEmbedding.config extraHeads (extraTapes bit) (initialConfiguration MatrixSignedEntry.machine (MatrixSignedEntry.input r)))
noncomputable def budget (r : Request) := MatrixSignedEntry.budget r+1+MatrixSignedMaskPass.budget r

def selected : Fin 7 → Fin 425 := ![12,22,400,200,407,394,424]
noncomputable def values (r : Request) (negative : Bool) (bit : ℕ) : Fin 7 → List Bool :=
  ![UnaryTemplate.tape r.d,UnaryTemplate.tape r.p,UnaryTemplate.tape r.U,UnaryTemplate.tape r.Capacity,
    MatrixSignedPlane.plane r negative bit,MatrixRightPlaneNative.plane r,UnaryTemplate.tape (2*bit)]
def heads : Fin 7 → ℕ := ![0,1,1,1,0,0,1]

theorem local_tapes (r : Request) (negative : Bool) (bit : ℕ) :
    (MatrixSignedMaskPass.input r negative false bit).tapes=
      ![MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape (2*bit),[false],[],UnaryTemplate.tape r.Gates,[],
        UnaryTemplate.tape r.Buckets,UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.Capacity,
        UnaryTemplate.tape r.U,MatrixBucketLeftPlane.plane r,[],[],[],[]] := by
  funext j; fin_cases j
  all_goals simp [MatrixSignedMaskPass.input,MatrixSignedMaskPrepare.input,Composition.leftConfig,TapeEmbedding.config,
    MatrixCoefficientBitPass.input,Rewind.recording,Rewind.config,MatrixCoefficientBitNative.cfg_tapes,
    MatrixSignedMaskPrepare.extraTapes,Fin.addCases]

theorem local_heads (r : Request) (negative : Bool) (bit : ℕ) :
    (MatrixSignedMaskPass.input r negative false bit).heads=(![0,1,0,0,1,0,1,1,1,1,0,0,0,0,0] : Fin 15 → ℕ) := by
  funext j; fin_cases j <;> rfl

theorem input_tapes (r : Request) (bit : ℕ) (i : Fin 425) :
    (input r bit).tapes i=(if i=0 then physicalInput r else if i=424 then UnaryTemplate.tape (2*bit) else []) := by
  fin_cases i <;> rfl

theorem input_heads (r : Request) (bit : ℕ) (i : Fin 425) :
    (input r bit).heads i=(if i=424 then 1 else 0) := by
  fin_cases i <;> rfl

theorem plane_run (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) : ∃ actual,
    runFrom (machine negative) (budget r) (input r bit)=some actual ∧
    (∀ j,actual.final.tapes (selected j)=values r negative bit j) ∧
    (∀ j,actual.final.heads (selected j)=heads j) ∧
    (∀ i : Fin 15,actual.final.tapes ((i.castAdd 1).natAdd 409)=[] ∧ actual.final.heads ((i.castAdd 1).natAdd 409)=0) ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,pT,pH,rightT,rightH,bs⟩ := MatrixSignedEntry.raw_run r
  obtain ⟨same,hs,st,sh,_⟩ := MatrixSignedEntryRetained.retained_run r
  have heq : same=base := Option.some.inj (hs.symm.trans hb)
  subst same
  have hemb := TapeEmbedding.run_embed MatrixSignedEntry.machine extraHeads (extraTapes bit) _ _ base hb
  let prepared := TapeEmbedding.receipt extraHeads (extraTapes bit) base
  obtain ⟨nb,nm,na,body,hr,bodyT,bodyH,_,_,_,bodyS⟩ := MatrixSignedMaskPass.plane_run r negative false bit ht
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes (MatrixSignedMaskPass.input r negative false bit)=
      Composition.restart prepared.final (last negative).start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      rw [local_heads]
      have bh' (j : Fin 15) := bh j
      simp only [MatrixSignedEntry.entry_heads] at bh'
      fin_cases j
      · exact bh' 0
      · rfl
      · exact bh' 2
      · exact bh' 3
      · exact bh' 4
      · exact bh' 5
      · exact bh' 6
      · exact bh' 7
      · exact bh' 8
      · exact bh' 9
      · exact bh' 10
      · exact bh' 11
      · exact bh' 12
      · exact bh' 13
      · exact bh' 14
    · intro j
      rw [local_tapes]
      have bt' (j : Fin 15) := bt j
      simp only [MatrixSignedEntry.entry_tapes] at bt'
      fin_cases j
      · exact bt' 0
      · rfl
      · exact bt' 2
      · exact bt' 3
      · exact bt' 4
      · exact bt' 5
      · exact bt' 6
      · exact bt' 7
      · exact bt' 8
      · exact bt' 9
      · exact bt' 10
      · exact bt' 11
      · exact bt' 12
      · exact bt' 13
      · exact bt' 14
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective (MatrixSignedMaskPass.machine negative)
    prepared.final.heads prepared.final.tapes _ _ body hr
  rw [hi] at hf
  have hj := Composition.run_join first (last negative) _ _ _ prepared focused hemb hf
  have localT (j : Fin 15) : focused.final.tapes (slots j)=MatrixSignedMaskPass.output r negative false bit nb nm na j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bodyT]
  have localH (j : Fin 15) : focused.final.heads (slots j)=MatrixSignedMaskPass.finalHeads r j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bodyH]
  have retained (i : Fin 409) (hn : RecoveryFocus.pick slots (i.castAdd 16)=none) :
      focused.final.tapes (i.castAdd 16)=base.final.tapes i ∧ focused.final.heads (i.castAdd 16)=base.final.heads i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (retained 12 (by decide)).1.trans (st 0)
    · exact (retained 22 (by decide)).1.trans pT
    · exact localT 9
    · exact localT 8
    · exact localT 13
    · exact (retained 394 (by decide)).1.trans rightT
    · exact localT 1
  · intro j; fin_cases j
    · exact (retained 12 (by decide)).2.trans (sh 0)
    · exact (retained 22 (by decide)).2.trans pH
    · exact localH 9
    · exact localH 8
    · exact localH 13
    · exact (retained 394 (by decide)).2.trans rightH
    · exact localH 1
  · intro i
    change focused.final.tapes ((i.castAdd 1).natAdd 409)=[] ∧ focused.final.heads ((i.castAdd 1).natAdd 409)=0
    have hn : RecoveryFocus.pick slots ((i.castAdd 1).natAdd 409)=none := by fin_cases i <;> decide
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    fin_cases i <;> exact ⟨rfl,rfl⟩
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixVariablePlane
