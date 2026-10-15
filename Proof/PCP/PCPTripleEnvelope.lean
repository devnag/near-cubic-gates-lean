import Proof.PCP.PCPTripleCount

/-! The whole repeated-clause envelope prefix consumes the actual clause
count M, creates3M, measures every literal field once, and produces the
global unary capacity outside the serializer bank. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleEnvelope
open LocalBitMultitape
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacitySlots (i : Fin 43) : Fin 48 :=
  if i.val=2 then 3 else ⟨5+i.val,by omega⟩
theorem capacity_injective : Function.Injective capacitySlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [capacitySlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem capacity_not_count (i : Fin 43) : capacitySlots i≠0 := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [capacitySlots] at hv
  split at hv <;> dsimp at hv <;> omega

def extraHeads (pos : ℕ) (i : Fin 43) : ℕ := if i=0 then pos else 0
def extraTapes (source : List Bool) (i : Fin 43) : List Bool := if i=0 then source else []
def input (source : List Bool) (M : ℕ) (i : Fin 48) : List Bool :=
  Fin.addCases (m:=5) (n:=43) (motive:=fun _ => List Bool)
    (PCPTripleCount.input M) (extraTapes source) i
def inputHeads (pos : ℕ) (i : Fin 48) : ℕ :=
  Fin.addCases (m:=5) (n:=43) (motive:=fun _ => ℕ)
    PCPTripleCount.firstHeads (extraHeads pos) i
def outputHeads (pos : ℕ) (i : Fin 48) : ℕ :=
  Fin.addCases (m:=5) (n:=43) (motive:=fun _ => ℕ)
    PCPTripleCount.finalHeads (extraHeads pos) i
noncomputable def first := TapeEmbedding.machine 43 PCPTripleCount.machine
noncomputable def last := RecoveryFocus.machine capacitySlots
  (PCPSerializerCapacity.machine 12 1000000000001)
noncomputable def machine := Composition.machine first last
noncomputable def entry (source : List Bool) (pos M : ℕ) :=
  (⟨machine.start,inputHeads pos,input source M⟩ : Configuration 48 _)
def budget (B M : ℕ) := 12*M+42+
  PCPSerializerCapacity.coefficient 12 1000000000001*(B+1)^13

private theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
private theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl
private theorem joined_steps {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).steps=r.steps+1+s.steps := rfl

theorem envelope_run (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (M : ℕ) (hfields : fields.length=3*M) :
    ∃ r,runFrom machine (budget (FieldList.stream fields).length M)
      (entry (pre++FieldList.stream fields++suffix) pre.length M)=some r ∧
      r.final.heads=outputHeads pre.length ∧
      r.final.tapes 0=CompareMachine.word M ∧
      r.final.tapes 3=CompareMachine.word (3*M) ∧
      r.final.tapes 5=pre++FieldList.stream fields++suffix ∧
      r.final.tapes 6=List.replicate (FieldList.stream fields).length true ∧
      r.final.tapes 37=List.replicate (PCPSerializerReuse.envelope (FieldList.stream fields).length) true ∧
      r.steps ≤ budget (FieldList.stream fields).length M := by
  let source := pre++FieldList.stream fields++suffix
  obtain ⟨base,hb,bh,b0,b3,bs⟩ := PCPTripleCount.count_run M
  let prepared := TapeEmbedding.receipt (extraHeads pre.length) (extraTapes source) base
  have hp := TapeEmbedding.run_embed PCPTripleCount.machine
    (extraHeads pre.length) (extraTapes source) _ _ base hb
  have hsource : prepared.final.tapes 5=source := rfl
  have hcount : prepared.final.tapes 3=CompareMachine.word fields.length := by
    change base.final.tapes 3=_
    rw [hfields]
    exact b3
  have hh : prepared.final.heads=outputHeads pre.length := by
    funext i
    change Fin.addCases (m:=5) (n:=43) (motive:=fun _ => ℕ)
      base.final.heads (extraHeads pre.length) i=outputHeads pre.length i
    rw [bh]
    rfl
  have hin : ∀ j,prepared.final.tapes (capacitySlots j)=
      PCPSerializerCapacity.input 12 source fields.length j := by
    intro j
    fin_cases j
    · exact hsource
    · rfl
    · exact hcount
    all_goals rfl
  have hheads : ∀ j,prepared.final.heads (capacitySlots j)=
      PCPSerializerCapacity.heads 12 pre.length j := by
    intro j
    rw [hh]
    fin_cases j <;> rfl
  obtain ⟨finished,hf,fs,fh,fsource,fcount,fB,fE,other⟩ :=
    PCPSerializerCapacity.focused_run 12 1000000000001 capacitySlots capacity_injective
      pre fields suffix prepared.final.heads prepared.final.tapes hin hheads
  have joined := Composition.run_join first last _ _ _ prepared finished hp hf
  have htime : (12*M+41)+1+
      PCPSerializerCapacity.coefficient 12 1000000000001*((FieldList.stream fields).length+1)^(12+1)=
      budget (FieldList.stream fields).length M := by
    change (12*M+41)+1+
      PCPSerializerCapacity.coefficient 12 1000000000001*((FieldList.stream fields).length+1)^13=_
    unfold budget
    omega
  rw [htime] at joined
  have hs5 : finished.final.tapes 5=source := fsource
  have hs6 : finished.final.tapes 6=List.replicate (FieldList.stream fields).length true := fB
  have hs37 : finished.final.tapes 37=
      List.replicate (PCPSerializerReuse.envelope (FieldList.stream fields).length) true := fE
  refine ⟨Composition.joinedReceipt prepared finished,joined,?_⟩
  rw [joined_heads,joined_tapes,joined_steps]
  have hfinalheads : finished.final.heads=outputHeads pre.length := Eq.trans fh hh
  refine ⟨hfinalheads,?_,?_,hs5,hs6,hs37,?_⟩
  · exact (other 0 capacity_not_count).trans b0
  · have hslot : capacitySlots (PCPSerializerCapacity.old 12 2)=3 := rfl
    rw [hslot,hfields] at fcount
    exact fcount
  · change base.steps+1+finished.steps ≤ _
    unfold budget
    change finished.steps ≤ PCPSerializerCapacity.coefficient 12 1000000000001*
      ((FieldList.stream fields).length+1)^13 at fs
    omega

theorem envelope_budget (fields : List (List Bool)) (M : ℕ) (hfields : fields.length=3*M) :
    budget (FieldList.stream fields).length M ≤ 1000000000000000000*((FieldList.stream fields).length+1)^13 := by
  have hm := PCPSerializerCapacity.MassReady.count_le_mass fields
  rw [hfields] at hm
  have hp : (FieldList.stream fields).length+1 ≤ ((FieldList.stream fields).length+1)^13 := by
    calc
      _=((FieldList.stream fields).length+1)^1 := by simp
      _≤_ := pow_le_pow_right₀ (by omega) (by omega)
  unfold budget PCPSerializerCapacity.coefficient
  norm_num
  omega

end NearCubicWires.RepairOrdinary.PCPTripleEnvelope
