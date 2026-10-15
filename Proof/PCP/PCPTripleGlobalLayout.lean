import Proof.PCP.PCPTriple

/-! The measured global envelope and counted serializer use one physical
layout. No serializer capacity, scratch backing or triple count is supplied
by the source interface. Only its actual M and native clause stream enter. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleGlobal
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 133) : Fin 180 :=
  if h0 : i.val=0 then 5 else if h130 : i.val=130 then 37 else if h132 : i.val=132 then 0
  else ⟨48+i.val,by have hi := i.isLt; omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

noncomputable def first := TapeEmbedding.machine 132 PCPTripleEnvelope.machine
noncomputable def last := RecoveryFocus.machine slots PCPTripleCold.machine
noncomputable def machine := Composition.machine first last
def input (M : ℕ) (source : List Bool) : Fin 180 → List Bool :=
  Fin.addCases (m:=48) (n:=132) (PCPTripleEnvelope.input source M) (fun _ => [])
def heads (pos : ℕ) : Fin 180 → ℕ :=
  Fin.addCases (m:=48) (n:=132) (PCPTripleEnvelope.inputHeads pos) (fun _ => 0)
noncomputable def entry (M : ℕ) (source : List Bool) (pos : ℕ) :=
  (⟨machine.start,heads pos,input M source⟩ : Configuration 180 _)
def budget (B M : ℕ) := PCPTripleEnvelope.budget B M+1+PCPTripleCold.budget (envelope B) M

theorem flatten_stream (groups : List (List (List Bool))) :
    FieldList.stream groups.flatten=PCPTripleLoop.stream groups := by
  induction groups with
  | nil => rfl
  | cons fields groups ih =>
    simp only [List.flatten_cons,FieldList.stream,List.map_append,List.flatten_append] at ih ⊢
    rw [PCPTripleLoop.stream_cons,ih]
    simp only [FieldList.stream]

theorem flatten_length (groups : List (List (List Bool)))
    (hthree : ∀ fields∈groups,fields.length=3) : groups.flatten.length=3*groups.length := by
  induction groups with
  | nil => simp
  | cons fields groups ih =>
    have hf := hthree fields (by simp)
    have ht := ih (by intro g hg; exact hthree g (by simp [hg]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,hf,ht]
    omega

theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl
theorem repeat_tape {s : ℕ} (phase : Fin 5) (c : Configuration 132 s)
    (M head : ℕ) (i : Fin 132) :
    (RepeatMachine.cfg phase c M head).tapes (i.castAdd 1)=c.tapes i := by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
theorem repeat_head {s : ℕ} (phase : Fin 5) (c : Configuration 132 s)
    (M head : ℕ) (i : Fin 132) :
    (RepeatMachine.cfg phase c M head).heads (i.castAdd 1)=c.heads i := by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]

theorem cold_head_zero (pos : ℕ) (i : Fin 132) (hi : i≠0) :
    PCPTripleCold.heads pos 0 (i.castAdd 1)=0 := by
  simp only [PCPTripleCold.heads,Fin.addCases_left]
  fin_cases i <;> first | contradiction | rfl

end NearCubicWires.RepairOrdinary.PCPTripleGlobal
