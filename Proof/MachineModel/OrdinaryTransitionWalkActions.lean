import Proof.MachineModel.OrdinaryTransitionWalkCounters

/-! The array emitter consumes exactly the selected decoded action's tags,
claimed read vector and current heads. These identities introduce no physical
fields: they identify the fields returned by the paid canonical lookup. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def actionTag (write : Option Bool) (move : HeadMove) : TagMachine.Word :=
  TagMachine.extend (writeCode write++moveCode move)
def actionItems {t s : ℕ} (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) : List TransitionArray.Item :=
  List.ofFn fun i=>⟨actionTag (a.write i) (a.move i),reads i,heads i⟩

theorem actionTag_word (write : Option Bool) (move : HeadMove) :
    TagMachine.tagWord (actionTag write move)=writeCode write++moveCode move :=
  Sequential.tagWord_extend _ (by simp)

theorem actionTag_move (write : Option Bool) (move : HeadMove) :
    decodeMove [(actionTag write move) 2,(actionTag write move) 3]=move := by
  cases write with
  | none=>cases move <;> rfl
  | some b=>cases b <;> cases move <;> rfl

theorem actionTag_after (write : Option Bool) (move : HeadMove) (read : Bool) :
    TransitionTag.after (actionTag write move) read=write.getD read := by
  cases write with
  | none=>cases move <;> rfl
  | some b=>cases b <;> cases move <;> rfl

theorem tags_eq_flat (es : List TransitionArray.Item) :
    TransitionArray.tags es=(es.map fun e=>TagMachine.tagWord e.tag).flatten := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simp only [TransitionArray.tags,List.map_cons,List.flatten_cons,ih]

theorem scans_eq_map (es : List TransitionArray.Item) : TransitionArray.scans es=es.map (·.read) := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simpa only [TransitionArray.scans,List.map_cons] using congrArg (List.cons e.read) ih

theorem fields_eq_flat (w : ℕ) (es : List TransitionArray.Item) :
    TransitionArray.fields w es=(es.map fun e=>frame (binary w e.head)).flatten := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simp only [TransitionArray.fields,List.map_cons,List.flatten_cons,ih]

theorem nextFields_eq_flat (w : ℕ) (es : List TransitionArray.Item) :
    TransitionArray.nextFields w es=(es.map fun e=>frame (binary w (TransitionArray.nextHead e))).flatten := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simp only [TransitionArray.nextFields,List.map_cons,List.flatten_cons,ih]

theorem actionItems_tags {t s : ℕ} (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) :
    TransitionArray.tags (actionItems a heads reads)=
      (List.ofFn fun i=>writeCode (a.write i)++moveCode (a.move i)).flatten := by
  simp only [tags_eq_flat,actionItems,List.map_ofFn,Function.comp_def,actionTag_word]

theorem actionItems_scans {t s : ℕ} (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) :
    TransitionArray.scans (actionItems a heads reads)=List.ofFn reads := by
  simp only [scans_eq_map,actionItems,List.map_ofFn,Function.comp_def]

theorem actionItems_fields {t s : ℕ} (w : ℕ) (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) :
    TransitionArray.fields w (actionItems a heads reads)=(List.ofFn fun i=>frame (binary w (heads i))).flatten := by
  simp only [fields_eq_flat,actionItems,List.map_ofFn,Function.comp_def]

theorem actionItems_nextFields {t s : ℕ} (w : ℕ) (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) :
    TransitionArray.nextFields w (actionItems a heads reads)=
      (List.ofFn fun i=>frame (binary w ((a.move i).apply (heads i)))).flatten := by
  simp only [nextFields_eq_flat,actionItems,List.map_ofFn,Function.comp_def,TransitionArray.nextHead,actionTag_move]

theorem actionItems_valid {t s : ℕ} (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) :
    ∀ e∈actionItems a heads reads,TagMachine.valid true e.tag=true := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact Sequential.canonical_tags_valid _ _

theorem actionItems_heads {t s : ℕ} (w : ℕ) (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool)
    (hh : ∀ i,heads i+1<2^w) : ∀ e∈actionItems a heads reads,e.head+1<2^w := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact hh i

theorem action_next_slice {t s : ℕ} (j : ℕ) (a : Action t s) :
    slice (actionCode j (some a)) 1 j=binary j a.nextControl.val := by
  simp only [actionCode,slice,List.drop_succ_cons,List.drop_zero]
  have h := List.take_left (l₁:=fixedBits j a.nextControl.val)
    (l₂:=(List.ofFn fun i=>writeCode (a.write i)++moveCode (a.move i)).flatten)
  rw [fixedBits_length] at h
  exact h.trans (fixedBits_binary j a.nextControl.val)

theorem action_tags_slice {t s : ℕ} (j : ℕ) (a : Action t s) :
    slice (actionCode j (some a)) (1+j) (4*t)=
      (List.ofFn fun i=>writeCode (a.write i)++moveCode (a.move i)).flatten := by
  let payload := (List.ofFn fun i=>writeCode (a.write i)++moveCode (a.move i)).flatten
  have hl : payload.length=4*t := by
    have h := flat_ofFn_length (w:=4) (fun i=>writeCode (a.write i)++moveCode (a.move i)) (by intro i; simp)
    change payload.length=t*4 at h
    omega
  change ((true::(fixedBits j a.nextControl.val++payload)).drop (1+j)).take (4*t)=payload
  rw [Nat.add_comm 1 j,List.drop_succ_cons]
  have hd := List.drop_left (l₁:=fixedBits j a.nextControl.val) (l₂:=payload)
  rw [fixedBits_length] at hd
  rw [hd,←hl,List.take_length]

end NearCubicWires.RepairOrdinary.TransitionWalk
