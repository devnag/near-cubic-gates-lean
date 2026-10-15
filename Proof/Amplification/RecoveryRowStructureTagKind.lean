import Proof.Amplification.RecoveryRowStructureTagStore

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagKindSlots : Fin 5→Fin 52 := ![17,43,44,45,22]
theorem tagKindSlots_injective : Function.Injective tagKindSlots := by decide
noncomputable def tagKindMachine := RecoveryFocus.machine tagKindSlots RecoveryRowKind.machine

def classified (d : Data) (tag : List Bool) : Data :=
  setFlag (setFlag (setFlag
    (setTag d (ZeroPadding.pad (RecoveryReusableUnpair.capacity d.state.bits) (frame (RecoveryRowKind.after tag))))
      0 (decide (value tag=0))) 1 (decide (value tag=1))) 2 (decide (value tag=2))

theorem classified_tapes (d : Data) (capacity : Nat) (tag : List Bool) :
    (cfg (classified d tag) capacity (0 : Fin 1)).tapes=
      Function.update (Function.update (Function.update (Function.update (cfg d capacity (0 : Fin 1)).tapes
        17 (ZeroPadding.pad (RecoveryReusableUnpair.capacity d.state.bits) (frame (RecoveryRowKind.after tag))))
        43 [decide (value tag=0)]) 44 [decide (value tag=1)]) 45 [decide (value tag=2)] := by
  unfold classified
  rw [cfg_flag,cfg_flag,cfg_flag,cfg_tag_store]
  rfl

theorem classified_flags (d : Data) (tag : List Bool) (i : Fin 3) :
    (classified d tag).flags i=decide (value tag=i.val) := by
  fin_cases i <;> simp [classified,setFlag,setTag]

theorem tag_space (d : Data) (tag : List Bool) (hw : tag.length=d.state.bits.length) :
    2*tag.length+1≤RecoveryReusableUnpair.capacity d.state.bits := by
  rw [hw]
  change 2*d.state.bits.length+1≤8192*(d.state.bits.length+1)^2
  nlinarith

theorem classified_valid (d : Data) (tag word : List Bool) (hd : d.Valid word)
    (hw : tag.length=d.state.bits.length) : (classified d tag).Valid word := by
  have hl : (RecoveryRowKind.after tag).length=tag.length := by
    simp [RecoveryRowKind.after,RecoveryLiteralTag.predWord,RecoveryListPredecessor.result_length]
  have hs : (ZeroPadding.pad (RecoveryReusableUnpair.capacity d.state.bits) (frame (RecoveryRowKind.after tag))).length≤
      RecoveryReusableUnpair.capacity d.state.bits := by
    rw [ZeroPadding.pad_length,frame_length,hl]
    exact max_le le_rfl (tag_space d tag hw)
  exact setTag_valid d _ word hd hs

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem kind_output (ambient : Fin 52→List Bool) (tag : List Bool) (capacity padding : Nat)
    (hreset : ambient 22=List.replicate capacity false) :
    install tagKindSlots ambient
      (kindTapes (RecoveryRowKind.after tag) (fun i=>decide (value tag=i.val)) capacity padding)=
      Function.update (Function.update (Function.update (Function.update ambient
        17 (ZeroPadding.pad padding (frame (RecoveryRowKind.after tag))))
        43 [decide (value tag=0)]) 44 [decide (value tag=1)]) 45 [decide (value tag=2)] := by
  apply install_eq tagKindSlots tagKindSlots_injective
  · intro j
    fin_cases j
    · simp [tagKindSlots,kindTapes]
    · simp [tagKindSlots,kindTapes]
    · simp [tagKindSlots,kindTapes]
    · simp [tagKindSlots,kindTapes]
    · exact hreset.symm
  · intro i hi
    have h17 : i≠17 := by intro he; exact hi 0 he.symm
    have h43 : i≠43 := by intro he; exact hi 1 he.symm
    have h44 : i≠44 := by intro he; exact hi 2 he.symm
    have h45 : i≠45 := by intro he; exact hi 3 he.symm
    simp only [Function.update_of_ne h17,Function.update_of_ne h43,Function.update_of_ne h44,Function.update_of_ne h45]

theorem tag_kind_run (d : Data) (capacity : Nat) (tag word : List Bool) (hd : d.Valid word)
    (hw : tag.length=d.state.bits.length)
    (hsource : (cfg d capacity (0 : Fin 1)).tapes 17=
      ZeroPadding.pad (RecoveryReusableUnpair.capacity d.state.bits) (frame tag)) :
    ∃ r,runFrom tagKindMachine (RecoveryRowKind.time tag) (cfg d capacity tagKindMachine.start)=some r ∧
      r.final=cfg (classified d tag) capacity r.final.control ∧ r.steps=RecoveryRowKind.time tag ∧
      (classified d tag).Valid word ∧
      ∀ i,(classified d tag).flags i=decide (value tag=i.val) := by
  have hreset : 2*tag.length+1≤d.state.capacity :=
    (tag_space d tag hw).trans ((Nat.le_succ _).trans hd.2.1.reset)
  have h := tag_kind_ready tag d.flags d.state.capacity (RecoveryReusableUnpair.capacity d.state.bits)
  rw [Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hheads,htapes,hsteps⟩ := h.focus_at tagKindSlots tagKindSlots_injective
    (cfg d capacity tagKindMachine.start).heads (cfg d capacity tagKindMachine.start).tapes
    (by intro j; fin_cases j <;> first | exact hsource | rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hsteps,classified_valid d tag word hd hw,classified_flags d tag⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans ((kind_output (cfg d capacity (0 : Fin 1)).tapes tag d.state.capacity
      (RecoveryReusableUnpair.capacity d.state.bits) (by rfl)).trans (classified_tapes d capacity tag).symm)

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
