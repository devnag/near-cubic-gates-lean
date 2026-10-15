import Proof.MachineModel.OrdinaryMatrixPacketPositive

/-! The original request physically supplies the p guard sentinel.
All header work is outside the cold packet workspace. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketHeader
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) (E : ℕ) := MatrixPacketRestore.tapes a E+22
noncomputable def old (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixPacketRestore.tapes a E)) : Fin (tapes a E) := i.castAdd 22
noncomputable def extra (a : WilliamsAlgorithm) (E : ℕ) (i : Fin 22) : Fin (tapes a E) := i.natAdd (MatrixPacketRestore.tapes a E)
noncomputable def slots (a : WilliamsAlgorithm) (E : ℕ) (j : Fin 23) : Fin (tapes a E) :=
  if h0 : j.val=0 then old a E (MatrixPacketRestore.copySlots a E 0)
  else if h22 : j.val=22 then extra a E 0
  else extra a E ⟨j.val,by have h:=j.isLt; omega⟩
theorem slots_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (slots a E) := by
  intro i j he
  have hs:=(MatrixPacketRestore.copySlots a E 0).isLt
  have hi:=i.isLt
  have hj:=j.isLt
  have hv:=congrArg (fun k : Fin (tapes a E) => k.val) he
  unfold slots at hv
  repeat' split at hv
  all_goals simp only [old,extra,Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals exact Fin.ext (by omega)

theorem slots_extra (a : WilliamsAlgorithm) (E : ℕ) (j : Fin 23) (hj : j.val≠0) :
    ∃ k,slots a E j=extra a E k := by
  unfold slots
  rw [dif_neg hj]
  split
  · exact ⟨0,rfl⟩
  · exact ⟨_,rfl⟩

noncomputable def input (a : WilliamsAlgorithm) (E : ℕ) (r : Request) : Fin (tapes a E) → List Bool :=
  Fin.addCases (MatrixPacketColdPrepare.cold a E r) (fun _ => [])
noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) := RecoveryFocus.machine (slots a E) MatrixScoreHeaders.machine
/-- Everything after the two parsed dimensions: the gate count, the weight count and the columns of `φ`
(the header of `MatrixScoreBatch.header`), then the cuts. -/
def suffix (r : Request) :=
  natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p)
def budget (r : Request) := MatrixScoreHeaders.budget r.d r.p (suffix r)
theorem word_eq (r : Request) : natWord r.d++natWord r.p++suffix r=word r := by
  simp [word,header,suffix,List.append_assoc]

theorem input_old (a : WilliamsAlgorithm) (E : ℕ) (r : Request) (i : Fin (MatrixPacketRestore.tapes a E)) :
    input a E r (old a E i)=MatrixPacketColdPrepare.cold a E r i :=
  Fin.addCases_left (motive := fun _ => List Bool) (left := MatrixPacketColdPrepare.cold a E r)
    (right := fun _ : Fin 22 => []) i
theorem input_extra (a : WilliamsAlgorithm) (E : ℕ) (r : Request) (i : Fin 22) : input a E r (extra a E i)=[] :=
  Fin.addCases_right (motive := fun _ => List Bool) (left := MatrixPacketColdPrepare.cold a E r)
    (right := fun _ : Fin 22 => []) i

theorem input_slots (a : WilliamsAlgorithm) (E : ℕ) (r : Request) (j : Fin 23) :
    input a E r (slots a E j)=MatrixScoreHeaders.input (word r) j := by
  by_cases hj : j.val=0
  · have he : j=0 := Fin.ext hj
    subst j
    have h:=input_old a E r (MatrixPacketRestore.copySlots a E 0)
    apply h.trans
    simp [MatrixPacketColdPrepare.cold,MatrixScoreHeaders.input,physicalInput]
  · obtain ⟨k,hk⟩:=slots_extra a E j hj
    rw [hk,input_extra]
    simp [MatrixScoreHeaders.input,hj]

theorem old_outside (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixPacketRestore.tapes a E))
    (hi : i≠MatrixPacketRestore.copySlots a E 0) : ∀ j,slots a E j≠old a E i := by
  intro j he
  by_cases hj : j.val=0
  · have h0 : j=0 := Fin.ext hj
    subst j
    exact hi (Fin.ext (congrArg (fun k : Fin (tapes a E) => k.val) he.symm))
  · obtain ⟨k,hk⟩:=slots_extra a E j hj
    rw [hk] at he
    have hv:=congrArg (fun z : Fin (tapes a E) => z.val) he
    change MatrixPacketRestore.tapes a E+k.val=i.val at hv
    have hb:=i.isLt
    omega

theorem header_run (a : WilliamsAlgorithm) (E : ℕ) (r : Request) : ∃ actual,
    run (machine a E) (budget r) (input a E r)=some actual ∧
    (∀ i,actual.final.tapes (old a E i)=MatrixPacketColdPrepare.cold a E r i ∧ actual.final.heads (old a E i)=0) ∧
    actual.final.tapes (extra a E 0)=UnaryTemplate.tape r.p ∧ actual.final.heads (extra a E 0)=1 ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,sourceT,sourceH,_,_,_,_,_,_,_,_,_,_,_,_,pT,pH,bs⟩:=MatrixScoreHeaders.headers_run r.d r.p (suffix r)
  rw [word_eq] at hb sourceT
  let entry:=initialConfiguration MatrixScoreHeaders.machine (MatrixScoreHeaders.input (word r))
  have hin : RecoveryFocus.config (slots a E) (fun _ => 0) (input a E r) entry=
      initialConfiguration (machine a E) (input a E r) := by
    apply WilliamsSourceCrop.focus_same (slots a E) (initialConfiguration (machine a E) (input a E r)) entry
    · intro j; rfl
    · exact input_slots a E r
  obtain ⟨actual,ha,hf,hs⟩:=RecoveryFocus.run_config (slots a E) (slots_injective a E) MatrixScoreHeaders.machine
    (fun _ => 0) (input a E r) _ entry base hb
  rw [hin] at ha
  have localT (j : Fin 23) : actual.final.tapes (slots a E j)=base.final.tapes j := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E)]
  have localH (j : Fin 23) : actual.final.heads (slots a E j)=base.final.heads j := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E)]
  refine ⟨actual,ha,?_,(localT 22).trans pT,(localH 22).trans pH,hs.trans_le bs⟩
  intro i
  by_cases hi : i=MatrixPacketRestore.copySlots a E 0
  · subst i
    refine ⟨?_,(localH 0).trans sourceH⟩
    apply (localT 0).trans
    rw [sourceT]
    simp [MatrixPacketColdPrepare.cold,physicalInput]
  · have pk : RecoveryFocus.pick (slots a E) (old a E i)=none := by
      simp only [RecoveryFocus.pick,dif_neg (not_exists.mpr (old_outside a E i hi))]
    rw [hf]
    simp only [RecoveryFocus.config,pk]
    exact ⟨input_old a E r i,True.intro⟩

end NearCubicWires.RepairOrdinary.MatrixPacketHeader
