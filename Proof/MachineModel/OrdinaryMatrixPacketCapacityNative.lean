import Proof.MachineModel.OrdinaryMatrixPacketCapacityEntry

/-! The actual first packet supplies U/d/p to the whole capacity producer.
This is the cold scheduler bootstrap; it retains both streaming cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketCapacityNative
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixWilliamsProduct (source)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (E : ℕ) := MatrixPacketCapacityEntry.tapes E
noncomputable def tapes (a : WilliamsAlgorithm) (E : ℕ) := MatrixVariablePacketWorkspace.tapes a+extra E
noncomputable def slots (a : WilliamsAlgorithm) (E : ℕ) (j : Fin (extra E)) : Fin (tapes a E) :=
  if j.val=0 then ⟨400,by unfold tapes MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes MatrixVariableProduct.tapes; omega⟩
  else if j.val=1 then ⟨12,by unfold tapes MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes MatrixVariableProduct.tapes; omega⟩
  else if j.val=2 then ⟨22,by unfold tapes MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes MatrixVariableProduct.tapes; omega⟩
  else j.natAdd (MatrixVariablePacketWorkspace.tapes a)
theorem slots_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (slots a E) := by
  intro i j he
  have hm : 425≤MatrixVariablePacketWorkspace.tapes a := by
    unfold MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes MatrixVariableProduct.tapes
    omega
  have hv := congrArg Fin.val he
  unfold slots at hv
  repeat' split at hv
  all_goals simp only [Fin.val_natAdd] at hv
  all_goals exact Fin.ext (by omega)

theorem input_at (E U d p : ℕ) (j : Fin (MatrixPacketCapacityEntry.tapes E)) :
    MatrixPacketCapacityEntry.input E U d p j=
      if j.val=0 then UnaryTemplate.tape U else if j.val=1 then UnaryTemplate.tape d
      else if j.val=2 then UnaryTemplate.tape p else [] := by
  refine Fin.addCases (m := 21) (n := MatrixPacketCapacityPower.tapes E) (fun i => ?_) (fun i => ?_) j
  · fin_cases i <;> rfl
  · change (Fin.addCases (m := 21) (n := MatrixPacketCapacityPower.tapes E) (motive := fun _ => List Bool)
      (MatrixPacketCapacityDimensions.input U d p) (fun _ => [])) (i.natAdd 21)=_
    rw [Fin.addCases_right]
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

noncomputable def first (a : WilliamsAlgorithm) (E : ℕ) (negative : Bool) :=
  TapeEmbedding.machine (extra E) (MatrixVariablePacketReset.machine a negative)
noncomputable def last (a : WilliamsAlgorithm) (E C : ℕ) := RecoveryFocus.machine (slots a E)
  (MatrixPacketCapacityEntry.machine E C)
noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) (negative : Bool) := Composition.machine (first a E negative) (last a E C)
noncomputable def input (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (bit : ℕ) (out : List Bool) :=
  Composition.leftConfig (41+(RepairSource.ProjectionNormalization.DimensionPower.states C E+7+7))
    (TapeEmbedding.config (fun _ : Fin (extra E) => 0) (fun _ => []) (MatrixVariablePacketReset.input a r bit out))
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (negative : Bool) (bit : ℕ) :=
  MatrixVariablePacketReset.budget a r bit negative+1+
    MatrixPacketCapacityEntry.budget E C r.U r.d r.p
noncomputable def outputTape (a : WilliamsAlgorithm) (E : ℕ) := slots a E (MatrixPacketCapacityEntry.outputTape E)

theorem native_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (ht : bit<r.p) : ∃ actual,
    runFrom (machine a E C negative) (budget a E C r negative bit) (input a E C r bit out)=some actual ∧
    actual.final.tapes (outputTape a E)=List.replicate (C*(r.U+1)^2*(r.d+r.p+1)^E) true ∧ actual.final.heads (outputTape a E)=0 ∧
    actual.final.tapes (((MatrixVariablePacket.outputTape a).castAdd 1).castAdd (extra E))=out++packet r negative bit ∧
    actual.final.heads (((MatrixVariablePacket.outputTape a).castAdd 1).castAdd (extra E))=(out++packet r negative bit).length ∧
    actual.final.tapes (((MatrixVariablePacket.offset a).castAdd 1).castAdd (extra E))=UnaryTemplate.tape (2*bit) ∧
    actual.final.heads (((MatrixVariablePacket.offset a).castAdd 1).castAdd (extra E))=1 ∧
    actual.steps≤budget a E C r negative bit ∧
    (∀ j : Fin 3,
      actual.final.tapes (slots a E ⟨j.val,by unfold extra MatrixPacketCapacityEntry.tapes; omega⟩)=
        MatrixPacketCapacityEntry.input E r.U r.d r.p ⟨j.val,by unfold MatrixPacketCapacityEntry.tapes; omega⟩ ∧
      actual.final.heads (slots a E ⟨j.val,by unfold extra MatrixPacketCapacityEntry.tapes; omega⟩)=0) ∧
    (∃ base,
      runFrom (MatrixVariablePacketReset.machine a negative) (MatrixVariablePacketReset.budget a r bit negative)
        (MatrixVariablePacketReset.input a r bit out)=some base ∧
      ∀ i : Fin (MatrixVariablePacketWorkspace.tapes a),i.val≠400 ∧ i.val≠12 ∧ i.val≠22 →
        actual.final.tapes (i.castAdd (extra E))=base.final.tapes i ∧
        actual.final.heads (i.castAdd (extra E))=base.final.heads i) := by
  obtain ⟨base,hb,bt,bo,fields,heads,_,_,bs⟩ := MatrixVariablePacketReset.reset_run a r negative bit out ht
  have he := TapeEmbedding.run_embed (MatrixVariablePacketReset.machine a negative)
    (fun _ : Fin (extra E) => 0) (fun _ => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin (extra E) => 0) (fun _ => []) base
  have oldT (i : Fin (MatrixVariablePacketWorkspace.tapes a)) : prepared.final.tapes (i.castAdd (extra E))=base.final.tapes i := by
    change (Fin.addCases (m := MatrixVariablePacketWorkspace.tapes a) (n := extra E) (motive := fun _ => List Bool)
      base.final.tapes (fun _ => [])) (i.castAdd (extra E))=_
    rw [Fin.addCases_left]
  have oldH (i : Fin (MatrixVariablePacketWorkspace.tapes a)) : prepared.final.heads (i.castAdd (extra E))=base.final.heads i := by
    change (Fin.addCases (m := MatrixVariablePacketWorkspace.tapes a) (n := extra E) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd (extra E))=_
    rw [Fin.addCases_left]
  have freshT (i : Fin (extra E)) : prepared.final.tapes (i.natAdd (MatrixVariablePacketWorkspace.tapes a))=[] := by
    change (Fin.addCases (m := MatrixVariablePacketWorkspace.tapes a) (n := extra E) (motive := fun _ => List Bool)
      base.final.tapes (fun _ => [])) (i.natAdd (MatrixVariablePacketWorkspace.tapes a))=_
    rw [Fin.addCases_right]
  have freshH (i : Fin (extra E)) : prepared.final.heads (i.natAdd (MatrixVariablePacketWorkspace.tapes a))=0 := by
    change (Fin.addCases (m := MatrixVariablePacketWorkspace.tapes a) (n := extra E) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.natAdd (MatrixVariablePacketWorkspace.tapes a))=_
    rw [Fin.addCases_right]
  have old_zero (i : Fin 425) (hi : i.val≠424) :
      prepared.final.heads ((((i.castAdd (source a).program.tapeCount).castAdd 17).castAdd 1).castAdd (extra E))=0 := by
    have h := heads ((i.castAdd (source a).program.tapeCount).castAdd 17)
    have ho : (i.castAdd (source a).program.tapeCount).castAdd 17≠MatrixVariablePacket.offset a := by
      intro he; exact hi (congrArg Fin.val he)
    have hx : (i.castAdd (source a).program.tapeCount).castAdd 17≠MatrixVariablePacket.outputTape a := by
      intro he
      have hv := congrArg Fin.val he
      change i.val=MatrixVariableProduct.tapes a+16 at hv
      have hk : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
      omega
    split at h
    · rename_i he
      exact False.elim (ho he)
    · split at h
      · rename_i he
        exact False.elim (hx he)
      · exact (oldH _).trans h
  obtain ⟨value,⟨body,hbody,bodyT,bodyH,bodyS⟩,cap,capU,capd,capp⟩ :=
    MatrixPacketCapacityEntry.capacity_ready E C r.U r.d r.p
  let entry := initialConfiguration (MatrixPacketCapacityEntry.machine E C)
    (MatrixPacketCapacityEntry.input E r.U r.d r.p)
  have hi : RecoveryFocus.config (slots a E) prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final (last a E C).start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      change prepared.final.heads (slots a E j)=0
      by_cases h0 : j.val=0
      · simp only [slots,if_pos h0]
        exact old_zero 400 (by change (400 : ℕ)≠424; decide)
      by_cases h1 : j.val=1
      · simp only [slots,if_neg h0,if_pos h1]
        exact old_zero 12 (by change (12 : ℕ)≠424; decide)
      by_cases h2 : j.val=2
      · simp only [slots,if_neg h0,if_neg h1,if_pos h2]
        exact old_zero 22 (by change (22 : ℕ)≠424; decide)
      · simp only [slots,if_neg h0,if_neg h1,if_neg h2]
        exact freshH j
    · intro j
      change prepared.final.tapes (slots a E j)=MatrixPacketCapacityEntry.input E r.U r.d r.p j
      rw [input_at]
      by_cases h0 : j.val=0
      · simp only [slots,if_pos h0]
        exact (oldT _).trans (fields 2)
      by_cases h1 : j.val=1
      · simp only [slots,if_neg h0,if_pos h1]
        exact (oldT _).trans (fields 0)
      by_cases h2 : j.val=2
      · simp only [slots,if_neg h0,if_neg h1,if_pos h2]
        exact (oldT _).trans (fields 1)
      · simp only [slots,if_neg h0,if_neg h1,if_neg h2]
        exact freshT j
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config (slots a E) (slots_injective a E)
    (MatrixPacketCapacityEntry.machine E C) prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join (first a E negative) (last a E C) _ _ _ prepared focused he hf
  have other (i : Fin (MatrixVariablePacketWorkspace.tapes a)) (hn : i.val≠400 ∧ i.val≠12 ∧ i.val≠22) :
      focused.final.tapes (i.castAdd (extra E))=base.final.tapes i ∧ focused.final.heads (i.castAdd (extra E))=base.final.heads i := by
    have no : ¬∃ j,slots a E j=i.castAdd (extra E) := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      unfold slots at hv
      repeat' split at hv
      all_goals simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      all_goals omega
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick,dif_neg no]
    exact ⟨oldT i,oldH i⟩
  have ho := other ((MatrixVariablePacket.outputTape a).castAdd 1) (by
    have h : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
    simp only [MatrixVariablePacket.outputTape,Fin.val_castAdd,Fin.val_natAdd]
    omega)
  have hx := other ((MatrixVariablePacket.offset a).castAdd 1) (by change (424 : ℕ)≠400 ∧ 424≠12 ∧ 424≠22; decide)
  have boH := heads (MatrixVariablePacket.outputTape a)
  have bxH := heads (MatrixVariablePacket.offset a)
  have hn : MatrixVariablePacket.outputTape a≠MatrixVariablePacket.offset a := by
    intro h
    have hv := congrArg Fin.val h
    change MatrixVariableProduct.tapes a+16=424 at hv
    have hk : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
    omega
  have boH' : base.final.heads ((MatrixVariablePacket.outputTape a).castAdd 1)=(out++packet r negative bit).length := by
    split at boH
    · rename_i he
      exact False.elim (hn he)
    · simp only [if_true] at boH
      convert boH using 1
      rfl
  simp only [if_true] at bxH
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,ho.1.trans bt,ho.2.trans boH',
    hx.1.trans bo,hx.2.trans bxH,?_,?_,⟨base,hb,other⟩⟩
  · change focused.final.tapes (slots a E (MatrixPacketCapacityEntry.outputTape E))=_
    rw [ff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E),bodyT] using cap
  · change focused.final.heads (slots a E (MatrixPacketCapacityEntry.outputTape E))=0
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E),bodyH]
  · change base.steps+1+focused.steps≤_
    rw [fs]
    unfold budget
    omega
  · intro j
    have hv : value ⟨j.val,by omega⟩=
        MatrixPacketCapacityEntry.input E r.U r.d r.p ⟨j.val,by unfold MatrixPacketCapacityEntry.tapes; omega⟩ := by
      fin_cases j
      · exact capU
      · exact capd
      · exact capp
    constructor
    · change focused.final.tapes (slots a E _) = _
      rw [ff]
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E),bodyT]
      convert hv using 1
      rfl
    · change focused.final.heads (slots a E _) = 0
      rw [ff]
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E),bodyH]

end NearCubicWires.RepairOrdinary.MatrixPacketCapacityNative
