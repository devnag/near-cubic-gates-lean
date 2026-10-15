import Proof.MachineModel.OrdinaryMatrixPacketCapacityPower

/-! The full physical polynomial capacity producer starts from only the
retained U/d/p sentinels. It builds both successors, the fixed power, and
both assignment-side factors, retaining the original dimensions. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketCapacityEntry
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (E : ℕ) := 21+MatrixPacketCapacityPower.tapes E
def slots (E : ℕ) (i : Fin (MatrixPacketCapacityPower.tapes E)) : Fin (tapes E) :=
  if i.val=0 then ⟨17,by unfold tapes; omega⟩
  else if i.val=DimensionPower.tapes E then ⟨19,by unfold tapes; omega⟩
  else i.natAdd 21
theorem slots_injective (E : ℕ) : Function.Injective (slots E) := by
  intro i j he
  have hv := congrArg Fin.val he
  unfold slots at hv
  repeat' split at hv
  all_goals simp only [Fin.val_natAdd] at hv
  all_goals exact Fin.ext (by omega)

theorem local_input (E q u : ℕ) (i : Fin (MatrixPacketCapacityPower.tapes E)) :
    MatrixPacketCapacityPower.input E q u i=
      if i.val=0 then UnaryTemplate.tape q else if i.val=DimensionPower.tapes E then UnaryTemplate.tape u else [] := by
  refine Fin.addCases (m := DimensionPower.tapes E) (n := 5) (fun j => ?_) (fun j => ?_) i
  · change (Fin.addCases (m := DimensionPower.tapes E) (n := 5) (motive := fun _ => List Bool)
      (DimensionPower.input E q) (MatrixPacketCapacityPower.extras u)) (j.castAdd 5)=_
    rw [Fin.addCases_left]
    have hj : j.val≠DimensionPower.tapes E := Nat.ne_of_lt j.isLt
    simp [DimensionPower.input,hj]
  · change (Fin.addCases (m := DimensionPower.tapes E) (n := 5) (motive := fun _ => List Bool)
      (DimensionPower.input E q) (MatrixPacketCapacityPower.extras u)) (j.natAdd (DimensionPower.tapes E))=_
    rw [Fin.addCases_right]
    have hp : 0<DimensionPower.tapes E := by unfold DimensionPower.tapes; omega
    simp [MatrixPacketCapacityPower.extras,show DimensionPower.tapes E≠0 by omega]

noncomputable def first (E : ℕ) := TapeEmbedding.machine (MatrixPacketCapacityPower.tapes E) MatrixPacketCapacityDimensions.machine
noncomputable def last (E C : ℕ) := RecoveryFocus.machine (slots E) (MatrixPacketCapacityPower.machine E C)
noncomputable def machine (E C : ℕ) := Composition.machine (first E) (last E C)
def input (E U d p : ℕ) : Fin (tapes E) → List Bool :=
  Fin.addCases (MatrixPacketCapacityDimensions.input U d p) (fun _ => [])
noncomputable def outputTape (E : ℕ) := slots E ((3 : Fin 5).natAdd (DimensionPower.tapes E))
def budget (E C U d p : ℕ) := MatrixPacketCapacityDimensions.budget U d p+1+
  MatrixPacketCapacityPower.budget E C (d+p+1) (U+1)

theorem capacity_ready (E C U d p : ℕ) : ∃ out,ClockJoin.ReadyRun (machine E C) (budget E C U d p)
    (input E U d p) out ∧ out (outputTape E)=List.replicate (C*(U+1)^2*(d+p+1)^E) true ∧
    out ⟨0,by omega⟩=UnaryTemplate.tape U ∧
    out ⟨1,by omega⟩=UnaryTemplate.tape d ∧
    out ⟨2,by omega⟩=UnaryTemplate.tape p := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixPacketCapacityDimensions.dimensions_ready U d p
  let data := Fin.addCases (motive := fun _ => List Bool) (MatrixPacketCapacityDimensions.data6 U d p)
    (fun _ : Fin (MatrixPacketCapacityPower.tapes E) => [])
  have he := TapeEmbedding.run_embed MatrixPacketCapacityDimensions.machine (fun _ : Fin (MatrixPacketCapacityPower.tapes E) => 0)
    (fun _ => []) _ _ base hb
  let embedded := TapeEmbedding.receipt (fun _ : Fin (MatrixPacketCapacityPower.tapes E) => 0) (fun _ => []) base
  have hin : TapeEmbedding.config (fun _ : Fin (MatrixPacketCapacityPower.tapes E) => 0) (fun _ => [])
      (initialConfiguration MatrixPacketCapacityDimensions.machine (MatrixPacketCapacityDimensions.input U d p))=
      initialConfiguration (first E) (input E U d p) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 21) (n := MatrixPacketCapacityPower.tapes E) (fun j => ?_) (fun j => ?_) i
      all_goals simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at he
  have h0 : ClockJoin.ReadyRun (first E) (MatrixPacketCapacityDimensions.budget U d p) (input E U d p) data := by
    refine ⟨embedded,he,?_,?_,bs⟩
    · change Fin.addCases base.final.tapes (fun _ => [])=data
      rw [bt]
    · intro i
      refine Fin.addCases (m := 21) (n := MatrixPacketCapacityPower.tapes E) (fun j => ?_) (fun j => ?_) i
      · change (Fin.addCases (m := 21) (n := MatrixPacketCapacityPower.tapes E) (motive := fun _ => ℕ)
          base.final.heads (fun _ => 0)) (j.castAdd (MatrixPacketCapacityPower.tapes E))=0
        rw [Fin.addCases_left,bh]
      · change (Fin.addCases (m := 21) (n := MatrixPacketCapacityPower.tapes E) (motive := fun _ => ℕ)
          base.final.heads (fun _ => 0)) (j.natAdd 21)=0
        rw [Fin.addCases_right]
  have old (j : Fin 21) : data (j.castAdd (MatrixPacketCapacityPower.tapes E))=MatrixPacketCapacityDimensions.data6 U d p j := Fin.addCases_left j
  have fresh (j : Fin (MatrixPacketCapacityPower.tapes E)) : data (j.natAdd 21)=[] := Fin.addCases_right j
  obtain ⟨hU,hd,hp,hq,hu⟩ := MatrixPacketCapacityDimensions.output_fields U d p
  obtain ⟨value,hv,cap,_⟩ := MatrixPacketCapacityPower.power_ready E C (d+p+1) (U+1)
  have h1 := hv.focus (slots E) (slots_injective E) data (by
    intro j
    rw [local_input]
    by_cases h0 : j.val=0
    · simp only [slots,if_pos h0]
      exact (old 17).trans hq
    by_cases hP : j.val=DimensionPower.tapes E
    · simp only [slots,if_neg h0,if_pos hP]
      exact (old 19).trans hu
    · simp only [slots,if_neg h0,if_neg hP]
      exact fresh j)
  have keep (j : Fin 3) : RecoveryFocus.pick (slots E) (⟨j.val,by unfold tapes; omega⟩ : Fin (tapes E))=none := by
    have hn : ¬∃ k,slots E k=(⟨j.val,by unfold tapes; omega⟩ : Fin (tapes E)) := by
      rintro ⟨k,hk⟩
      have hv := congrArg Fin.val hk
      unfold slots at hv
      repeat' split at hv
      all_goals simp only [Fin.val_natAdd] at hv
      all_goals omega
    simp only [RecoveryFocus.pick,dif_neg hn]
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ h0 h1,?_,?_,?_,?_⟩
  · change (install (slots E) data value) (slots E _)=_
    rw [install,RecoveryFocus.pick_slot (slots E) (slots_injective E)]
    change value ((3 : Fin 5).natAdd (DimensionPower.tapes E))=_
    rw [cap]
    congr 1
    ring
  · change (install (slots E) data value) ((0 : Fin 21).castAdd (MatrixPacketCapacityPower.tapes E))=_
    have kp : RecoveryFocus.pick (slots E) ((0 : Fin 21).castAdd (MatrixPacketCapacityPower.tapes E))=none := keep 0
    rw [install,kp]
    exact (old 0).trans hU
  · change (install (slots E) data value) ((1 : Fin 21).castAdd (MatrixPacketCapacityPower.tapes E))=_
    have kp : RecoveryFocus.pick (slots E) ((1 : Fin 21).castAdd (MatrixPacketCapacityPower.tapes E))=none := keep 1
    rw [install,kp]
    exact (old 1).trans hd
  · change (install (slots E) data value) ((2 : Fin 21).castAdd (MatrixPacketCapacityPower.tapes E))=_
    have kp : RecoveryFocus.pick (slots E) ((2 : Fin 21).castAdd (MatrixPacketCapacityPower.tapes E))=none := keep 2
    rw [install,kp]
    exact (old 2).trans hp

end NearCubicWires.RepairOrdinary.MatrixPacketCapacityEntry
