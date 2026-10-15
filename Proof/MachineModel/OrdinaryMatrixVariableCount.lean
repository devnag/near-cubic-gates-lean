import Proof.MachineModel.OrdinaryMatrixPacketDimensions

/-! The original-request signed Williams call now physically supplies the
exact native count-block driver. The external append cursor is preserved
through all preparation, ready for the full packet writer. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableCount
open LocalBitMultitape MatrixScoreBatch RepairRepresentation MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) := MatrixVariableProduct.tapes a+17
noncomputable def slots (a : WilliamsAlgorithm) (i : Fin 18) : Fin (tapes a) :=
  if i.val=0 then ⟨400,by unfold tapes MatrixVariableProduct.tapes; omega⟩
  else if i.val=1 then ⟨12,by unfold tapes MatrixVariableProduct.tapes; omega⟩
  else (⟨i.val-2,by omega⟩ : Fin 17).natAdd (MatrixVariableProduct.tapes a)
theorem slots_injective (a : WilliamsAlgorithm) : Function.Injective (slots a) := by
  intro i j he
  have hv := congrArg Fin.val he
  unfold slots at hv
  repeat' split at hv
  all_goals simp only [Fin.val_natAdd] at hv
  all_goals have hk : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  all_goals exact Fin.ext (by omega)

noncomputable def first (a : WilliamsAlgorithm) (negative : Bool) := TapeEmbedding.machine 17 (MatrixVariableProduct.machine a negative)
noncomputable def last (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a) MatrixPacketDimensions.machine
noncomputable def machine (a : WilliamsAlgorithm) (negative : Bool) := Composition.machine (first a negative) (last a)
def extraHeads (out : List Bool) (i : Fin 17) := if i=16 then out.length else 0
def extraTapes (out : List Bool) (i : Fin 17) := if i=16 then out else []
noncomputable def input (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool) :=
  Composition.leftConfig 42 (TapeEmbedding.config (extraHeads out) (extraTapes out) (MatrixVariableProduct.input a r bit))
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := MatrixVariableProduct.budget a r+1+MatrixPacketDimensions.budget r.U r.d

theorem call_run {s : ℕ} (a : WilliamsAlgorithm) (U d : ℕ) (c : Configuration (tapes a) s)
    (ct : ∀ j,c.tapes (slots a j)=MatrixPacketDimensions.input U d j)
    (ch : ∀ j,c.heads (slots a j)=0) : ∃ actual,
    runFrom (last a) (MatrixPacketDimensions.budget U d) (Composition.restart c (last a).start)=some actual ∧
    actual.final.tapes (slots a 16)=UnaryTemplate.tape (U^2*(d+1)) ∧ actual.final.heads (slots a 16)=0 ∧
    (∀ i : Fin (MatrixVariableProduct.tapes a),actual.final.tapes (i.castAdd 17)=c.tapes (i.castAdd 17) ∧
      actual.final.heads (i.castAdd 17)=c.heads (i.castAdd 17)) ∧
    actual.final.tapes ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a))=c.tapes ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a)) ∧
    actual.final.heads ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a))=c.heads ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a)) ∧
    actual.steps≤MatrixPacketDimensions.budget U d := by
  obtain ⟨body,hb,bt,bh,bs⟩ := MatrixPacketDimensions.dimensions_ready U d
  let entry := initialConfiguration MatrixPacketDimensions.machine (MatrixPacketDimensions.input U d)
  have hi : RecoveryFocus.config (slots a) c.heads c.tapes entry=Composition.restart c (last a).start :=
    WilliamsSourceCrop.focus_same (slots a) c entry ch ct
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a) MatrixPacketDimensions.machine
    c.heads c.tapes _ entry body hb
  rw [hi] at ha
  obtain ⟨hU,hd,hn⟩ := MatrixPacketDimensions.output_fields U d
  have localT (j : Fin 18) : actual.final.tapes (slots a j)=MatrixPacketDimensions.output U d j := by
    rw [hf]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a),bt]
  have localH (j : Fin 18) : actual.final.heads (slots a j)=0 := by
    rw [hf]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a),bh]
  have other (i : Fin (tapes a)) (hi : ∀ j,slots a j≠i) :
      actual.final.tapes i=c.tapes i ∧ actual.final.heads i=c.heads i := by
    rw [hf]; simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  have old (i : Fin (MatrixVariableProduct.tapes a)) :
      actual.final.tapes (i.castAdd 17)=c.tapes (i.castAdd 17) ∧ actual.final.heads (i.castAdd 17)=c.heads (i.castAdd 17) := by
    by_cases h0 : i.val=400
    · have he : i.castAdd 17=slots a 0 := Fin.ext h0
      rw [he]
      exact ⟨(localT 0).trans (hU.trans (ct 0).symm),(localH 0).trans (ch 0).symm⟩
    by_cases h1 : i.val=12
    · have he : i.castAdd 17=slots a 1 := Fin.ext h1
      rw [he]
      exact ⟨(localT 1).trans (hd.trans (ct 1).symm),(localH 1).trans (ch 1).symm⟩
    apply other
    intro j he
    have hv := congrArg Fin.val he
    unfold slots at hv
    repeat' split at hv
    all_goals simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    all_goals omega
  have hout := other ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a)) (by
    intro j he
    have hv := congrArg Fin.val he
    unfold slots at hv
    repeat' split at hv
    all_goals simp only [Fin.val_natAdd] at hv
    all_goals have hk : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
    all_goals omega)
  exact ⟨actual,ha,(localT 16).trans hn,localH 16,old,hout.1,hout.2,hs.trans_le bs⟩

end NearCubicWires.RepairOrdinary.MatrixVariableCount
