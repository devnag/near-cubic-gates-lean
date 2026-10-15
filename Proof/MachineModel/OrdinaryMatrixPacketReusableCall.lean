import Proof.MachineModel.OrdinaryMatrixPacketPreparedEntry

/-! Execute the existing bounded packet from its physically restored entry,
retaining every external cursor and driver. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketReusableCall
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
open MatrixWilliamsProduct (source)
open MatrixPacketRestoreDock (slots slots_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) (negative : Bool) :=
  RecoveryFocus.machine (slots a E) (MatrixVariablePacketReset.machine a negative)

theorem call_run {s : ℕ} (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (c : Configuration (MatrixPacketRestore.tapes a E) s)
    (ht : bit<r.p) (hcap : MatrixVariablePacketWorkspace.footprint a r bit negative≤cap)
    (ch : ∀ i,c.heads (slots a E i)=(MatrixVariablePacketReset.input a r bit out).heads i)
    (ct : ∀ i,c.tapes (slots a E i)=
      (ZeroPadding.config (MatrixVariablePacketWorkspace.caps a cap) (MatrixVariablePacketReset.input a r bit out)).tapes i) : ∃ actual,
    runFrom (machine a E negative) (MatrixVariablePacketReset.budget a r bit negative)
      (Composition.restart c (machine a E negative).start)=some actual ∧
    actual.final.tapes (slots a E ((MatrixVariablePacket.outputTape a).castAdd 1))=out++packet r negative bit ∧
    actual.final.heads (slots a E ((MatrixVariablePacket.outputTape a).castAdd 1))=(out++packet r negative bit).length ∧
    actual.final.tapes (slots a E ((MatrixVariablePacket.offset a).castAdd 1))=UnaryTemplate.tape (2*bit) ∧
    actual.final.heads (slots a E ((MatrixVariablePacket.offset a).castAdd 1))=1 ∧
    (∀ i,MatrixVariablePacketWorkspace.working a i →
      (actual.final.tapes (slots a E i)).length=cap ∧ actual.final.heads (slots a E i)=0) ∧
    (∀ j,actual.final.tapes (slots a E ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1))=
      ZeroPadding.pad (MatrixVariablePacketWorkspace.caps a cap ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1))
        (MatrixVariableDimensions.values r negative bit j)) ∧
    (∀ i,(∀ j,slots a E j≠i) →
      actual.final.tapes i=c.tapes i ∧
      actual.final.heads i=c.heads i) ∧
    actual.steps≤MatrixVariablePacketReset.budget a r bit negative := by
  obtain ⟨body,hbody,outT,offT,fields,bodyHeads,logH,support,bs⟩ :=
    MatrixVariablePacketWorkspace.workspace_run a r negative bit cap out ht hcap
  let entry := ZeroPadding.config (MatrixVariablePacketWorkspace.caps a cap) (MatrixVariablePacketReset.input a r bit out)
  have hi : RecoveryFocus.config (slots a E) c.heads c.tapes entry=
      Composition.restart c (machine a E negative).start := WilliamsSourceCrop.focus_same (slots a E) c entry ch ct
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config (slots a E) (slots_injective a E)
    (MatrixVariablePacketReset.machine a negative) c.heads c.tapes _ entry body hbody
  rw [hi] at hf
  have localT (i : Fin (MatrixVariablePacketWorkspace.tapes a)) : focused.final.tapes (slots a E i)=body.final.tapes i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E)]
  have localH (i : Fin (MatrixVariablePacketWorkspace.tapes a)) : focused.final.heads (slots a E i)=body.final.heads i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E)]
  have hn : MatrixVariablePacket.outputTape a≠MatrixVariablePacket.offset a := by
    intro he
    have hv:=congrArg Fin.val he
    change MatrixVariableProduct.tapes a+16=424 at hv
    have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
    omega
  have outH := bodyHeads (MatrixVariablePacket.outputTape a)
  have offH := bodyHeads (MatrixVariablePacket.offset a)
  have outH' : body.final.heads ((MatrixVariablePacket.outputTape a).castAdd 1)=(out++packet r negative bit).length := by
    split at outH
    · rename_i he
      exact False.elim (hn he)
    · simp only [if_true] at outH
      convert outH using 1
      rfl
  simp only [if_true] at offH
  refine ⟨focused,hf,(localT _).trans outT,(localH _).trans outH',
    (localT _).trans offT,(localH _).trans offH,?_,(fun j => (localT _).trans (fields j)),?_,?_⟩
  · intro i hw
    refine ⟨(congrArg List.length (localT i)).trans (support i hw),?_⟩
    apply (localH i).trans
    revert hw
    refine Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (fun j => ?_) (fun j => ?_) i
    · intro hw
      have h:=bodyHeads j
      split at h
      · rename_i he
        exact False.elim (hw.1 (congrArg Fin.val he))
      · split at h
        · rename_i he
          exact False.elim (hw.2 (congrArg Fin.val he))
        · exact h
    · intro _; fin_cases j; exact logH
  · intro i no
    have pk : RecoveryFocus.pick (slots a E) i=none := by
      simp only [RecoveryFocus.pick,dif_neg (not_exists.mpr no)]
    change focused.final.tapes i=_ ∧ focused.final.heads i=_
    rw [ff]
    simp only [RecoveryFocus.config,pk]
    trivial
  · exact fs.trans_le bs

end NearCubicWires.RepairOrdinary.MatrixPacketReusableCall
