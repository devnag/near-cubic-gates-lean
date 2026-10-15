import Proof.MachineModel.OrdinaryMatrixVariablePacketReset
import Proof.PCP.PCPSerializerTapeSupport

/-! Local packet workspace has a bound independent of the accumulated
output length. The physically supplied clear capacity pads only local work. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePacketWorkspace
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixWilliamsProduct (source)
open MatrixVariablePacket (offset outputTape)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) := MatrixVariableCount.tapes a+1
noncomputable def working (a : WilliamsAlgorithm) (i : Fin (tapes a)) : Prop :=
  i.val≠424 ∧ i.val≠MatrixVariableProduct.tapes a+16
noncomputable instance (a : WilliamsAlgorithm) (i : Fin (tapes a)) : Decidable (working a i) :=
  inferInstanceAs (Decidable (i.val≠424 ∧ i.val≠MatrixVariableProduct.tapes a+16))
noncomputable def caps (a : WilliamsAlgorithm) (C : ℕ) (i : Fin (tapes a)) := if working a i then C else 0
noncomputable def footprint (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (negative : Bool) :=
  (physicalInput r).length+2*r.p+MatrixVariablePacketReset.budget a r bit negative+4

theorem entry_bounds (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool)
    (i : Fin (tapes a)) (hi : working a i) :
    (MatrixVariablePacketReset.input a r bit out).heads i=0 ∧
    ((MatrixVariablePacketReset.input a r bit out).tapes i).length≤(physicalInput r).length+2*bit+2 := by
  revert hi
  refine Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (fun j => ?_) (fun j => ?_) i
  · intro hi
    have hh := MatrixVariablePacketReset.input_head a r bit out j (by
      simpa only [MatrixVariablePacketReset.selected,Bool.decide_iff,working,Fin.val_castAdd] using hi)
    constructor
    · change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
        (motive := fun _ => ℕ) (MatrixVariablePacket.input a r bit out).heads (fun _ => 0)) (j.castAdd 1)=0
      rw [Fin.addCases_left]
      exact hh
    · change ((Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
        (motive := fun _ => List Bool) (MatrixVariablePacket.input a r bit out).tapes (fun _ => [])) (j.castAdd 1)).length≤_
      rw [Fin.addCases_left]
      revert hi
      refine Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (fun k => ?_) (fun k => ?_) j
      · intro _
        change ((Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
          (motive := fun _ => List Bool) (MatrixVariableProduct.input a r bit).tapes (MatrixVariableCount.extraTapes out)) (k.castAdd 17)).length≤_
        rw [Fin.addCases_left]
        have hb := (MatrixVariableWorkspace.entry_bounds a r bit).2 (k.castAdd 1)
        change ((Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 1)
          (motive := fun _ => List Bool) (MatrixVariableProduct.input a r bit).tapes (fun _ => [])) (k.castAdd 1)).length≤_ at hb
        rw [Fin.addCases_left] at hb
        exact hb
      · intro hi
        change ((Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
          (motive := fun _ => List Bool) (MatrixVariableProduct.input a r bit).tapes (MatrixVariableCount.extraTapes out)) (k.natAdd (MatrixVariableProduct.tapes a))).length≤_
        rw [Fin.addCases_right]
        have hk : k≠16 := by intro he; subst k; simp [working] at hi
        simp [MatrixVariableCount.extraTapes,hk]
  · intro _
    fin_cases j
    constructor
    · change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
        (motive := fun _ => ℕ) (MatrixVariablePacket.input a r bit out).heads (fun _ => 0)) ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=0
      rw [Fin.addCases_right]
    · change ((Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
        (motive := fun _ => List Bool) (MatrixVariablePacket.input a r bit out).tapes (fun _ => [])) ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))).length≤_
      rw [Fin.addCases_right]
      simp

theorem workspace_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit C : ℕ) (out : List Bool)
    (ht : bit<r.p) (hC : footprint a r bit negative≤C) : ∃ actual,
    runFrom (MatrixVariablePacketReset.machine a negative) (MatrixVariablePacketReset.budget a r bit negative)
      (ZeroPadding.config (caps a C) (MatrixVariablePacketReset.input a r bit out))=some actual ∧
    actual.final.tapes ((outputTape a).castAdd 1)=out++packet r negative bit ∧
    actual.final.tapes ((offset a).castAdd 1)=UnaryTemplate.tape (2*bit) ∧
    (∀ j,actual.final.tapes ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1)=
      ZeroPadding.pad (caps a C ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1))
        (MatrixVariableDimensions.values r negative bit j)) ∧
    (∀ i : Fin (MatrixVariableCount.tapes a),actual.final.heads (i.castAdd 1)=
      if i=offset a then 1 else if i=outputTape a then (out++packet r negative bit).length else 0) ∧
    actual.final.heads ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=0 ∧
    (∀ i,working a i → (actual.final.tapes i).length=C) ∧
    actual.steps≤MatrixVariablePacketReset.budget a r bit negative := by
  obtain ⟨base,hb,bt,bo,fields,heads,logH,_,bs⟩ := MatrixVariablePacketReset.reset_run a r negative bit out ht
  have support (i : Fin (tapes a)) (hi : working a i) : (base.final.tapes i).length≤C := by
    obtain ⟨hh,hl⟩ := entry_bounds a r bit out i hi
    have supp := PCPSerializerReuse.tape_support (MatrixVariablePacketReset.machine a negative) _ _ base hb i
      ((physicalInput r).length+2*bit+2) 0 hh.le (hl.trans (Nat.le_max_left _ _))
    have hmax : max ((physicalInput r).length+2*bit+2) (0+base.steps+1)≤footprint a r bit negative := by
      unfold footprint
      omega
    exact supp.trans (hmax.trans hC)
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config (MatrixVariablePacketReset.machine a negative)
    (caps a C) _ _ base hb
  refine ⟨actual,ha,?_,?_,?_,?_,?_,?_,hs.trans_le bs⟩
  · simp only [hf,ZeroPadding.config,bt]
    simp [caps,working,outputTape]
  · simp only [hf,ZeroPadding.config,bo]
    simp [caps,working,offset]
  · intro j
    simp only [hf,ZeroPadding.config,fields j]
  · intro i
    exact (congrArg (fun c => c.heads (i.castAdd 1)) hf).trans (heads i)
  · exact (congrArg (fun c => c.heads ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))) hf).trans logH
  · intro i hi
    simp only [hf,ZeroPadding.config,ZeroPadding.pad_length,caps,hi,if_true]
    exact max_eq_left (support i hi)

end NearCubicWires.RepairOrdinary.MatrixVariablePacketWorkspace
