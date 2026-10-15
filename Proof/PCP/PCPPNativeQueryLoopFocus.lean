import Proof.PCP.PCPPNativeQueryLayout

/-! The actual original-node loop in its enclosing query bank. Its real
header-produced size template is consumed and retained; all upper parser
work and retained arity are framed around the same execution. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem nodes_run {n r : ℕ} (pre suffix : List Bool) (base C F : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame (PCPPNativeNodeLoop.source pre suffix oracle.nodes) (rowCache projection)
      pre.length base base C F out ah atapes)
    (hdriver : ah 122=1 ∧ atapes 122=UnaryTemplate.tape oracle.size)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes) :
    ∃ result,runFrom nodes (oracle.size*(6*F+11)+3) ⟨nodes.start,ah,atapes⟩=some result ∧
      result.steps ≤ oracle.size*(6*F+11)+3 ∧
      lowFrame (PCPPNativeNodeLoop.source pre suffix oracle.nodes) (rowCache projection)
        (pre.length+(PCPPNativeNodeLoop.nativeWords oracle.nodes).length) base (base+2*oracle.size) C F
        (out++(PCPPNative.copiedNodes base oracle projection oracle.size).flatMap PCPPRequestNodeSchema.native)
        result.final.heads result.final.tapes ∧
      result.final.heads 122=1 ∧ result.final.tapes 122=UnaryTemplate.tape oracle.size ∧
      (∀ i : Fin 168,123 ≤ i.val → result.final.heads i=ah i ∧ result.final.tapes i=atapes i) := by
  obtain ⟨raw,hr,rs,rf⟩ := PCPPNativeNodeLoop.oracle_run pre suffix base C F oracle projection out hCF hw
  obtain ⟨result,run,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock loopSlots loop_injective
    PCPPNativeNodeLoop.machine _ ah atapes _
    (fun j => (loop_input 0 _ _ _ _ _ _ _ _ _ _ ah atapes hlow hdriver j).1)
    (fun j => (loop_input 0 _ _ _ _ _ _ _ _ _ _ ah atapes hlow hdriver j).2) raw hr
  refine ⟨result,run,by omega,?_,?_,?_,?_⟩
  · intro j
    have hheads := hh (j.castAdd 1)
    have htapes := ht (j.castAdd 1)
    rw [rf] at hheads htapes
    have finalLow := loop_lower 3 (PCPPNativeNodeLoop.source pre suffix oracle.nodes) (rowCache projection)
      (pre.length+(PCPPNativeNodeLoop.nativeWords oracle.nodes).length) base (base+2*oracle.size) C F
      (out++(PCPPNative.copiedNodes base oracle projection oracle.size).flatMap PCPPRequestNodeSchema.native) oracle.size 1 j
    exact ⟨hheads.trans finalLow.1,htapes.trans finalLow.2⟩
  · have h := hh 122
    rw [rf] at h
    exact h.trans (PCPPNativeNodeLoop.template_count 3 _ _ _ _ _ _ _ _ _ _).2
  · have h := ht 122
    rw [rf] at h
    exact h.trans (PCPPNativeNodeLoop.template_count 3 _ _ _ _ _ _ _ _ _ _).1
  · intro i hi
    exact keep i (by intro j; apply Fin.ne_of_val_ne; change j.val≠i.val; omega)

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
