import Proof.PCP.PCPPNativeQueryHeaderFocus

/-! Original native descriptor header through the complete copied-node loop.
The physically parsed size is the driver; no count tape is assumed at entry. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape SourceInterfaces RepairRepresentation PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def originalHead {n : ℕ} (oracle : BooleanCircuit n) := natWord n++natWord oracle.size
def originalBody {n : ℕ} (oracle : BooleanCircuit n) := PCPPNativeNodeLoop.nativeWords oracle.nodes
def copied {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n) (projection : Fin n → ProjectedRandomBit r) :=
  (PCPPNative.copiedNodes base oracle projection oracle.size).flatMap PCPPRequestNodeSchema.native
noncomputable def headerNodes := Composition.machine header nodes
def headerNodesBudget {n : ℕ} (oracle : BooleanCircuit n) (F : ℕ) :=
  PCPPNativeQueryHeader.budget n oracle.size+1+(oracle.size*(6*F+11)+3)

theorem original_parts {n : ℕ} (oracle : BooleanCircuit n) :
    PCPPNative.descriptor oracle=originalHead oracle++originalBody oracle++natWord oracle.output.val := by
  simp only [PCPPNative.descriptor_eq,originalHead,originalBody,PCPPNativeNodeLoop.nativeWords,BooleanCircuit.size,List.append_assoc]
theorem header_source {n : ℕ} (oracle : BooleanCircuit n) :
    PCPPNativeQueryHeader.source [] (originalBody oracle++natWord oracle.output.val) n oracle.size=PCPPNative.descriptor oracle := by
  rw [original_parts]
  simp only [PCPPNativeQueryHeader.source,originalHead,List.nil_append,List.append_assoc]
theorem node_source {n : ℕ} (oracle : BooleanCircuit n) :
    PCPPNativeNodeLoop.source (originalHead oracle) (natWord oracle.output.val) oracle.nodes=PCPPNative.descriptor oracle := by
  rw [original_parts]
  rfl

theorem header_nodes_run {n r : ℕ} (base C F : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes) :
    ∃ result,runFrom headerNodes (headerNodesBudget oracle F)
      ⟨headerNodes.start,heads 0 out,data (PCPPNative.descriptor oracle) (rowCache projection) base base C F out⟩=some result ∧
      result.steps ≤ headerNodesBudget oracle F ∧
      lowFrame (PCPPNative.descriptor oracle) (rowCache projection)
        ((originalHead oracle).length+(originalBody oracle).length) base (base+2*oracle.size) C F
        (out++copied base oracle projection) result.final.heads result.final.tapes ∧
      result.final.tapes 123=UnaryTemplate.tape n ∧ result.final.heads 123=1 ∧
      result.final.tapes 122=UnaryTemplate.tape oracle.size ∧ result.final.heads 122=1 ∧
      (∀ i,reserved i → result.final.heads i=0 ∧ result.final.tapes i=[]) := by
  obtain ⟨a,ha,as,alow,aa,ah,ac,ach,afresh⟩ := header_focus_run []
    (originalBody oracle++natWord oracle.output.val) (rowCache projection) n oracle.size base base C F out
  rw [header_source] at ha alow
  obtain ⟨b,hb,bs,blow,bch,bc,bkeep⟩ := nodes_run (originalHead oracle) (natWord oracle.output.val)
    base C F oracle projection out a.final.heads a.final.tapes
    (by rw [node_source]
        simpa only [originalHead,List.length_append,List.length_nil,Nat.zero_add] using alow)
    ⟨ach,ac⟩ hCF hw
  let result := Composition.joinedReceipt a b
  have hr := Composition.run_join header nodes _ _ _ a b ha hb
  refine ⟨result,hr,?_,?_,?_,?_,bc,bch,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold headerNodesBudget
    omega
  · change lowFrame (PCPPNative.descriptor oracle) (rowCache projection)
      ((originalHead oracle).length+(originalBody oracle).length) base (base+2*oracle.size) C F
      (out++copied base oracle projection) b.final.heads b.final.tapes
    simpa only [node_source,originalBody,copied] using blow
  · exact ((bkeep 123 (by decide)).2).trans aa
  · exact ((bkeep 123 (by decide)).1).trans ah
  · intro i hi
    have hk := bkeep i (reserved_high i hi)
    exact ⟨hk.1.trans (afresh i hi).1,hk.2.trans (afresh i hi).2⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
