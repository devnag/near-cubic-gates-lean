import Proof.PCP.PCPPNativeQueryFooterNodes

/-! One whole query is emitted from the original native oracle descriptor.
Header, original nodes, footer, index conversion and final shared negation
are all executed; the result is the exact existing copyQuery node stream. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emitted {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n) (projection : Fin n → ProjectedRandomBit r) :=
  (PCPPNative.queryNodes base oracle projection).flatMap PCPPRequestNodeSchema.native
def budget {n : ℕ} (base C F : ℕ) (oracle : BooleanCircuit n) :=
  parsedNodesBudget oracle F+1+PCPPNativeQueryTail.budget base oracle.output.val C
theorem emitted_eq {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n) (projection : Fin n → ProjectedRandomBit r) :
    copied base oracle projection++PCPPNativeQueryTail.emitted base oracle.output.val=emitted base oracle projection := by
  rw [PCPPNativeQueryTail.emitted_nodes r]
  simp only [emitted,PCPPNative.queryNodes,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,copied]

theorem body_run {n r : ℕ} (base C F : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes)
    (hC : PCPPNativeAddressAppend.budget base oracle.output.val+1 ≤ C) :
    ∃ result,runFrom body (budget base C F oracle)
      (entry (PCPPNative.descriptor oracle) (rowCache projection) 0 base base C F out)=some result ∧
      result.steps ≤ budget base C F oracle ∧
      lowFrame (PCPPNative.descriptor oracle) (rowCache projection) (PCPPNative.descriptor oracle).length
        base (base+2*oracle.size) C F (out++emitted base oracle projection) result.final.heads result.final.tapes ∧
      result.final.tapes 164=List.replicate oracle.output.val true ∧ result.final.heads 164=0 ∧
      result.final.tapes 123=UnaryTemplate.tape n ∧ result.final.heads 123=1 ∧
      result.final.tapes 122=UnaryTemplate.tape oracle.size ∧ result.final.heads 122=1 := by
  obtain ⟨a,ha,as,alow,ai,aih,aa,aah,ac,ach⟩ := parsed_nodes_run base C F oracle projection out hCF hw
  obtain ⟨b,hb,bs,bh,bt⟩ := tail_run (PCPPNative.descriptor oracle) (rowCache projection)
    (PCPPNative.descriptor oracle).length base (base+2*oracle.size) C F oracle.output.val
    (out++copied base oracle projection) a.final.heads a.final.tapes alow ⟨aih,ai⟩ hC hCF
  let result := Composition.joinedReceipt a b
  have hr := Composition.run_join parsedNodes tail _ _ _ a b ha hb
  have hbytes : (out++copied base oracle projection)++PCPPNativeQueryTail.emitted base oracle.output.val=
      out++emitted base oracle projection := by rw [List.append_assoc,emitted_eq]
  rw [hbytes] at bh bt
  have keep (i : Fin 168) (hi : i≠5) : b.final.heads i=a.final.heads i ∧ b.final.tapes i=a.final.tapes i := by
    exact ⟨by simpa only [hi,ite_false] using bh i,by simpa only [hi,ite_false] using bt i⟩
  refine ⟨result,hr,?_,?_,((keep 164 (by decide)).2).trans ai,((keep 164 (by decide)).1).trans aih,
    ((keep 123 (by decide)).2).trans aa,((keep 123 (by decide)).1).trans aah,
    ((keep 122 (by decide)).2).trans ac,((keep 122 (by decide)).1).trans ach⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · change lowFrame (PCPPNative.descriptor oracle) (rowCache projection) (PCPPNative.descriptor oracle).length
      base (base+2*oracle.size) C F (out++emitted base oracle projection) b.final.heads b.final.tapes
    intro i
    by_cases hi : i=5
    · subst i
      change b.final.heads 5=(out++emitted base oracle projection).length ∧
        b.final.tapes 5=out++emitted base oracle projection
      exact ⟨by simpa only [ite_true] using bh 5,by simpa only [ite_true] using bt 5⟩
    · have hglobal : i.castAdd 46≠(5 : Fin 168) := by
        intro h; apply hi; apply Fin.ext; exact congrArg (fun j : Fin 168 => j.val) h
      have hk := keep (i.castAdd 46) hglobal
      have hlow := alow i
      constructor
      · simpa only [PCPPNativeNodeReusable.heads,hi,ite_false] using hk.1.trans hlow.1
      · simpa only [PCPPNativeNodeReusable.data,hi,ite_false] using hk.2.trans hlow.2

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
