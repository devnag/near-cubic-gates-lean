import Proof.PCP.PCPPNativeHierarchySource

/-! Original hierarchy verifier/time specialization. Its fixed-source
input/log exponent is retained explicitly before the remaining native cost. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def originalBudget {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (r : InputRequest)
    (oracle : BooleanCircuit (width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :=
  HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
    (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source+
    4*(PCPPNative.descriptor oracle).length+7+
    PCPPNativeCounterNodes.budget oracle (pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
      (queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)

theorem original_budget_bound {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 (H.time r.1).bits oracle≤
      originalBudget source H Cpad r oracle := by
  have hb:=HierarchyStreamCost.budget_bound source H Cpad hcoeff hpad r
  unfold budget
  rw [PCPPNativeHierarchy.original_budget source H Cpad hpad r]
  unfold originalBudget
  omega

theorem original_run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let c:=circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle
    ∃ result,run (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (originalBudget source H Cpad r oracle)
      (SourceHandoff.sourceTapes (PCPPNativeInputFields.word (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)))=some result ∧
      result.steps≤originalBudget source H Cpad r oracle ∧
      result.final.tapes (slots source k 177)=c.nodes.flatMap PCPPRequestNodeSchema.native ∧
      result.final.heads (slots source k 177)=(c.nodes.flatMap PCPPRequestNodeSchema.native).length ∧
      result.final.heads (slots source k 89)=0 ∧ result.final.tapes (slots source k 89)=List.replicate c.output.val true ∧
      result.final.heads (slots source k 91)=0 ∧ result.final.tapes (slots source k 91)=List.replicate c.size true ∧
      result.final.heads (slots source k 72)=0 ∧ result.final.tapes (slots source k 72)=List.replicate (width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) true := by
  obtain ⟨result,hr,hs,rest⟩:=raw_run source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 (H.time r.1).bits hpad oracle
  have hb:=original_budget_bound source H Cpad hcoeff hpad r oracle
  have more:=run_moreFuel (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    (originalBudget source H Cpad r oracle-budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 (H.time r.1).bits oracle)
    _ result hr
  rw [Nat.add_sub_of_le hb,input_word] at more
  exact ⟨result,more,hs.trans hb,rest⟩

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
