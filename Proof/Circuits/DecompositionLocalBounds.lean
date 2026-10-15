import Proof.Circuits.DecompositionSourceEnvelope
import Proof.Circuits.DecompositionProgram

/-! The literal local decomposition contract, from the same imported
constructor's actual output and the complete ordinary native serializer.
No extra source field or alternate balanced encoding is used. -/
namespace NearCubicWires.RepairOrdinary.DecompositionLocal
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
open DecompositionSchema DecompositionResource DecompositionCodeBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def serializer (D C : ℕ) (a : DecompositionAlgorithm) (hC : 1 ≤ C)
    (hatom : ∀ r z,z∈(groups (a.output r).children).flatten →
      DecompositionAtom.budget z+1 ≤ C*(measured (a.output r).children+1)^D)
    (hchild : ∀ r xs,xs∈groups (a.output r).children → PCPTraversal.budget
      (PCPSerializerMass.mass (DecompositionNesting.atomFields xs))+1 ≤ C*(measured (a.output r).children+1)^D)
    (houter : ∀ r,PCPTraversal.budget (PCPSerializerMass.mass
      (childFields (groups (a.output r).children))) ≤ C*(measured (a.output r).children+1)^D) :
    RepairSource.OrdinaryWordFunction ExactDecompositionRequest
      (fun r => natWord r.arity++exactListWord (a.output r).children)
      (fun r => (output (a.output r).children).bits)
      (fun r => sourceCoefficient D C a*(parameter r)^sourceDegree D a) where
  program := DecompositionGlobal.program D C
  realizes := by
    intro r
    obtain ⟨receipt,hr,ho,_⟩ := schema_run D C (a.output r).children (hatom r) (hchild r)
    have hb := runtime_bound D C a r hC (houter r)
    have hm := run_moreFuel (DecompositionGlobal.machine D C)
      (DecompositionSchema.budget D C (a.output r).children)
      (sourceCoefficient D C a*(parameter r)^sourceDegree D a-
        DecompositionSchema.budget D C (a.output r).children) _ receipt hr
    rw [Nat.add_sub_of_le hb] at hm
    refine ⟨receipt,?_,ho⟩
    rw [DecompositionGlobal.input_eq]
    exact hm

noncomputable def localBounds (a : DecompositionAlgorithm) : DecompositionLocalBounds a where
  coefficient := sourceCoefficient globalDegree globalCoefficient a
  degree := sourceDegree globalDegree a
  coefficientPositive := sourceCoefficient_positive _ _ a
  children := DecompositionResource.children_bound _ _ a
  balancedOutput := fun r => output (a.output r).children
  balancedDecode := fun r => output_decode (a.output r).children
  balancedBits := fun r => bits_bound _ _ a r (by decide)
  balancedSerializer := serializer globalDegree globalCoefficient a (by decide)
    (fun r => atom_capacity (a.output r).children)
    (fun r => child_capacity (a.output r).children)
    (fun r => Nat.le_of_succ_le (outer_capacity (a.output r).children))

theorem localBounds_degree (a : DecompositionAlgorithm) :
    (localBounds a).degree=(a.degree+1)*146 := rfl

end NearCubicWires.RepairOrdinary.DecompositionLocal
