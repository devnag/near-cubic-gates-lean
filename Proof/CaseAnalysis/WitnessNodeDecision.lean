import Proof.CaseAnalysis.WitnessNodeSmall

/-! The final finite node decision is exactly the existing canonical
Boolean-node decoder and its strict earlier-node topology condition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeDecision
open LocalBitMultitape RadixSemantics CompetitorWitnessTriple
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def branch (small : Fin 3 → Fin 5 → Bool) (bounds : Fin 3 → Fin 2 → Bool)
    (shape : Fin 5 → Bool) : Bool:=
  (small 0 0 && shape 3 && (small 1 0 || small 1 1) && small 2 0) ||
  (small 0 1 && shape 3 && !(bounds 1 0) && small 2 0) ||
  (small 0 2 && shape 3 && !(bounds 1 1) && small 2 0) ||
  ((small 0 3 || small 0 4) && shape 2 && shape 4 && !(bounds 1 1) && !(bounds 2 1))
def accept (natural : Fin 3 → Bool) (small : Fin 3 → Fin 5 → Bool)
    (bounds : Fin 3 → Fin 2 → Bool) (shape : Fin 5 → Bool) : Bool:=
  (natural 0 && natural 1 && natural 2) && shape 0 && shape 1 && branch small bounds shape

def shapes (bits : List Bool) : Fin 5 → Bool:=
  ![decide (field bits 0=1),decide (field bits 2=1),decide (field bits 4=1),
    decide (node bits 4=0),decide (node bits 6=0)]
def smalls (bits : List Bool) (i : Fin 3) (j : Fin 5):=decide (NodeMeaning.number bits i=j.val)
def ranges (n index : ℕ) (bits : List Bool) (i : Fin 3) : Fin 2 → Bool:=
  ![decide (n ≤ NodeMeaning.number bits i),decide (index ≤ NodeMeaning.number bits i)]

theorem branch_exact (n index : ℕ) (bits : List Bool) :
    ((shapes bits 0 && shapes bits 1) && branch (smalls bits) (ranges n index bits) (shapes bits))=true ↔
      NodeMeaning.shape bits ∧ NodeMeaning.test n index
        (NodeMeaning.number bits 0) (NodeMeaning.number bits 1) (NodeMeaning.number bits 2):=by
  generalize ht:NodeMeaning.number bits 0=tag
  rcases tag with _|_|_|_|_|tag
  all_goals
    simp [branch,smalls,ranges,shapes,NodeMeaning.shape,NodeMeaning.test,ht,
      structural,PCPPNativeCanonical.headerValid]
  all_goals omega

theorem accept_exact (n index : ℕ) (bits : List Bool) (natural : Fin 3 → Bool)
    (small : Fin 3 → Fin 5 → Bool) (bounds : Fin 3 → Fin 2 → Bool)
    (hnat : ∀ i,natural i=true ↔ BitFields.passes (NodeMeaning.codeWord bits i))
    (hsmall : NodeMeaning.naturals bits → small=smalls bits)
    (hbound : bounds=ranges n index bits) :
    accept natural small bounds (shapes bits)=true ↔ NodeMeaning.valid n index bits:=by
  have hall:(natural 0 && natural 1 && natural 2)=true ↔ NodeMeaning.naturals bits:=by
    simp only [Bool.and_eq_true,hnat,NodeMeaning.naturals]
    constructor
    · rintro ⟨⟨h0,h1⟩,h2⟩ i
      fin_cases i <;> assumption
    · intro h
      exact ⟨⟨h 0,h 1⟩,h 2⟩
  by_cases hn:NodeMeaning.naturals bits
  · have ha:=hall.mpr hn
    rw [accept,ha,hsmall hn,hbound]
    simp only [Bool.true_and]
    exact (branch_exact n index bits).trans (by simp only [NodeMeaning.valid,hn,true_and])
  · have ha:(natural 0 && natural 1 && natural 2)=false:=Bool.eq_false_iff.mpr (by intro ha;exact hn (hall.mp ha))
    simp only [accept,ha,Bool.false_and,Bool.false_eq_true,NodeMeaning.valid,hn,false_and]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeDecision
