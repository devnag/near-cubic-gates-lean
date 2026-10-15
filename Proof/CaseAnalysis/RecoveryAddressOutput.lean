import Proof.CaseAnalysis.RecoveryAddressBudget

/-! The original address expression returns a reusable bank. Only its graph,
counter and consumed outer stack change during the final reverse fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RecoveryBoundedSelectorFinish (folded fold_output_heads fold_output_data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fixedHeads : Fin 41→ℕ:=heads [] [] 0
def fixedData (index C D value limit total : ℕ) (source : List Bool):=
  data index 0 C D value limit total [] source []

theorem heads_override (out stack : List Bool) (pos : ℕ) :
    heads out stack pos=fun i=>if i=20 then out.length else if i=37 then pos
      else if i=38 then stack.length else fixedHeads i := by
  funext i
  fin_cases i <;> rfl

theorem data_override (index base C D value limit total : ℕ) (out source stack : List Bool) :
    data index base C D value limit total out source stack=
      fun i=>if i=20 then out else if i=25 then List.replicate base true
        else if i=38 then stack else fixedData index C D value limit total source i := by
  funext i
  fin_cases i <;> rfl

def afterData (index base C D value limit total erased : ℕ) (out source pre : List Bool) (i : Fin 41):=
  if i=38 then pre++List.replicate erased false else data index base C D value limit total out source pre i

theorem output_heads (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ) :
    (reverseOutput index base C D value limit total pos out source pre refs).heads=
      heads (folded base out refs).out pre pos := by
  funext i
  by_cases hi : ∃ j,foldSlots j=i
  · obtain ⟨j,rfl⟩:=hi
    simp only [reverseOutput,RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective,fold_output_heads]
    fin_cases j <;> rfl
  · simp only [reverseOutput,RecoveryFocus.config,RecoveryFocus.pick,dif_neg hi]
    have h20 : i≠20:=fun h=>hi ⟨20,h.symm⟩
    have h38 : i≠38:=fun h=>hi ⟨31,h.symm⟩
    simp only [heads_override,if_neg h20,if_neg h38]

theorem output_tapes (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ) :
    (reverseOutput index base C D value limit total pos out source pre refs).tapes=
      afterData index (folded base out refs).acc C D value limit total (folded base out refs).erased
        (folded base out refs).out source pre := by
  funext i
  by_cases hi : ∃ j,foldSlots j=i
  · obtain ⟨j,rfl⟩:=hi
    simp only [reverseOutput,RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective,fold_output_data]
    fin_cases j <;> first
    | rfl
    | exact ZeroPadding.pad_zero _
  · simp only [reverseOutput,RecoveryFocus.config,RecoveryFocus.pick,dif_neg hi]
    have h20 : i≠20:=fun h=>hi ⟨20,h.symm⟩
    have h25 : i≠25:=fun h=>hi ⟨25,h.symm⟩
    have h38 : i≠38:=fun h=>hi ⟨31,h.symm⟩
    simp only [afterData,data_override,if_neg h20,if_neg h25,if_neg h38]

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
