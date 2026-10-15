import Proof.CaseAnalysis.RecoveryAddressNodeBank

/-! Exact address-call wiring in the retained original universal-node bank.
The existing D, C outer stack and L are shared sequentially by both calls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addressSlots : Fin 42→Fin 51:=
  Fin.addCases (m:=36) (n:=6) (motive:=fun _=>Fin 51) (fun j=>j.castAdd 15) ![39,49,40,46,50,43]
theorem address_injective : Function.Injective addressSlots := by decide
noncomputable def addressMachine:=RecoveryFocus.machine addressSlots RecoveryBoundedAddressReuse.machine

theorem address_heads (out : List Bool) (j : Fin 42) :
    heads out (addressSlots j)=RecoveryBoundedAddressReuse.finalHeads out j := by
  fin_cases j <;> rfl

theorem address_tapes (index base C D value limit total L : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond savedConstant address : List Bool) (count : ℕ) (hC : 1 ≤ C) (j : Fin 42) :
    data index base C D value limit total L out source secondIndex savedFirst savedSecond savedConstant address count (addressSlots j)=
      RecoveryBoundedAddressReuse.finalData index base C D value limit count L out address j := by
  fin_cases j
  all_goals first
  | rfl
  | exact (ZeroPadding.pad_zero _).symm
  | (change List.replicate C false=ZeroPadding.pad 0 (ZeroPadding.pad C [false]);
      rw [ZeroPadding.pad_zero];exact (RecoveryBoundedSelectorLoop.pad_false C hC).symm)

def fixedHeads : Fin 51→ℕ:=heads []
theorem heads_override (out : List Bool) : heads out=fun i=>if i=20 then out.length else fixedHeads i := by
  funext i
  fin_cases i <;> rfl
def runFixedData (index C D limit total L : ℕ) (source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond savedConstant address : List Bool) (count : ℕ):=
  data index 0 C D 0 limit total L [] source secondIndex savedFirst savedSecond savedConstant address count
theorem run_data_override (index base C D value limit total L : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond savedConstant address : List Bool) (count : ℕ) :
    data index base C D value limit total L out source secondIndex savedFirst savedSecond savedConstant address count=
      fun i=>if i=20 then out else if i=25 then List.replicate base true
        else if i=34 then ZeroPadding.pad C (List.replicate value true)
        else runFixedData index C D limit total L source secondIndex savedFirst savedSecond savedConstant address count i := by
  funext i
  fin_cases i <;> rfl

theorem address_install (index base acc C D value nextValue limit total L : ℕ) (out result source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond savedConstant address : List Bool) (count : ℕ) (hC : 1 ≤ C) :
    install addressSlots (data index base C D value limit total L out source secondIndex savedFirst savedSecond savedConstant address count)
      (RecoveryBoundedAddressReuse.finalData index acc C D nextValue limit count L result address)=
      data index acc C D nextValue limit total L result source secondIndex savedFirst savedSecond savedConstant address count := by
  apply HierarchyWidth.install_eq addressSlots address_injective
  · exact address_tapes index acc C D nextValue limit total L result source secondIndex savedFirst savedSecond savedConstant address count hC
  · intro i hi
    have h20 : i≠20:=fun h=>hi 20 h.symm
    have h25 : i≠25:=fun h=>hi 25 h.symm
    have h34 : i≠34:=fun h=>hi 34 h.symm
    simp only [run_data_override,if_neg h20,if_neg h25,if_neg h34]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
