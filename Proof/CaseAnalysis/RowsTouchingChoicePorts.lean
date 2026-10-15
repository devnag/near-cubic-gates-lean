import Proof.CaseAnalysis.RowsTouchingChoiceLayout

/-! Check finite tape cases with abstract words, before substituting the
binary frames and padded counters into the actual run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem vector_outside {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 b4 b5 b6 b9 : α)
    (i : Fin 12) (h4:i=4→b4=a4) (h5:i=5→b5=a5) (h6:i=6→b6=a6) (h9:i=9→b9=a9):
    (![a0,a1,a2,a3,b4,b5,b6,a7,a8,b9,a10,a11] : Fin 12→α) i=
      (![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11] : Fin 12→α) i:=by
  fin_cases i <;> simp_all

theorem copy_installed (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : List Bool) (mode : Bool):
    install (copySlots mode) ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11]
      ![a10,a10,a11,a7]=
      ![a0,a1,a2,a3,if mode then a4 else a10,if mode then a10 else a5,a6,a7,a8,a9,a10,a11]:=by
  apply HierarchyWidth.install_eq _ (copy_injective mode)
  · intro j;cases mode <;> fin_cases j <;> rfl
  · intro i hi
    apply vector_outside
    · intro he;subst i;cases mode
      · exact False.elim (hi 1 rfl)
      · rfl
    · intro he;subst i;cases mode
      · rfl
      · exact False.elim (hi 1 rfl)
    · intro _;rfl
    · intro _;rfl

theorem product_installed (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 acc scratch : List Bool) (mode : Bool):
    install (productSlots mode) ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11]
      ![if mode then a1 else a0,acc,scratch,a7,a8,if mode then a3 else a2]=
      ![a0,a1,a2,a3,if mode then a4 else acc,if mode then acc else a5,scratch,a7,a8,a9,a10,a11]:=by
  apply HierarchyWidth.install_eq _ (product_injective mode)
  · intro j;cases mode <;> fin_cases j <;> rfl
  · intro i hi
    apply vector_outside
    · intro he;subst i;cases mode
      · exact False.elim (hi 1 rfl)
      · rfl
    · intro he;subst i;cases mode
      · rfl
      · exact False.elim (hi 1 rfl)
    · intro he;subst i;exact False.elim (hi 2 rfl)
    · intro _;rfl

theorem compare_installed (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 flag : List Bool):
    install compareSlots ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11] ![a4,a5,flag,a7]=
      ![a0,a1,a2,a3,a4,a5,a6,a7,a8,flag,a10,a11]:=by
  apply HierarchyWidth.install_eq _ (by decide)
  · intro j;fin_cases j <;> rfl
  · intro i hi
    apply vector_outside
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro he;subst i;exact False.elim (hi 2 rfl)

theorem guard_installed (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 flag : List Bool):
    install guardSlots ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11] ![a2,flag]=
      ![a0,a1,a2,a3,a4,a5,a6,a7,a8,flag,a10,a11]:=by
  apply HierarchyWidth.install_eq _ (by decide)
  · intro j;fin_cases j <;> rfl
  · intro i hi
    apply vector_outside
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro he;subst i;exact False.elim (hi 1 rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
