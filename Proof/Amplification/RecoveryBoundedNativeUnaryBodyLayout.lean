import Proof.Amplification.RecoveryBoundedNativeUnaryFlag

/-! The actual value driver keeps its cursor across literal iterations.
The polarity write precedes the checked literal step; its cursor advance
is an executed transition after the reusable step has halted. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryBody
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagSlots : Fin 2→Fin 35:=![29,34]
def valueSlot : Fin 1→Fin 35:=fun _=>34
def heads (out stack : List Bool) (pos : ℕ) : Fin 35→ℕ :=
  Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
    (RecoveryBoundedNativeLiteralStep.heads out stack) (fun _=>pos)
def data (index position C value : ℕ) (negative : Bool) (out stack : List Bool) : Fin 35→List Bool :=
  Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedNativeLiteralStep.data index position C negative out stack 0)
    (fun _=>List.replicate value true)
noncomputable def first:=RecoveryFocus.machine flagSlots RecoveryBoundedNativeUnaryFlag.machine
noncomputable def second:=TapeEmbedding.machine 1 RecoveryBoundedNativeLiteralStep.machine
noncomputable def last:=RecoveryFocus.machine valueSlot RecoveryBoundedNativeUnaryFlag.advance
noncomputable def machine:=Composition.machine (Composition.machine first second) last
noncomputable def entry (index position C value pos : ℕ) (negative : Bool) (out stack : List Bool) :=
  (⟨machine.start,heads out stack pos,data index position C value negative out stack⟩ : Configuration 35 _)

theorem flag_input (index position C value pos : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 2) :
    heads out stack pos (flagSlots j)=![0,pos] j ∧
    data index position C value negative out stack (flagSlots j)=![[negative],List.replicate value true] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩
theorem flag_tapes (index position C value : ℕ) (old negative : Bool) (out stack : List Bool) :
    install flagSlots (data index position C value old out stack)
      ![[negative],List.replicate value true]=data index position C value negative out stack := by
  apply HierarchyWidth.install_eq flagSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 0
    fin_cases i
    all_goals first | exact False.elim (h rfl) |
      simp [data,Fin.addCases,RecoveryBoundedNativeLiteralStep.data,
        RecoveryBoundedNativeLiteralStack.data,RecoveryBoundedNativeLiteral.data]

theorem value_input (index position C value pos : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 1) :
    heads out stack pos (valueSlot j)=pos ∧
    data index position C value negative out stack (valueSlot j)=List.replicate value true := by
  fin_cases j; exact ⟨rfl,rfl⟩
theorem heads_old (out stack : List Bool) (pos next : ℕ) (i : Fin 35) (hi : i≠34) :
    heads out stack pos i=heads out stack next i := by
  refine Fin.addCases (m:=34) (n:=1) (motive:=fun i=>i≠34 → heads out stack pos i=heads out stack next i) ?_ ?_ i hi
  · intro j _
    simp only [heads,Fin.addCases_left]
  · intro j hj
    fin_cases j
    exact False.elim (hj rfl)

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryBody
