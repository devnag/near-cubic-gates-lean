import Proof.PCP.PCPPNativeQueryAllocate
import Proof.Circuits.DecompositionCountPosition

/-! Literal cold query-bank layout: original descriptor/stream, raw R/Q,
and the physically computed C/F/G. The two real sentinel drivers are
constructed after the blank workspace is allocated. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryCold
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def allocateSlots (i : Fin 171) : Fin 178 := i.castAdd 7
def widthSlots : Fin 3 → Fin 178 := ![174,172,176]
def countSlots : Fin 3 → Fin 178 := ![175,173,177]
def data (bits fields : List Bool) (R Q C F G phase : ℕ) : Fin 178 → List Bool :=
  Fin.addCases (m := 171) (n := 7)
    (if phase=0 then PCPPNativeQueryAllocate.input bits C F G
      else PCPPNativeQueryReusable.data bits [] 0 C F G [])
    ![fields,if 2≤phase then UnaryTemplate.tape R else [],
      if 3≤phase then UnaryTemplate.tape Q else [],List.replicate R true,List.replicate Q true,
      if 2≤phase then List.replicate (R+3) false else [],
      if 3≤phase then List.replicate (Q+3) false else []]
noncomputable def first := RecoveryFocus.machine allocateSlots PCPPNativeQueryAllocate.machine
noncomputable def second := RecoveryFocus.machine widthSlots (DimensionTemplate.machine false)
noncomputable def third := RecoveryFocus.machine countSlots (DimensionTemplate.machine false)
noncomputable def prepare := Composition.machine (Composition.machine first second) third
def directions (i : Fin 178) : HeadMove := if i=172 ∨ i=173 then .right else .stay
def position := DecompositionCountPosition.move directions
noncomputable def machine := Composition.machine prepare position
def budget (R Q G : ℕ) := 2*G+2*R+2*Q+24

theorem first_run (bits fields : List Bool) (R Q C F G : ℕ) :
    ClockJoin.ReadyRun first (2*G+4) (data bits fields R Q C F G 0) (data bits fields R Q C F G 1) := by
  have h := (PCPPNativeQueryAllocate.allocate_run bits C F G).focus allocateSlots
    (by intro a b h; apply Fin.ext; exact congrArg (fun j : Fin 178 => j.val) h) (data bits fields R Q C F G 0)
    (by intro i; simp [data,allocateSlots])
  rw [HierarchyWidth.install_eq allocateSlots
    (by intro a b h; apply Fin.ext; exact congrArg (fun j : Fin 178 => j.val) h) _ (data bits fields R Q C F G 1) _
    (by intro i; simp [data,allocateSlots]) (by
      intro i
      refine Fin.addCases (m := 171) (n := 7) (fun j hj => ?_) (fun j _ => ?_) i
      · exact False.elim (hj j rfl)
      · fin_cases j <;> rfl)] at h
  exact h

theorem second_run (bits fields : List Bool) (R Q C F G : ℕ) :
    ClockJoin.ReadyRun second (2*R+8) (data bits fields R Q C F G 1) (data bits fields R Q C F G 2) := by
  have h := (DimensionTemplate.ready false R).focus widthSlots (by decide) (data bits fields R Q C F G 1)
    (by intro i; fin_cases i <;> rfl)
  rw [HierarchyWidth.install_eq widthSlots (by decide) _ (data bits fields R Q C F G 2) _
    (by intro i; fin_cases i <;> rfl) (by
      intro i
      refine Fin.addCases (m := 171) (n := 7) (fun _ _ => ?_) (fun j hj => ?_) i
      · simp [data]
      · have h1 := hj 1
        have h2 := hj 2
        fin_cases j <;> simp_all [data,widthSlots,Fin.addCases])] at h
  exact h

theorem third_run (bits fields : List Bool) (R Q C F G : ℕ) :
    ClockJoin.ReadyRun third (2*Q+8) (data bits fields R Q C F G 2) (data bits fields R Q C F G 3) := by
  have h := (DimensionTemplate.ready false Q).focus countSlots (by decide) (data bits fields R Q C F G 2)
    (by intro i; fin_cases i <;> rfl)
  rw [HierarchyWidth.install_eq countSlots (by decide) _ (data bits fields R Q C F G 3) _
    (by intro i; fin_cases i <;> rfl) (by
      intro i
      refine Fin.addCases (m := 171) (n := 7) (fun _ _ => ?_) (fun j hj => ?_) i
      · simp [data]
      · have h1 := hj 1
        have h2 := hj 2
        fin_cases j <;> simp_all [data,countSlots,Fin.addCases])] at h
  exact h

theorem prepare_run (bits fields : List Bool) (R Q C F G : ℕ) :
    ClockJoin.ReadyRun prepare (2*G+2*R+2*Q+22)
      (data bits fields R Q C F G 0) (data bits fields R Q C F G 3) := by
  have h := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (first_run bits fields R Q C F G) (second_run bits fields R Q C F G))
    (third_run bits fields R Q C F G)
  have ht : (2*G+4)+1+(2*R+8)+1+(2*Q+8)=2*G+2*R+2*Q+22 := by omega
  rw [ht] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPPNativeQueryCold
