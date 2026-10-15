import Proof.CaseAnalysis.HierarchyRequestBound

/-! The original request producer has exactly one physical data input. This
lookup permits direct docking on the retained refuter answer in the common
program; all remaining tapes belong to its initially blank workspace. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyRequest
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem append_blank_lookup {t e index : Nat} (hi : index < t)
    (value : List Bool) (a : Fin t → List Bool)
    (ha : ∀ j, a j=if j.val=index then value else []) (i : Fin (t+e)) :
    Fin.addCases a (fun _ : Fin e => []) i=if i.val=index then value else [] := by
  refine Fin.addCases (m:=t) (n:=e) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd]
    rw [ha j]
    split_ifs <;> rfl
  · simp only [Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem clock_input_lookup (D : Nat) (bits : List Bool)
    (i : Fin (CloseoutHierarchyClock.Input.tapes D)) :
    CloseoutHierarchyClock.Input.input D bits i=if i.val=2 then frame bits else [] := by
  have h := HierarchyFromInput.tapes_lower D
  exact append_blank_lookup (by omega : 2 < HierarchyFromInput.tapes D)
    (frame bits) (HierarchyFromInput.input D bits) (by intro j; rfl) i

theorem input_lookup (k : Nat) (bits : List Bool) (i : Fin (tapes k)) :
    input k bits i=if i.val=2 then frame bits else [] := by
  have h := HierarchyFromInput.tapes_lower (k+2)
  have hi : 2 < CloseoutHierarchyClock.Input.tapes (k+2) := by
    unfold CloseoutHierarchyClock.Input.tapes
    omega
  exact append_blank_lookup hi (frame bits) (CloseoutHierarchyClock.Input.input (k+2) bits)
    (clock_input_lookup (k+2) bits) i

end NearCubicWires.RepairSource.CloseoutHierarchyRequest
