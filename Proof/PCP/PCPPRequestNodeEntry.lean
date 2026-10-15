import Proof.PCP.PCPPRequestNode

/-! The complete node caller has only one initial source tape; this literal
entry invariant supports paid reusable scratch reset and erasure. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCold
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem extend_zero {m n : ℕ} (hm : 0 < m) {α : Type} (x z : α) :
    Fin.addCases (m := m) (n := n) (motive := fun _ => α)
      (fun i => if i.val=0 then x else z) (fun _ => z)=
      (fun i => if i.val=0 then x else z) := by
  funext i
  refine Fin.addCases (m := m) (n := n) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd]
    split_ifs <;> rfl
  · simp only [Fin.addCases_right,Fin.val_natAdd]
    have hn : m+j.val≠0 := by omega
    rw [if_neg hn]

theorem entry_heads (source : List Bool) (pos : ℕ) :
    (entry source pos).heads=(fun i : Fin 642 => if i=0 then pos else 0) := by
  change Fin.addCases (m := 408) (n := 234) (motive := fun _ => ℕ)
    (Fin.addCases (m := 406) (n := 2) (motive := fun _ => ℕ) (PCPPRequestNodeFields.inputHeads pos) (fun _ => 0))
    (fun _ => 0)=(fun i : Fin 642 => if i=0 then pos else 0)
  have h : PCPPRequestNodeFields.inputHeads pos=(fun i : Fin 406 => if i.val=0 then pos else 0) := by
    funext i
    simp only [PCPPRequestNodeFields.inputHeads,Fin.ext_iff,Fin.val_zero]
  rw [h,extend_zero (by decide),extend_zero (by decide)]
  funext i
  simp only [Fin.ext_iff,Fin.val_zero]

theorem entry_tapes (source : List Bool) (pos : ℕ) :
    (entry source pos).tapes=(fun i : Fin 642 => if i=0 then source else []) := by
  change Fin.addCases (m := 408) (n := 234) (motive := fun _ => List Bool)
    (Fin.addCases (m := 406) (n := 2) (motive := fun _ => List Bool) (PCPPRequestNodeFields.inputTapes source) (fun _ => []))
    (fun _ => [])=(fun i : Fin 642 => if i=0 then source else [])
  have h : PCPPRequestNodeFields.inputTapes source=(fun i : Fin 406 => if i.val=0 then source else []) := by
    funext i
    simp only [PCPPRequestNodeFields.inputTapes,Fin.ext_iff,Fin.val_zero]
  rw [h,extend_zero (by decide),extend_zero (by decide)]
  funext i
  simp only [Fin.ext_iff,Fin.val_zero]

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCold
