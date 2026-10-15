import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
namespace BankExtension
/-- The finite bank identity is proved without unfolding the printer's large
tape-count expression or reducing dependent addCases equality transports. -/
theorem bank_extend (base small large : Nat) (h : small ≤ large)
    (words : Fin 9 → List Bool) :
    ∀ j : Fin (base+(10+(7+small))),
      Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin base => [])
        (fun k : Fin (10+(7+large)) => if hk : k.val<9 then words ⟨k.val,hk⟩ else [])
        (⟨j.val, by have hj := j.isLt; omega⟩ : Fin (base+(10+(7+large)))) =
      Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin base => [])
        (fun k : Fin (10+(7+small)) => if hk : k.val<9 then words ⟨k.val,hk⟩ else []) j := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin base => [])
      (fun k : Fin (10+(7+large)) => if hk : k.val<9 then words ⟨k.val,hk⟩ else [])
      (Fin.castAdd (10+(7+large)) k) = _
    simp only [Fin.addCases_left]
  · let k' : Fin (10+(7+large)) := ⟨k.val, by have hk := k.isLt; omega⟩
    change Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin base => [])
      (fun k : Fin (10+(7+large)) => if hk : k.val<9 then words ⟨k.val,hk⟩ else [])
      (Fin.natAdd base k') = _
    simp only [Fin.addCases_right, k']

end BankExtension
