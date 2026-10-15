import Proof.PCP.PCPPRequestNodeFieldsLayout

/-! Abstract controller sizes keep three actual cold calls out of kernel
normalization during their data-preserving composition. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeFields
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem restart_joined {t a b c : ℕ} (first : ExecutionReceipt t a)
    (second : ExecutionReceipt t b) (q : Fin c) :
    Composition.restart (Composition.joinedReceipt first second).final q=
      Composition.restart second.final q := rfl

theorem join_three_run {t a b c : ℕ} (first : Machine t a) (second : Machine t b)
    (third : Machine t c) (f g h : ℕ) (initial : Configuration t a)
    (x : ExecutionReceipt t a) (y : ExecutionReceipt t b) (z : ExecutionReceipt t c)
    (hx : runFrom first f initial=some x)
    (hy : runFrom second g (Composition.restart x.final second.start)=some y)
    (hz : runFrom third h (Composition.restart y.final third.start)=some z) :
    ∃ out,runFrom (Composition.machine (Composition.machine first second) third)
      ((f+1+g)+1+h) (Composition.leftConfig c (Composition.leftConfig b initial))=some out ∧
      out.final.heads=z.final.heads ∧ out.final.tapes=z.final.tapes ∧
      out.steps=x.steps+1+y.steps+1+z.steps := by
  have hxy := Composition.run_join first second f g initial x y hx hy
  have hz' : runFrom third h
      (Composition.restart (Composition.joinedReceipt x y).final third.start)=some z := by
    rw [restart_joined]
    exact hz
  have hall := Composition.run_join (Composition.machine first second) third _ _ _
    (Composition.joinedReceipt x y) z hxy hz'
  exact ⟨Composition.joinedReceipt (Composition.joinedReceipt x y) z,hall,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.PCPPRequestNodeFields
