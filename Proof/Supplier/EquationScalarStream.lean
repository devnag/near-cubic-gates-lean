import Proof.Supplier.EquationScalarStreamFirst
import Proof.Supplier.EquationScalarStreamTail

/-! One complete reusable streaming scalar transformation. The local bank
is physically isolated, transformed, copied and erased on every call. -/
namespace NearCubicWires.RepairOrdinary.EquationScalarStream
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem scalar_run (negate : Bool) (pre suffix out : List Bool) (C p : Nat) (z : Int)
    (hz : z.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ r,runFrom (machine negate) (budget C p)
      (entry negate C pre.length (pre++frame (signMagnitude p z)++suffix) out)=some r ∧
      r.final.heads=heads (pre.length+2*p+3)
        (out++frame (signMagnitude (p+1) (EquationScalar.target negate z))).length ∧
      r.final.tapes=tapes C (pre++frame (signMagnitude p z)++suffix)
        (out++frame (signMagnitude (p+1) (EquationScalar.target negate z))) ∧ r.steps ≤ budget C p := by
  obtain ⟨time,a,base,hbudget,hb,bh,bt,b0,b10,b13,b14,b15,b16,bsupport,_bs⟩ :=
    first_run negate pre suffix out C p z hz hC
  let bits := signMagnitude (p+1) (EquationScalar.target negate z)
  let padding := List.replicate (C-(frame bits).length) false
  have hcap : 2*bits.length+1 ≤ C := by simp [bits]; omega
  obtain ⟨last,hl,lh,lt,ls⟩ := tail_run C (pre.length+2*p+3) bits padding out a hcap
    (by intro j; exact (bsupport j).le) b10 b13 b14 b15 b16
  have he : Composition.restart base.final tail.start=
      (⟨tail.start,heads (pre.length+2*p+3) out.length,a⟩ : Configuration 17 _) := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  rw [←he] at hl
  have joined := Composition.run_join (first negate) tail _ _ _ base last hb hl
  have htime : time+1+(4*bits.length+2*C+9) ≤ budget C p := by
    simp only [bits,signMagnitude_length,budget]
    omega
  have hlong := runFrom_moreFuel (machine negate) _
    (budget C p-(time+1+(4*bits.length+2*C+9))) _ (Composition.joinedReceipt base last) joined
  have hfull : (time+1+(4*bits.length+2*C+9))+
      (budget C p-(time+1+(4*bits.length+2*C+9)))=budget C p := by omega
  rw [hfull] at hlong
  refine ⟨Composition.joinedReceipt base last,hlong,lh,?_,?_⟩
  · change last.final.tapes=_
    rw [lt,b0]
  · exact runFrom_steps_le (machine negate) (budget C p) _ _ hlong

theorem successor_run (pre suffix out : List Bool) (C p : Nat) (z : Int)
    (hz : z.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ r,runFrom (machine false) (budget C p)
      (entry false C pre.length (pre++frame (signMagnitude p z)++suffix) out)=some r ∧
      r.final.heads=heads (pre.length+2*p+3) (out++frame (signMagnitude (p+1) (z+1))).length ∧
      r.final.tapes=tapes C (pre++frame (signMagnitude p z)++suffix)
        (out++frame (signMagnitude (p+1) (z+1))) ∧ r.steps ≤ budget C p :=
  scalar_run false pre suffix out C p z hz hC

theorem negate_run (pre suffix out : List Bool) (C p : Nat) (z : Int)
    (hz : z.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ r,runFrom (machine true) (budget C p)
      (entry true C pre.length (pre++frame (signMagnitude p z)++suffix) out)=some r ∧
      r.final.heads=heads (pre.length+2*p+3) (out++frame (signMagnitude (p+1) (-z))).length ∧
      r.final.tapes=tapes C (pre++frame (signMagnitude p z)++suffix)
        (out++frame (signMagnitude (p+1) (-z))) ∧ r.steps ≤ budget C p :=
  scalar_run true pre suffix out C p z hz hC

end
end NearCubicWires.RepairOrdinary.EquationScalarStream
