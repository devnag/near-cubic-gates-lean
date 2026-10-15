import Proof.Supplier.EquationScalarWiden

namespace NearCubicWires.RepairOrdinary.EquationWiden
open LocalBitMultitape RecoveryExecution SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_widen (p n : ℕ) (hn : n<2^p) :
    binary (p+1) n=binary p n++[false] := by
  induction p generalizing n with
  | zero =>
    have he : n=0 := by simpa using hn
    subst n
    rfl
  | succ p ih =>
    have hd : n/2<2^p := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).2
      (by simpa [pow_succ] using hn)
    change (n%2==1)::binary (p+1) (n/2) =
      (n%2==1)::(binary p (n/2)++[false])
    exact congrArg (fun bits => (n%2==1)::bits) (ih _ hd)

theorem signMagnitude_widen (p : ℕ) (z : ℤ) (hz : z.natAbs<2^p) :
    signMagnitude (p+1) z=signMagnitude p z++[false] := by
  simp only [signMagnitude,binary_widen p z.natAbs hz,List.cons_append]

/-- The streaming machine now emits the literal widened scalar at the
matrix Request codec, preserving both global source and append cursors. -/
theorem scalar_run (pre suffix out : List Bool) (p : ℕ) (z : ℤ)
    (hz : z.natAbs<2^p) :
    ∃ r,runFrom machine (2*p+5)
      (cfg 0 (pre++frame (signMagnitude p z)++suffix) pre.length out)=some r ∧
      r.final=cfg 4 (pre++frame (signMagnitude p z)++suffix)
        (pre.length+2*p+3) (out++frame (signMagnitude (p+1) z)) ∧
      r.steps=2*p+5 := by
  have h := field_run pre (signMagnitude p z) suffix out
  rw [←signMagnitude_widen p z hz] at h
  simpa only [signMagnitude_length,frame_length,Nat.mul_add,Nat.mul_one,
    Nat.add_assoc,show 2+3=5 from rfl,show 2+1=3 from rfl] using h

end NearCubicWires.RepairOrdinary.EquationWiden
