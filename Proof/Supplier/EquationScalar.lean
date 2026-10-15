import Proof.Supplier.EquationScalarRun

/-! Cold signed successor and negation for the literal matrix scalar codec.
The opcode is static; both width and sign are read from the actual field. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine (negate : Bool) := Graph.machine negate
def input (p : Nat) (z : Int) : Fin 12→List Bool :=
  fun i => if i=0 then frame (signMagnitude p z) else []
def target (negate : Bool) (z : Int) := if negate then -z else z+1

theorem present_binary (w n : Nat) (hn : n<2^w) :
    DecompositionBitFields.present (binary w n)=decide (0<n) := by
  rw [Scan.present_value,binary_value w n hn]

/-- Both transforms preserve the complete source, emit an exact fresh
frame on tape9, and physically return every tape head to zero. -/
theorem scalar_run (negate : Bool) (p : Nat) (z : Int) (hz : z.natAbs<2^p) :
    ∃ time out,time ≤ 64*(p+1) ∧ ReadyRun (machine negate) time (input p z) out ∧
      out 0=frame (signMagnitude p z) ∧ out 9=frame (signMagnitude (p+1) (target negate z)) := by
  have hi : EquationScalar.input p z=Prepare.input (decide (z<0)) (binary p z.natAbs) := rfl
  rw [hi]
  cases negate
  · cases z with
    | ofNat n =>
      have hn : n<2^p := hz
      have hz0 : ¬(n : Int)<0 := by omega
      have hz1 : ¬(n : Int)+1<0 := by omega
      have habs : ((n : Int)+1).natAbs=n+1 := by
        have he : (n : Int)+1=((n+1 : Nat) : Int) := by omega
        rw [he]; rfl
      have h := Graph.positive_run p n hn
      simpa [Graph.Result,machine,target,signMagnitude,Emit.negative,hz0,hz1,habs] using h
    | negSucc n =>
      have hn : n+1<2^p := hz
      have hm : n<2^(p+1) := by rw [pow_succ]; have hp := Nat.two_pow_pos p; omega
      have he : Int.negSucc n+1= -(n : Int) := by omega
      have h := Graph.negative_run p (n+1) hn (by omega)
      simpa [Graph.Result,machine,target,signMagnitude,Emit.negative,he,
        present_binary (p+1) n hm] using h
  · cases z with
    | ofNat n =>
      have hn : n<2^p := hz
      have hz0 : ¬(n : Int)<0 := by omega
      have hm : n<2^(p+1) := by rw [pow_succ]; have hp := Nat.two_pow_pos p; omega
      have h := Graph.negate_run false p n hn
      simpa [Graph.Result,machine,target,signMagnitude,Emit.negative,hz0,
        present_binary (p+1) n hm] using h
    | negSucc n =>
      have hn : n+1<2^p := hz
      have hz1 : ¬(n : Int)+1<0 := by omega
      have habs : ((n : Int)+1).natAbs=n+1 := by
        have he : (n : Int)+1=((n+1 : Nat) : Int) := by omega
        rw [he]; rfl
      have h := Graph.negate_run true p (n+1) hn
      simpa [Graph.Result,machine,target,signMagnitude,Emit.negative,hz1,habs] using h

theorem successor_run (p : Nat) (z : Int) (hz : z.natAbs<2^p) :
    ∃ time out,time ≤ 64*(p+1) ∧ ReadyRun (machine false) time (input p z) out ∧
      out 0=frame (signMagnitude p z) ∧ out 9=frame (signMagnitude (p+1) (z+1)) :=
  scalar_run false p z hz

theorem negate_run (p : Nat) (z : Int) (hz : z.natAbs<2^p) :
    ∃ time out,time ≤ 64*(p+1) ∧ ReadyRun (machine true) time (input p z) out ∧
      out 0=frame (signMagnitude p z) ∧ out 9=frame (signMagnitude (p+1) (-z)) :=
  scalar_run true p z hz

end
end NearCubicWires.RepairOrdinary.EquationScalar
