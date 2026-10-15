import Proof.Supplier.EquationScalar
import Proof.PCP.PCPSerializerTapeSupport

/-! Replay the actual cold scalar in finite zero backing and derive every
local tape's support from its actual trace, for the paid repeated caller. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def paddedInput (C p : Nat) (z : Int) := fun i => ZeroPadding.pad C (input p z i)

theorem padded_run (negate : Bool) (C p : Nat) (z : Int)
    (hz : z.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ time out,time ≤ 64*(p+1) ∧ ReadyRun (machine negate) time (paddedInput C p z) out ∧
      out 0=ZeroPadding.pad C (frame (signMagnitude p z)) ∧
      out 9=ZeroPadding.pad C (frame (signMagnitude (p+1) (target negate z))) ∧
      (∀ i,(out i).length=C) := by
  obtain ⟨time,out,ht,⟨base,hr,bt,bh,bs⟩,h0,h9⟩ := scalar_run negate p z hz
  obtain ⟨r,hp,hf,hs,_⟩ := ZeroPadding.run_config (machine negate) (fun _=>C) _ _ base hr
  have hi : ZeroPadding.config (fun _=>C) (initialConfiguration (machine negate) (input p z))=
      initialConfiguration (machine negate) (paddedInput C p z) := rfl
  rw [hi] at hp
  have hbound (i : Fin 12) : (base.final.tapes i).length ≤ C := by
    have hinput : (input p z i).length ≤ C := by
      unfold input
      split
      · simp only [frame_length,signMagnitude_length]; omega
      · simp
    have h := PCPSerializerReuse.tape_support (machine negate) time _ base hr i C 0 (by rfl)
      (by exact hinput.trans (Nat.le_max_left _ _))
    have hc : 0+base.steps+1 ≤ C := by omega
    simpa only [max_eq_left hc] using h
  refine ⟨time,fun i=>ZeroPadding.pad C (out i),ht,?_,?_,?_,?_⟩
  · exact ⟨r,hp,by rw [hf]; change (fun i=>ZeroPadding.pad C (base.final.tapes i))=_; rw [bt],
      by intro i; simpa only [hf,ZeroPadding.config] using bh i,hs.trans bs⟩
  · dsimp only; rw [h0]
  · dsimp only; rw [h9]
  · intro i
    change (ZeroPadding.pad C (out i)).length=C
    rw [ZeroPadding.pad_length]
    have hb : (out i).length ≤ C := by rw [←bt]; exact hbound i
    omega

end
end NearCubicWires.RepairOrdinary.EquationScalar
