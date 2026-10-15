import Proof.MachineModel.OrdinaryMatrixBucketGateNativeLoop

/-! The unweighted left mask and both loop cursor offsets are physically
written from the cold bucket bank. No coefficient-bit or driver-head value
is installed by a semantic configuration replacement. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketGateBootstrap
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 36 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun i => if i=6 then some true else none,
    fun i => if i=22 ∨ i=35 then .right else .stay⟩
noncomputable def target (r : Request) (unused : Fin 3 → List Bool) :=
  MatrixBucketGateNativeLoop.cfg r 0 0 (MatrixBatchGateNativeLoop.output r) 0 [] unused (MatrixBucketGateNativeLoop.cold r)
noncomputable def input (r : Request) (unused : Fin 3 → List Bool) :=
  Function.update (target r unused).tapes 6 (List.replicate (MatrixScoreReusableRanks.D r) false)

theorem target_mask (r : Request) (unused : Fin 3 → List Bool) :
    (target r unused).tapes 6=ZeroPadding.pad (MatrixScoreReusableRanks.D r) [true] := by
  simp only [target,MatrixBucketGateNativeLoop.cfg_tapes]
  rfl

theorem boot_run (r : Request) (unused : Fin 3 → List Bool) :
    ∃ actual,run machine 1 (input r unused)=some actual ∧
      actual.final.heads=(target r unused).heads ∧ actual.final.tapes=(target r unused).tapes ∧ actual.steps=1 := by
  let entry := initialConfiguration machine (input r unused)
  let final : Configuration 36 2 := ⟨1,(target r unused).heads,(target r unused).tapes⟩
  have hs : step machine entry=some final := by
    simp only [step,machine,entry,initialConfiguration]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      change HeadMove.apply (if i=22 ∨ i=35 then .right else .stay) 0=(target r unused).heads i
      simp only [target,MatrixBucketGateNativeLoop.cfg_heads]
      fin_cases i <;> rfl
    · funext i
      by_cases hi : i=6
      · subst i
        change writeTapeBit (input r unused 6) 0 true=(target r unused).tapes 6
        rw [target_mask]
        simp only [input,Function.update_self]
        change writeTapeBit (ZeroPadding.pad (MatrixScoreReusableRanks.D r) []) 0 true=_
        rw [ZeroPadding.write_pad]
        rfl
      · change (match if i=6 then some true else none with
          | none => input r unused i
          | some bit => writeTapeBit (input r unused i) 0 bit)=(target r unused).tapes i
        simp [hi,input]
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

end NearCubicWires.RepairOrdinary.MatrixBucketGateBootstrap
