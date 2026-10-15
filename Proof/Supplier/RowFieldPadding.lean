import Proof.Supplier.RowCoordinateMeaning
import Proof.Amplification.RecoveryPaddedCopyMeaning

/-! Reuse the checked fixed-width copier on the isolated signed coefficient
field. The sign remains its first bit and every extra magnitude bit is
physically written as zero. Allocated source and work padding are retained. -/
namespace NearCubicWires.RepairOrdinary.RowFieldPadding
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_extend (w p x : ℕ) (hw : w ≤ p) (hx : x<2^w) :
    binary w x++List.replicate (p-w) false=binary p x := by
  have h := BoundedCounter.binary_of_value (binary w x++List.replicate (p-w) false)
  have hl : (binary w x++List.replicate (p-w) false).length=p := by simp; omega
  rw [hl,RadixSemantics.value_append,binary_value w x hx,RecoveryRootIteration.zeros_value] at h
  simpa only [Nat.mul_zero,Nat.add_zero] using h.symm

theorem signed_extend (w p : ℕ) (z : ℤ) (hw : w ≤ p) (hz : z.natAbs<2^w) :
    RecoveryColdPaddedCopy.data (signMagnitude w z) (p+1)=signMagnitude p z := by
  rw [RecoveryColdPaddedCopy.data_eq_pad _ _ (by simp [signMagnitude]; omega)]
  simp only [signMagnitude,List.length_cons,binary_length,Nat.add_sub_add_right,List.cons_append]
  rw [binary_extend w p z.natAbs hw hz]

def caps (F : ℕ) (i : Fin 4) := if i=2 then 0 else F
def padded (F : ℕ) (a : Fin 4→List Bool) := fun i=>ZeroPadding.pad (caps F i) (a i)
def input (w p F : ℕ) (z : ℤ) : Fin 4→List Bool :=
  ![ZeroPadding.pad F (frame (signMagnitude w z)),List.replicate F false,
    CompareMachine.word (p+1),List.replicate F false]
def output (w p F : ℕ) (z : ℤ) : Fin 4→List Bool :=
  ![ZeroPadding.pad F (frame (signMagnitude w z)),ZeroPadding.pad F (frame (signMagnitude p z)),
    CompareMachine.word (p+1),List.replicate F false]

theorem padding_ready (w p F : ℕ) (z : ℤ) (hw : w ≤ p) (hz : z.natAbs<2^w)
    (hF : 2*p+5 ≤ F) :
    ReadyRun RecoveryColdPaddedCopy.machine (4*p+12) (input w p F z) (output w p F z) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := RecoveryColdPaddedCopy.copy_ready (signMagnitude w z) (p+1)
  obtain ⟨a,ha,af,asteps,_⟩ := ZeroPadding.run_config RecoveryColdPaddedCopy.machine (caps F) _ _ r hr
  have hin : ZeroPadding.config (caps F)
      (initialConfiguration RecoveryColdPaddedCopy.machine
        ![frame (signMagnitude w z),[],CompareMachine.word (p+1),[]])=
      initialConfiguration RecoveryColdPaddedCopy.machine (input w p F z) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,caps,input,ZeroPadding.pad]
  rw [hin] at ha
  have ht : 4*(p+1)+8=4*p+12 := by omega
  rw [ht] at ha
  refine ⟨a,ha,?_,?_,asteps.trans (rs.trans ht)⟩
  · rw [af]
    change padded F r.final.tapes=output w p F z
    rw [rt,signed_extend w p z hw hz]
    funext i
    fin_cases i <;> simp [padded,caps,output,ZeroPadding.pad,List.length_replicate,
      Nat.add_sub_of_le (show 2*(p+1)+3 ≤ F by omega)]
  · intro i
    rw [af]
    exact rh i

end NearCubicWires.RepairOrdinary.RowFieldPadding
