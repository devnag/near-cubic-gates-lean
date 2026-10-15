import Proof.Amplification.RecoveryHeaderBound

/-! Produce the literal valuation cap3(B+1) from the already materialized
widthW=B+2. The first width mark is skipped; every remaining mark emits
three actual output marks. No numeric input or runtime offset is supplied. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word := CompareMachine.word

def raw : Machine 2 6 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==5
  rule := fun q bits=> ![
    some ⟨1,![none,some false],fun _=>.right⟩,
    some ⟨2,fun _=>none,![.right,.stay]⟩,
    some (if bits 0 then ⟨3,![none,some true],![.stay,.right]⟩
      else ⟨5,fun _=>none,fun _=>.stay⟩),
    some ⟨4,![none,some true],![.stay,.right]⟩,
    some ⟨2,![none,some true],fun _=>.right⟩,none] q

def cfg (n k : Nat) : Configuration 2 6 :=
  ⟨2,![k+2,3*k+1],![word (n+1),word (3*k)]⟩
def mid1 (n k : Nat) : Configuration 2 6 :=
  ⟨3,![k+2,3*k+2],![word (n+1),word (3*k+1)]⟩
def mid2 (n k : Nat) : Configuration 2 6 :=
  ⟨4,![k+2,3*k+3],![word (n+1),word (3*k+2)]⟩
def final (n : Nat) : Configuration 2 6 :=
  ⟨5,![(n+1)+1,3*n+1],![word (n+1),word (3*n)]⟩

theorem first_step (n k : Nat) (hk : k<n) : step raw (cfg n k)=some (mid1 n k) := by
  have hm : readTapeBit (word (n+1)) (k+2)=true := RecoveryColdWidth.mark (n+1) (k+1) (by omega)
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,hm,ite_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · exact RecoveryColdWidth.write_end (3*k)

theorem second_step (n k : Nat) : step raw (mid1 n k)=some (mid2 n k) := by
  simp only [step,raw,mid1]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · exact RecoveryColdWidth.write_end (3*k+1)

theorem third_step (n k : Nat) : step raw (mid2 n k)=some (cfg n (k+1)) := by
  simp only [step,raw,mid2]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i
    · rfl
    · change 3*k+3+1=3*(k+1)+1
      omega
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (word (3*k+2)) (3*k+3) true=word (3*(k+1))
      rw [show 3*(k+1)=3*k+2+1 by omega]
      exact RecoveryColdWidth.write_end (3*k+2)

theorem end_step (n : Nat) : step raw (cfg n n)=some (final n) := by
  have he : readTapeBit (word (n+1)) (n+2)=false := RecoveryColdWidth.ending (n+1)
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,he,Bool.false_eq_true,ite_false]
  rfl

theorem loop_trace (n k remaining : Nat) (hk : k+remaining=n) :
    Timed raw (3*remaining+1) (cfg n k) (final n) := by
  induction remaining generalizing k with
  | zero=>
    have he : k=n := by omega
    subst k
    exact Timed.single (by rfl) (end_step n)
  | succ remaining ih=>
    have h := (((Timed.single (by rfl) (first_step n k (by omega))).trans
      (Timed.single (by rfl) (second_step n k))).trans
      (Timed.single (by rfl) (third_step n k))).trans (ih (k+1) (by omega))
    have he : 1+1+1+(3*remaining+1)=3*(remaining+1)+1 := by omega
    rw [he] at h
    exact h

end NearCubicWires.RepairOrdinary.RecoveryColdCap
