import Proof.Assembly.ClosureBinaryEnumerator
import Proof.MachineModel.UInputFields

/-! The enumerator's framed binary assignment is physically read into the
raw coordinate word consumed by FrozenMask. Both source and scratch are
retained with all heads zero; the raw destination starts as K zero cells. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryEnumerator
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch CanonicalRecoveryLanguage

theorem assignment_run (K j : Nat) :
    Step Streaming.machine (4*K+2) (fun _=>0)
      ![frame (SignedSortKey.binary K j),List.replicate K false,List.replicate K false]
      (fun _=>0)
      ![frame (SignedSortKey.binary K j),List.ofFn (bitInputOfCode K j),List.replicate K false] := by
  obtain ⟨r,hr,ht,hh,_⟩ := UInputFields.unwrap_ready (List.ofFn (bitInputOfCode K j))
  have h := Step.of_run hr (funext hh) ht
  have hp := h.pad (![0,K,K] : Fin 3→Nat)
  simp only [List.length_ofFn] at hp
  have hw : List.ofFn (bitInputOfCode K j) = SignedSortKey.binary K j :=
    RepairSource.VerifierDecoding.fixedBits_binary K j
  refine (hp.congr_in rfl ?_).congr rfl ?_
  all_goals funext i; fin_cases i <;> simp [ZeroPadding.pad,hw]

theorem budget_le (K cost : Nat) : budget K cost ≤ 2^K*(cost+4*K+6) := by
  have hp := Nat.two_pow_pos K
  have he : 2^K=(2^K-1)+1 := by omega
  conv_rhs => rw [he,Nat.add_mul,Nat.one_mul]
  unfold budget
  omega

end NearCubicWires.P1Closure.BinaryEnumerator
