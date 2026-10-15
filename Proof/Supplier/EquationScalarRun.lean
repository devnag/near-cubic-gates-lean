import Proof.Supplier.EquationScalarTail

/-! Complete cold scalar execution. No width, sign flag, counter or
workspace is provided separately from the single source field. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Graph
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def Result (negate sign : Bool) (p n m : Nat) : Prop :=
  ∃ time out,time ≤ 64*(p+1) ∧
    ReadyRun (machine negate) time (Prepare.input sign (binary p n)) out ∧
    out 0=frame (sign::binary p n) ∧
    out 9=frame (Emit.negative negate sign (DecompositionBitFields.present (binary (p+1) m))::binary (p+1) m)

theorem complete (negate sign : Bool) (p n m time : Nat) (a : Fin 12→List Bool)
    (hpre : Timed (machine negate) time (entry negate 0 (Prepare.input sign (binary p n))) (entry negate 3 a))
    (ht : time ≤ 8*p+24) (h0 : a 0=frame (sign::binary p n))
    (hmag : a 2=frame (binary (p+1) m)) (hsign : a 1=[sign])
    (h6 : a 6=[]) (h7 : a 7=[false]) (h8 : a 8=[]) (h9 : a 9=[]) (h11 : a 11=[]) :
    Result negate sign p n m := by
  have htail := tail negate a (binary (p+1) m) sign hmag hsign h6 h7 h8 h9 h11
  have h := hpre.trans htail
  rw [entry_zero,binary_length] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨time+(12*(p+1)+16),finished negate a (binary (p+1) m) sign,by omega,?_,?_,?_⟩
  · exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i; simp [hf,RecoveryCalls.stopped],hs⟩
  · rw [finished_source,h0]
  · exact finished_output _ _ _ _

theorem negate_run (sign : Bool) (p n : Nat) (hn : n<2^p) : Result true sign p n n := by
  have hprep : ReadyRun (programs true 0) (Prepare.budget (binary p n))
      (Prepare.input sign (binary p n)) (Prepare.output sign (binary p n)) := Prepare.ready _ _
  have hpre := hprep.call sizes (programs true) 0 (next true) 0 3 (by intro q; rfl)
  apply complete true sign p n n _ _ hpre
  · simp [Prepare.budget]; omega
  · rfl
  · simp [Prepare.output,widen_binary p n hn]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem positive_run (p n : Nat) (hn : n<2^p) : Result false false p n (n+1) := by
  have hn' : n+1<2^(p+1) := by rw [pow_succ]; have hp := Nat.two_pow_pos p; omega
  obtain ⟨cost,scratch,hcost,_hscratch,harith⟩ := increment_cold (p+1) n hn'
  let a := Prepare.output false (binary p n)
  let b := install incSlots a ![frame (binary (p+1) (n+1)),List.replicate scratch false]
  have hi : ReadyRun (programs false 1) cost a b := harith.focus incSlots (by decide) a (by
    intro i; fin_cases i <;> simp [a,incSlots,Prepare.output,widen_binary p n hn])
  have hprep : ReadyRun (programs false 0) (Prepare.budget (binary p n))
      (Prepare.input false (binary p n)) a := Prepare.ready _ _
  have h0 := hprep.call sizes (programs false) 0 (next false) 0 1 (by intro q; rfl)
  have h1 := hi.call sizes (programs false) 0 (next false) 1 3 (by intro q; rfl)
  apply complete false false p n (n+1) _ b (h0.trans h1)
  · simp [Prepare.budget]; omega
  all_goals simp [b,a,install,pick_inc,Prepare.output]

theorem negative_run (p n : Nat) (hn : n<2^p) (hp : 0<n) : Result false true p n (n-1) := by
  have hn' : n<2^(p+1) := by rw [pow_succ]; have hp := Nat.two_pow_pos p; omega
  let a := Prepare.output true (binary p n)
  let b := install predSlots a ![frame (binary (p+1) (n-1)),[true],List.replicate (2*(p+1)+1) false]
  have hi : ReadyRun (programs false 2) (4*(p+1)+4) a b :=
    (predecessor_cold (p+1) n hn' hp).focus predSlots (by decide) a (by
      intro i; fin_cases i <;> simp [a,predSlots,Prepare.output,widen_binary p n hn])
  have hprep : ReadyRun (programs false 0) (Prepare.budget (binary p n))
      (Prepare.input true (binary p n)) a := Prepare.ready _ _
  have h0 := hprep.call sizes (programs false) 0 (next false) 0 2 (by intro q; rfl)
  have h1 := hi.call sizes (programs false) 0 (next false) 2 3 (by intro q; rfl)
  apply complete false true p n (n-1) _ b (h0.trans h1)
  · simp [Prepare.budget]; omega
  all_goals simp [b,a,install,pick_pred,Prepare.output]

end
end NearCubicWires.RepairOrdinary.EquationScalar.Graph
