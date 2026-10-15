import Proof.Supplier.EquationWidenLoop

/-! Physical zero scalar emission for the odd right coordinate. The actual
bit-count driver is retained and rewound, and the destination stays at its
global append cursor. No false payload bit is removed as backing storage. -/
namespace NearCubicWires.RepairOrdinary.EquationZeroField
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bs =>
    if q.val=0 then some
      (if bs 0 then ⟨1,![none,some true],![.stay,.right]⟩
      else ⟨2,![none,some false],![.left,.right]⟩)
    else if q.val=1 then some ⟨0,![none,some false],![.right,.right]⟩
    else if q.val=2 then some
      (if bs 0 then ⟨2,fun _ => none,![.left,.stay]⟩
      else ⟨3,fun _ => none,![.right,.stay]⟩)
    else none

def cfg (q : Fin 4) (n pos : ℕ) (out : List Bool) : Configuration 2 4 :=
  ⟨q,![pos,out.length],![CompareMachine.word n,out]⟩

theorem marker (n pos : ℕ) (out : List Bool) (hp : pos<n) :
    step machine (cfg 0 n (pos+1) out)=
      some (cfg 1 n (pos+1) (out++[true])) := by
  simp [step,machine,cfg,Configuration.scanned,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem data (n pos : ℕ) (out : List Bool) :
    step machine (cfg 1 n pos out)=some (cfg 0 n (pos+1) (out++[false])) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem delimiter (n : ℕ) (out : List Bool) :
    step machine (cfg 0 n (n+1) out)=some (cfg 2 n n (out++[false])) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem retreat (n pos : ℕ) (out : List Bool) (hp : pos<n) :
    step machine (cfg 2 n (pos+1) out)=some (cfg 2 n pos out) := by
  simp [step,machine,cfg,Configuration.scanned,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop (n : ℕ) (out : List Bool) :
    step machine (cfg 2 n 0 out)=some (cfg 3 n 1 out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem rewind (n pos : ℕ) (out : List Bool) (hp : pos≤n) :
    Timed machine (pos+1) (cfg 2 n pos out) (cfg 3 n 1 out) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (stop n out)
  | succ pos ih =>
    have h := (Timed.single (by rfl) (retreat n pos out (by omega))).trans (ih (by omega))
    simpa only [Nat.add_comm 1 (pos+1)] using h

theorem remaining (n rem pos : ℕ) (out : List Bool) (hn : pos+rem=n) :
    Timed machine (2*rem+n+2) (cfg 0 n (pos+1) out)
      (cfg 3 n 1 (out++frame (List.replicate rem false))) := by
  induction rem generalizing pos out with
  | zero =>
    have he : pos=n := by omega
    subst pos
    have h := (Timed.single (by rfl) (delimiter n out)).trans (rewind n n (out++[false]) (by omega))
    simpa [frame,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
  | succ rem ih =>
    have h0 := Timed.single (by rfl) (marker n pos out (by omega))
    have h1 := Timed.single (by rfl) (data n (pos+1) (out++[true]))
    have ht := ih (pos+1) ((out++[true])++[false]) (by omega)
    have h := (h0.trans h1).trans ht
    simpa [frame,List.replicate_succ,List.append_assoc,Nat.mul_add,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem field_run (n : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (3*n+2) (cfg 0 n 1 out)=some r ∧
      r.final=cfg 3 n 1 (out++frame (List.replicate n false)) ∧ r.steps=3*n+2 := by
  have h := remaining n n 0 out (by omega)
  have he : 2*n+n+2=3*n+2 := by omega
  simp only [he,Nat.zero_add] at h
  exact h.run (by rfl)

theorem binary_zero (p : ℕ) : SignedSortKey.binary p 0=List.replicate p false := by
  induction p with
  | zero => rfl
  | succ p ih => simpa [SignedSortKey.binary,List.replicate_succ] using congrArg (List.cons false) ih

theorem scalar_run (p : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (3*p+8) (cfg 0 (p+2) 1 out)=some r ∧
      r.final=cfg 3 (p+2) 1 (out++frame (MatrixScoreBatch.signMagnitude (p+1) 0)) ∧
      r.steps=3*p+8 := by
  have h := field_run (p+2) out
  have he : MatrixScoreBatch.signMagnitude (p+1) 0=List.replicate (p+2) false := by
    simp [MatrixScoreBatch.signMagnitude,binary_zero,List.replicate_succ]
  rw [←he] at h
  simpa [Nat.mul_add,Nat.add_assoc] using h

end NearCubicWires.RepairOrdinary.EquationZeroField
