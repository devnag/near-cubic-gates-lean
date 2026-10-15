import Proof.PCP.VerifierDecodingPreparation

/-! Turn a paid unary dimension into a framed word for the shared physical
length-to-binary counter. Both cursors are restored by an actual return scan. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.UnaryFrameMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 5) (sm om : HeadMove) (write : Option Bool := none) : Action 2 5 :=
  ⟨next,![none,write],![sm,om]⟩
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val = 4
  rule := fun state bits =>
    ![some (if bits 0 then action 1 .stay .right (some true) else action 2 .left .stay (some false)),
      some (action 0 .right .right (some true)),
      some (if bits 0 then action 3 .left .left else action 4 .right .stay),
      some (action 2 .stay .left),none] state

def cfg (state : Fin 5) (n sh oh : ℕ) (out : List Bool) : Configuration 2 5 :=
  ⟨state,![sh,oh],![CompareMachine.word n,out]⟩
@[simp] theorem cfg_cells (state : Fin 5) (n sh oh : ℕ) (out : List Bool) :
    (cfg state n sh oh out).tapeCells = n+1+out.length := by
  simp [cfg, CompareMachine.word,Configuration.tapeCells,Fin.sum_univ_succ]

theorem mark_step (n pos : ℕ) (pre : List Bool) (hp : pos < n) :
    step machine (cfg 0 n (pos+1) pre.length pre) =
      some (cfg 1 n (pos+1) (pre.length+1) (pre++[true])) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.read_mark,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

theorem payload_step (n pos : ℕ) (pre : List Bool) :
    step machine (cfg 1 n (pos+1) pre.length pre) =
      some (cfg 0 n (pos+2) (pre.length+1) (pre++[true])) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

theorem write_prefix (k n pos : ℕ) (pre : List Bool) (hk : pos+k ≤ n) :
    Prefix machine (n+1+pre.length+2*k+1) (2*k)
      (cfg 0 n (pos+1) pre.length pre)
      (cfg 0 n (pos+k+1) (pre.length+2*k) (pre++List.replicate (2*k) true)) := by
  induction k generalizing pos pre with
  | zero => simp; exact Prefix.refl _ (by simp)
  | succ k ih =>
    have hp := ih (pos+1) (pre++[true,true]) (by omega)
    simp only [List.length_append,List.length_cons,List.length_nil] at hp
    have hspace : n+1+(pre.length+2)+2*k+1 = n+1+pre.length+2*(k+1)+1 := by omega
    rw [hspace] at hp
    have ht : Prefix machine (n+1+pre.length+2*(k+1)+1) (2*k)
        (cfg 0 n (pos+2) (pre.length+2) (pre++[true,true]))
        (cfg 0 n (pos+(k+1)+1) (pre.length+2*(k+1)) (pre++List.replicate (2*(k+1)) true)) := by
      have he : 2*(k+1)=2+2*k := by omega
      simpa [he,List.replicate_add,List.replicate_succ,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp
    have h1 := Prefix.step (by simp; omega :
        (cfg 1 n (pos+1) (pre.length+1) (pre++[true])).tapeCells ≤ n+1+pre.length+2*(k+1)+1)
      (by rfl : machine.halted (1 : Fin 5) = false)
      (by simpa [List.append_assoc] using payload_step n pos (pre++[true])) ht
    have h0 := Prefix.step (by simp; omega :
        (cfg 0 n (pos+1) pre.length pre).tapeCells ≤ n+1+pre.length+2*(k+1)+1)
      (by rfl : machine.halted (0 : Fin 5) = false) (mark_step n pos pre (by omega)) h1
    convert h0 using 1
    omega

theorem frame_true (n : ℕ) : frame (List.replicate n true) = List.replicate (2*n) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : 2*(n+1)=2+2*n := by omega
    simpa [List.replicate_succ,RepairSource.frame,RepairOrdinary.frame,he,List.replicate_add] using
      congrArg (fun tail : List Bool => true::true::tail) ih

theorem bridge_step (n : ℕ) (pre : List Bool) :
    step machine (cfg 0 n (n+1) pre.length pre) = some (cfg 2 n n pre.length (pre++[false])) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

theorem rewind_first (n k : ℕ) (out : List Bool) (hk : k < n) :
    step machine (cfg 2 n (k+1) (2*(k+1)) out) = some (cfg 3 n k (2*k+1) out) := by
  simp [step,machine,cfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]; omega
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_second (n k : ℕ) (out : List Bool) :
    step machine (cfg 3 n k (2*k+1) out) = some (cfg 2 n k (2*k) out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_stop (n : ℕ) (out : List Bool) :
    step machine (cfg 2 n 0 0 out) = some (cfg 4 n 1 0 out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_prefix (n k : ℕ) (out : List Bool) (hk : k ≤ n) :
    Prefix machine (n+1+out.length) (2*k+1) (cfg 2 n k (2*k) out) (cfg 4 n 1 0 out) := by
  induction k with
  | zero => exact Prefix.step (by simp) (by rfl) (rewind_stop n out) (Prefix.refl _ (by simp))
  | succ k ih =>
    have hp := Prefix.step (by simp) (by rfl) (rewind_second n k out) (ih (by omega))
    have h := Prefix.step (by simp) (by rfl) (rewind_first n k out (by omega)) hp
    convert h using 1
    omega

/-- Output allocation and both cursor returns are executed. -/
theorem unary_frame_run (n : ℕ) :
    ∃ receipt : ExecutionReceipt 2 5,
      runFrom machine (4*n+2) (cfg 0 n 1 0 []) = some receipt ∧
      receipt.final = cfg 4 n 1 0 (frame (List.replicate n true)) ∧
      receipt.steps = 4*n+2 ∧ receipt.peakTapeCells ≤ 3*n+2 := by
  have hp := write_prefix n n 0 [] (by omega)
  simp only [List.length_nil,List.nil_append,Nat.zero_add] at hp
  have hb := bridge_step n (List.replicate (2*n) true)
  simp only [List.length_replicate] at hb
  rw [←frame_true] at hb
  have ht := rewind_prefix n n (frame (List.replicate n true)) (Nat.le_refl _)
  have hspace : n+1+(frame (List.replicate n true)).length = n+1+0+2*n+1 := by
    simp [RepairSource.frame,RepairOrdinary.frame_length]
    omega
  rw [hspace] at ht
  have hj := Prefix.step (by simp) (by rfl) hb ht
  obtain ⟨r,hr,hf,hs,hpeak⟩ := (hp.trans hj).run (by rfl) (by
    simp [RepairSource.frame,RepairOrdinary.frame_length]; omega)
  refine ⟨r,?_,hf,by omega,by omega⟩
  have he : 2*n+(2*n+1+1)=4*n+2 := by omega
  simpa only [he] using hr

end NearCubicWires.RepairSource.VerifierDecoding.UnaryFrameMachine
