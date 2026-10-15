import Proof.SourceAssembly.SourceReuse

/- A paid parallel saturating rewind and erase of the disposable source bank.
The true driver and false log are retained exactly for the next request. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SourceAssemblyClear
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
noncomputable section

def join {t : Nat} {α : Type} (a : Fin t → α) (b c : α) : Fin (t+1+1) → α :=
  Fin.addCases (Fin.addCases a (fun _ : Fin 1 => b)) (fun _ : Fin 1 => c)

def driver (t : Nat) : Fin (t+1+1) := ((0 : Fin 1).natAdd t).castAdd 1
def logPort (t : Nat) : Fin (t+1+1) := (0 : Fin 1).natAdd (t+1)

def cfg {t : Nat} (q : Fin 3) (A : Fin t → List Bool) (H : Fin t → Nat)
    (C d l : Nat) (log : List Bool) : Configuration (t+1+1) 3 :=
  ⟨q,join H d l,join A (List.replicate C true) log⟩

def rewind (t : Nat) : Machine (t+1+1) 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q scan => if q.val=0 then
    some (if scan (driver t) then
      ⟨0,join (fun _ => none) none (some true),join (fun _ => .left) .right .right⟩
    else ⟨1,fun _ => none,join (fun _ => .stay) .stay .left⟩)
    else if q.val=1 then some (if scan (logPort t) then
      ⟨1,join (fun _ => none) none (some false),join (fun _ => .stay) .left .left⟩
    else ⟨2,fun _ => none,fun _ => .stay⟩) else none

theorem forward_step {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C done : Nat) (hd : done<C) :
    step (rewind t) (cfg 0 A (fun i => H i-done) C done done (List.replicate done true)) =
    some (cfg 0 A (fun i => H i-(done+1)) C (done+1) (done+1)
      (List.replicate (done+1) true)) := by
  simp [step,rewind,cfg,Configuration.scanned,driver,join,readTapeBit,List.getD,hd]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j
      · intro k; simp [join,applyAction,HeadMove.apply,Nat.sub_sub]
      · intro k; simp [join,applyAction,HeadMove.apply]
    · intro j; simp [join,applyAction,HeadMove.apply]
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;> simp [join,applyAction]
    · intro j
      simp only [join,applyAction,Fin.addCases_right]
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate done true) true

theorem bridge_step {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat) (C : Nat) :
    step (rewind t) (cfg 0 A H C C C (List.replicate C true)) =
    some (cfg 1 A H C C (C-1) (List.replicate C true)) := by
  simp [step,rewind,cfg,Configuration.scanned,driver,join,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;> simp [join,applyAction,HeadMove.apply]
    · intro j; simp [join,applyAction,HeadMove.apply]
  · rfl

theorem back_step {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C n z : Nat) :
    step (rewind t) (cfg 1 A H C (n+1) n
      (List.replicate (n+1) true++List.replicate z false)) =
    some (cfg 1 A H C n (n-1)
      (List.replicate n true++List.replicate (z+1) false)) := by
  simp [step,rewind,cfg,Configuration.scanned,logPort,join,Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;>
        simp [join,applyAction,HeadMove.apply]
    · intro j; simp [join,applyAction,HeadMove.apply]
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;> simp [join,applyAction]
    · intro j; simp [join,applyAction,Streaming.erase_counter]

theorem stop_step {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C z : Nat) :
    step (rewind t) (cfg 1 A H C 0 0 (List.replicate z false)) =
    some (cfg 2 A H C 0 0 (List.replicate z false)) := by
  simp [step,rewind,cfg,Configuration.scanned,logPort,join,Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;> simp [join,applyAction,HeadMove.apply]
    · intro j; simp [join,applyAction,HeadMove.apply]
  · rfl

theorem forward_timed {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C remaining done : Nat) (h : done+remaining=C) :
    Timed (rewind t) (remaining+1)
      (cfg 0 A (fun i => H i-done) C done done (List.replicate done true))
      (cfg 1 A (fun i => H i-C) C C (C-1) (List.replicate C true)) := by
  induction remaining generalizing done with
  | zero =>
    have he : done=C := by omega
    subst done
    exact Timed.single (by rfl) (bridge_step A _ C)
  | succ remaining ih =>
    exact Timed.step (by rfl) (forward_step A H C done (by omega))
      (ih (done+1) (by omega))

theorem back_timed {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C n z : Nat) :
    Timed (rewind t) (n+1)
      (cfg 1 A H C n (n-1) (List.replicate n true++List.replicate z false))
      (cfg 2 A H C 0 0 (List.replicate (n+z) false)) := by
  induction n generalizing z with
  | zero => simpa using Timed.single (by rfl) (stop_step A H C z)
  | succ n ih =>
    have h := Timed.step (by rfl) (back_step A H C n z) (ih (z+1))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_sub_cancel] using h

theorem raw_rewind {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C : Nat) (hH : ∀ i, H i≤C) :
    Step (rewind t) (2*C+2) (join H 0 0) (join A (List.replicate C true) [])
      (fun _ => 0) (join A (List.replicate C true) (List.replicate C false)) := by
  have hf := forward_timed A H C C 0 (by omega)
  have hb := back_timed A (fun i => H i-C) C C 0
  simp only [Nat.sub_zero,Nat.add_zero,List.replicate_zero,List.append_nil] at hf hb
  have h := hf.trans hb
  have hh : (fun i => H i-C) = fun _ => 0 := funext (fun i => Nat.sub_eq_zero_of_le (hH i))
  rw [hh,show C+1+(C+1)=2*C+2 by omega] at h
  obtain ⟨r,hr,hfinal,_⟩ := h.run (by rfl)
  refine Step.of_run hr ?_ ?_
  · rw [hfinal]
    funext i
    refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;> simp [cfg,join]
    · intro j; simp [cfg,join]
  · rw [hfinal]; rfl

theorem pad_join_log {t : Nat} (A : Fin t → List Bool) (driver log : List Bool)
    (cap : Nat) :
    (fun i => ZeroPadding.pad (join (fun _ : Fin t => 0) 0 cap i)
      (join A driver log i)) = join A driver (ZeroPadding.pad cap log) := by
  funext i
  refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j <;> intro k <;>
      simp [join,ZeroPadding.pad_zero]
  · intro j; simp [join]

theorem rewind_run {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat)
    (C : Nat) (hH : ∀ i, H i≤C) :
    Step (rewind t) (2*C+2) (join H 0 0)
      (join A (List.replicate C true) (List.replicate (C+1) false))
      (fun _ => 0) (join A (List.replicate C true) (List.replicate (C+1) false)) := by
  have h := (raw_rewind A H C hH).pad (join (fun _ : Fin t => 0) 0 (C+1))
  rw [pad_join_log,pad_join_log] at h
  have hlog : ZeroPadding.pad (C+1) (List.replicate C false) =
      List.replicate (C+1) false := by
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
    congr 1
    omega
  rw [hlog] at h
  simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using h

def machine (t : Nat) := Composition.machine (rewind t) (RecoveryScratchErase.resetMachine t)

/-- Arbitrary nonempty dirty data and nonzero heads become the SAME retained
false bank.  The fixed machine and fuel do not depend on the next request size,
and neither the driver nor its log must be reconstructed between calls. -/
theorem clear_run {t : Nat} (A : Fin t → List Bool) (H : Fin t → Nat) (C : Nat)
    (hH : ∀ i, H i≤C) (hA : ∀ i, (A i).length≤C) :
    Step (machine t) (4*C+7) (join H 0 0)
      (join A (List.replicate C true) (List.replicate (C+1) false))
      (fun _ => 0)
      (join (fun _ : Fin t => List.replicate C false)
        (List.replicate C true) (List.replicate (C+1) false)) := by
  have h1 := rewind_run A H C hH
  have h2 := Step.of_ready (RecoveryScratchErase.erase_ready C (C+1) A hA)
  have h2' : Step (RecoveryScratchErase.resetMachine t) (2*C+4) (fun _ => 0)
      (join A (List.replicate C true) (List.replicate (C+1) false))
      (fun _ => 0) (join (fun _ : Fin t => List.replicate C false)
        (List.replicate C true) (List.replicate (C+1) false)) := by
    convert h2 using 1 <;>
      (funext i; simp only [join,Nat.max_self])
  have h := h1.seq h2'
  simpa only [machine,show 2*C+2+1+(2*C+4)=4*C+7 by omega] using h

end
end SourceAssemblyClear
