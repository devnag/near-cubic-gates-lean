import Proof.PCP.VerifierDecodingRangeLayout

/-! One finite decoder subprogram reads and validates a state-index field.
Its boolean result is produced by actual tape transitions. Every call return
is paid, and truncated fields stop before invoking binary comparison. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flipProgram : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val = 1
  rule := fun q bits => if q.val = 0 then
    some ⟨1,![none,none,none,none,some (!(bits 4)),none],fun _ => .stay⟩ else none

def flipInput (source bits bound : List Bool) (pos capacity : ℕ) : Configuration 6 2 :=
  ⟨0,heads pos,store source (frame bits) bound bits.length (max capacity (2*bits.length+1))
    (decide (value bound ≤ value bits))⟩
def flipOutput (source bits bound : List Bool) (pos capacity : ℕ) : Configuration 6 2 :=
  ⟨1,heads pos,store source (frame bits) bound bits.length (max capacity (2*bits.length+1))
    (decide (value bits < value bound))⟩

theorem flip_step (source bits bound : List Bool) (pos capacity : ℕ) :
    step flipProgram (flipInput source bits bound pos capacity) = some (flipOutput source bits bound pos capacity) := by
  have h : decide (value bound ≤ value bits) = !(decide (value bits < value bound)) := by
    by_cases hle : value bound ≤ value bits
    · simp [hle,Nat.not_lt.mpr hle]
    · simp [hle,Nat.lt_of_not_ge hle]
  simp [step,flipProgram,flipInput,Configuration.scanned,store,heads,readTapeBit]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,flipOutput,heads]
  · funext i; fin_cases i <;> simp [applyAction,flipOutput,store,writeTapeBit,h]

theorem flip_run (source bits bound : List Bool) (pos capacity : ℕ) :
    ∃ receipt : ExecutionReceipt 6 2,
      runFrom flipProgram 1 (flipInput source bits bound pos capacity) = some receipt ∧
      receipt.final = flipOutput source bits bound pos capacity ∧ receipt.steps = 1 := by
  have hp := Timed.single (by rfl : flipProgram.halted (0 : Fin 2) = false) (flip_step source bits bound pos capacity)
  exact hp.run (by rfl)

def sizes : Fin 3 → ℕ := ![6,7,2]
def programs : (j : Fin 3) → Machine 6 (sizes j)
  | ⟨0,_⟩ => fieldProgram
  | ⟨1,_⟩ => compareProgram
  | ⟨2,_⟩ => flipProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (j : Fin 3) (state : Fin (sizes j)) (_ : Fin 6 → Bool) : Option (Fin 3) :=
  if j.val = 0 then if state.val = 4 then some 1 else none
  else if j.val = 1 then some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

private theorem call (j l : Fin 3) (time : ℕ) (c : Configuration 6 (sizes j))
    (d : Configuration 6 (sizes l)) (q : Fin (sizes j))
    (h : ∃ receipt, runFrom (programs j) time c = some receipt ∧
      receipt.final = ⟨q,d.heads,d.tapes⟩ ∧ receipt.steps = time)
    (hd : d.control = (programs l).start) (hn : ∀ bits, next j q bits = some l) :
    Timed machine (time+1) (controlConfig (RecoveryCalls.code sizes j) c)
      (controlConfig (RecoveryCalls.code sizes l) d) := by
  obtain ⟨r,hr,hf,hs⟩ := h
  have hp := prefix_of_run (programs j) time c r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp.1⟩
  rw [hs] at hb
  have ht := RecoveryCalls.return_step sizes programs 0 next j l r.final hp.2 (by rw [hf]; exact hn _)
  have he : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes = d := by
    apply configuration_ext
    · exact hd.symm
    · simp [RecoveryCalls.restarted,hf]
    · simp [RecoveryCalls.restarted,hf]
  rw [he] at ht
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) ht)

private theorem stop (j : Fin 3) (time : ℕ) (c d : Configuration 6 (sizes j))
    (h : ∃ receipt, runFrom (programs j) time c = some receipt ∧ receipt.final = d ∧ receipt.steps = time)
    (hn : ∀ bits, next j d.control bits = none) :
    Timed machine (time+1) (controlConfig (RecoveryCalls.code sizes j) c)
      (RecoveryCalls.stopped sizes d.heads d.tapes) := by
  obtain ⟨r,hr,hf,hs⟩ := h
  have hp := prefix_of_run (programs j) time c r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp.1⟩
  rw [hs] at hb
  have ht := RecoveryCalls.stop_step sizes programs 0 next j r.final hp.2 (by rw [hf]; exact hn _)
  rw [hf] at ht hb
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) ht)

/-- Exact enclosed state-index test. The source and width tapes are retained;
the comparison's scratch tape and every call-return transition are charged. -/
theorem range_run (pre bits tail backing bound : List Bool) (capacity : ℕ)
    (hb : backing.length ≤ 2*bits.length+1) (hw : bound.length = bits.length) :
    let source := pre++Streaming.marks bits++tail
    ∃ receipt,
      runFrom machine (8*bits.length+10)
        (controlConfig (RecoveryCalls.code sizes 0) (fieldInput source backing bound pre.length bits.length capacity)) = some receipt ∧
      receipt.final = RecoveryCalls.stopped sizes (heads (pre.length+2*bits.length))
        (store source (frame bits) bound bits.length (max capacity (2*bits.length+1))
          (decide (value bits < value bound))) ∧ receipt.steps = 8*bits.length+10 := by
  dsimp only
  let source := pre++Streaming.marks bits++tail
  let pos := pre.length+2*bits.length
  have h0 := call 0 1 (4*bits.length+2) (fieldInput source backing bound pre.length bits.length capacity)
    (compareInput source bits bound pos capacity) (4 : Fin 6) (field_layout pre bits tail backing bound capacity hb)
    rfl (by intro b; rfl)
  have hc := compare_layout source bits bound pos capacity hw
  have h1 := call 1 2 (4*bits.length+4) (compareInput source bits bound pos capacity)
    (flipInput source bits bound pos capacity) (6 : Fin 7)
    (by
      obtain ⟨r,hr,hf,hs⟩ := hc
      refine ⟨r,hr,?_,hs⟩
      rw [hf]
      rfl) rfl (by intro b; rfl)
  have h2 := stop 2 1 (flipInput source bits bound pos capacity) (flipOutput source bits bound pos capacity)
    (flip_run source bits bound pos capacity) (by intro b; rfl)
  have hp := h0.trans (h1.trans h2)
  have he : (4*bits.length+2+1)+(4*bits.length+4+1+(1+1)) = 8*bits.length+10 := by omega
  rw [he] at hp
  exact hp.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])

end NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
