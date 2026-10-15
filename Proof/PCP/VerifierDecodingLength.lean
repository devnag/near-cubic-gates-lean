import Proof.PCP.VerifierDecodingPower

/-! Produce the literal code-length cap from blank workspace and restore the
source head, retaining its unary marks for subsequent dimension guards. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LengthMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 6) (sourceMove countMove : HeadMove) (write : Option Bool := none) : Action 2 6 :=
  ⟨next,![none,write],![sourceMove,countMove]⟩
def machine : Machine 2 6 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val = 5
  rule := fun state bits =>
    ![some (action 1 .stay .right (some false)),
      some (if bits 0 then action 2 .right .stay else action 3 .stay .left),
      some (action 1 .right .right (some true)),
      some (if bits 1 then action 4 .left .left else action 5 .stay .right),
      some (action 3 .left .stay),none] state

def cfg (state : Fin 6) (source : List Bool) (pos count head : ℕ) : Configuration 2 6 :=
  ⟨state,![pos,head],![source,false::List.replicate count true]⟩
@[simp] theorem cfg_cells (state : Fin 6) (source : List Bool) (pos count head : ℕ) :
    (cfg state source pos count head).tapeCells = source.length+count+1 := by
  simp [cfg, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem initialize_step (source : List Bool) :
    step machine (initialConfiguration machine ![source,[]]) = some (cfg 1 source 0 0 1) := by
  simp [step, machine, initialConfiguration]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem marker_step (pre tail : List Bool) (count : ℕ) :
    step machine (cfg 1 (pre++true::tail) pre.length count (count+1)) =
      some (cfg 2 (pre++true::tail) (pre.length+1) count (count+1)) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem payload_step (pre tail : List Bool) (bit : Bool) (count : ℕ) :
    step machine (cfg 2 (pre++bit::tail) pre.length count (count+1)) =
      some (cfg 1 (pre++bit::tail) (pre.length+1) (count+1) (count+2)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]
    have h := Streaming.write_append (false::List.replicate count true) true
    simpa only [List.replicate_add, List.replicate_one, List.length_cons,
      List.length_replicate, List.cons_append] using h

theorem scan_prefix (bits pre : List Bool) (count : ℕ) :
    let source := pre ++ frame bits
    Prefix machine (source.length+count+bits.length+1) (2*bits.length)
      (cfg 1 source pre.length count (count+1))
      (cfg 1 source (pre.length+2*bits.length) (count+bits.length) (count+bits.length+1)) := by
  induction bits generalizing pre count with
  | nil => simp; exact Prefix.refl _ (by simp)
  | cons bit bits ih =>
    let source := pre ++ frame (bit::bits)
    let space := source.length+count+(bit::bits).length+1
    have he : (pre++[true,bit]) ++ frame bits = source := by
      simp [source, RepairSource.frame, RepairOrdinary.frame, List.append_assoc]
    have ht := ih (pre++[true,bit]) (count+1)
    dsimp only at ht
    rw [he] at ht
    have htail : Prefix machine space (2*bits.length)
        (cfg 1 source (pre.length+2) (count+1) (count+2))
        (cfg 1 source (pre.length+2*(bit::bits).length) (count+(bit::bits).length)
          (count+(bit::bits).length+1)) := by
      simpa [space, List.length_append, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
    have h1 := Prefix.step (by simp [space] : (cfg 2 source (pre.length+1) count (count+1)).tapeCells ≤ space)
      (by rfl : machine.halted (2 : Fin 6) = false)
      (by simpa [source, RepairSource.frame, RepairOrdinary.frame, List.append_assoc] using
        payload_step (pre++[true]) (frame bits) bit count)
      (by simpa [source, RepairSource.frame, RepairOrdinary.frame, Nat.add_assoc] using htail)
    have h0 := Prefix.step (by simp [space] : (cfg 1 source pre.length count (count+1)).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 6) = false)
      (by simpa [source, RepairSource.frame, RepairOrdinary.frame, List.append_assoc] using
        marker_step pre (bit::frame bits) count) h1
    convert h0 using 1
    all_goals simp [RepairSource.frame, RepairOrdinary.frame, Nat.add_assoc, Nat.mul_add]

theorem bridge_step (pre : List Bool) (count : ℕ) :
    step machine (cfg 1 (pre++[false]) pre.length count (count+1)) =
      some (cfg 3 (pre++[false]) pre.length count count) := by
  have hr := Streaming.read_append pre [] false
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem rewind_first (source : List Bool) (count k : ℕ) (hk : k < count) :
    step machine (cfg 3 source (2*(k+1)) count (k+1)) =
      some (cfg 4 source (2*k+1) count k) := by
  have hr : readTapeBit (false::List.replicate count true) (k+1) = true := by
    change readTapeBit (List.replicate count true) k = true
    simp [SliceMachine.read_unary, hk]
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]; omega
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem rewind_second (source : List Bool) (count k : ℕ) :
    step machine (cfg 4 source (2*k+1) count k) = some (cfg 3 source (2*k) count k) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem rewind_stop (source : List Bool) (count : ℕ) :
    step machine (cfg 3 source 0 count 0) = some (cfg 5 source 0 count 1) := by
  simp [step, machine, cfg, Configuration.scanned, readTapeBit, List.getD]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem rewind_prefix (source : List Bool) (count k : ℕ) (hk : k ≤ count) :
    Prefix machine (source.length+count+1) (2*k+1)
      (cfg 3 source (2*k) count k) (cfg 5 source 0 count 1) := by
  induction k with
  | zero => exact Prefix.step (by simp) (by rfl) (rewind_stop source count) (Prefix.refl _ (by simp))
  | succ k ih =>
    have h1 := Prefix.step (by simp : (cfg 4 source (2*k+1) count k).tapeCells ≤ source.length+count+1)
      (by rfl : machine.halted (4 : Fin 6) = false) (rewind_second source count k) (ih (by omega))
    have h0 := Prefix.step (by simp : (cfg 3 source (2*(k+1)) count (k+1)).tapeCells ≤ source.length+count+1)
      (by rfl : machine.halted (3 : Fin 6) = false) (rewind_first source count k (by omega)) h1
    convert h0 using 1
    omega

/-- The cap comes from the literal code and initially blank workspace. -/
theorem length_run (word : List Bool) :
    ∃ receipt : ExecutionReceipt 2 6,
      run machine (4*word.length+3) ![frame word,[]] = some receipt ∧
      receipt.final = cfg 5 (frame word) 0 word.length 1 ∧
      receipt.steps = 4*word.length+3 ∧ receipt.peakTapeCells ≤ 3*word.length+2 := by
  have hp := scan_prefix word [] 0
  dsimp only at hp
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hp
  have hsource : Streaming.marks word ++ [false] = frame word := by
    have h := Streaming.frame_append word []
    simpa [RepairOrdinary.frame] using h.symm
  have hb := bridge_step (Streaming.marks word) word.length
  rw [hsource, Streaming.marks_length] at hb
  have ht := Prefix.step (by simp : (cfg 1 (frame word) (2*word.length) word.length (word.length+1)).tapeCells ≤
      (frame word).length+word.length+1)
    (by rfl : machine.halted (1 : Fin 6) = false) hb (rewind_prefix (frame word) word.length word.length (Nat.le_refl _))
  have hi := Prefix.step (by
      simp [initialConfiguration, Configuration.tapeCells, Fin.sum_univ_succ]
      omega : (initialConfiguration machine ![frame word,[]]).tapeCells ≤ (frame word).length+word.length+1)
    (by rfl : machine.halted machine.start = false) (initialize_step (frame word)) (hp.trans ht)
  obtain ⟨r,hr,hf,hs,hpeak⟩ := hi.run (by rfl) (by simp)
  refine ⟨r, ?_, hf, by omega, ?_⟩
  · have htime : 2*word.length+(2*word.length+1+1)+1 = 4*word.length+3 := by omega
    change runFrom machine (2*word.length+(2*word.length+1+1)+1) _ = some r at hr
    simpa only [run, htime] using hr
  · simp only [RepairSource.frame, RepairOrdinary.frame_length] at hpeak
    omega

end NearCubicWires.RepairSource.VerifierDecoding.LengthMachine
