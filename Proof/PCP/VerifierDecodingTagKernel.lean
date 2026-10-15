import Proof.PCP.VerifierDecodingTableBoundEntry

/-! A fixed four-payload-bit reader for one literal write/move tag pair.
The partial word is held in finite control (145 states), never in an
unbounded scalar. A missing frame marker rejects immediately. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TagMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Word := Fin 4 → Bool
abbrev Control := Option (Fin 9 × Word)
noncomputable def code : Control ≃ Fin (Fintype.card Control) := Fintype.equivFin _
def received (bits : Word) (count : ℕ) : Word := fun i => if i.val < count then bits i else false
noncomputable def cfg (phase : Fin 9) (bits : Word) (source : List Bool) (pos : ℕ) :
    Configuration 1 (Fintype.card Control) := ⟨code (some (phase,bits)),fun _ => pos,fun _ => source⟩
noncomputable def rejected (source : List Bool) (pos : ℕ) : Configuration 1 (Fintype.card Control) :=
  ⟨code none,fun _ => pos,fun _ => source⟩

noncomputable def machine (limit : Fin 5) : Machine 1 (Fintype.card Control) where
  descriptionBits := 0
  start := code (some (0,fun _ => false))
  halted := fun state => match code.symm state with
    | none => true
    | some (phase,_) => decide (phase.val = 2*limit.val)
  rule := fun state scanned => match code.symm state with
    | none => none
    | some (phase,bits) =>
      if h : phase.val < 2*limit.val then
        let nextPhase : Fin 9 := ⟨phase.val+1,by omega⟩
        let next := if phase.val % 2 = 0 then
            if scanned 0 then some (nextPhase,bits) else none
          else some (nextPhase,Function.update bits ⟨phase.val/2,by omega⟩ (scanned 0))
        some ⟨code next,fun _ => none,fun _ => .right⟩
      else none

@[simp] theorem cfg_cells (phase : Fin 9) (bits : Word) (source : List Bool) (pos : ℕ) :
    (cfg phase bits source pos).tapeCells = source.length := by
  simp [cfg,Configuration.tapeCells]
@[simp] theorem rejected_cells (source : List Bool) (pos : ℕ) :
    (rejected source pos).tapeCells = source.length := by
  simp [rejected,Configuration.tapeCells]

theorem received_zero (bits : Word) : received bits 0 = fun _ => false := by funext i; simp [received]
theorem received_four (bits : Word) : received bits 4 = bits := by funext i; simp [received]
theorem received_succ (bits : Word) (k : ℕ) (hk : k < 4) :
    Function.update (received bits k) ⟨k,hk⟩ (bits ⟨k,by omega⟩) = received bits (k+1) := by
  funext i
  by_cases hi : i = (⟨k,hk⟩ : Fin 4)
  · subst i; simp [received]
  · have hi' : i.val ≠ k := by intro h; apply hi; exact Fin.ext h
    have hlt : (i.val < k) ↔ (i.val < k+1) := by omega
    simp only [Function.update_of_ne hi,received,hlt]

theorem marker_step (pre tail : List Bool) (bits : Word) (k : ℕ) (limit : Fin 5) (hk : k < limit.val) :
    step (machine limit) (cfg ⟨2*k,by omega⟩ bits (pre++true::tail) pre.length) =
      some (cfg ⟨2*k+1,by omega⟩ bits (pre++true::tail) (pre.length+1)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append,show 2*k < 2*limit.val by omega]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · rfl

theorem payload_step (pre tail : List Bool) (bits : Word) (k : ℕ) (limit : Fin 5) (hk : k < limit.val) (bit : Bool) :
    step (machine limit) (cfg ⟨2*k+1,by omega⟩ bits (pre++bit::tail) pre.length) =
      some (cfg ⟨2*(k+1),by omega⟩ (Function.update bits ⟨k,by omega⟩ bit) (pre++bit::tail) (pre.length+1)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append,show 2*k+1 < 2*limit.val by omega]
  apply configuration_ext
  · have hp : (⟨2*k+1+1,by omega⟩ : Fin 9) = ⟨2*(k+1),by omega⟩ := by
      apply Fin.ext
      change 2*k+1+1 = 2*(k+1)
      omega
    have hi : (⟨(2*k+1)/2,by omega⟩ : Fin 4) = ⟨k,by omega⟩ := by
      apply Fin.ext
      change (2*k+1)/2=k
      omega
    simp only [applyAction,hp,hi]
  · funext i; simp [applyAction,HeadMove.apply]
  · rfl

theorem missing_step (pre : List Bool) (bits : Word) (k : ℕ) (limit : Fin 5) (hk : k < limit.val) :
    step (machine limit) (cfg ⟨2*k,by omega⟩ bits (pre++[false]) pre.length) =
      some (rejected (pre++[false]) (pre.length+1)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append,show 2*k < 2*limit.val by omega]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply,rejected]
  · rfl

/-- One actual two-transition framed payload read, retaining the source. -/
theorem bit_prefix (pre tail : List Bool) (bits : Word) (k : ℕ) (limit : Fin 5) (hk : k < limit.val) :
    let source := pre++true::bits ⟨k,by omega⟩::tail
    Prefix (machine limit) source.length 2
      (cfg ⟨2*k,by omega⟩ (received bits k) source pre.length)
      (cfg ⟨2*(k+1),by omega⟩ (received bits (k+1)) source (pre.length+2)) := by
  dsimp only
  have hm := marker_step pre (bits ⟨k,by omega⟩::tail) (received bits k) k limit hk
  have hb := payload_step (pre++[true]) tail (received bits k) k limit hk (bits ⟨k,by omega⟩)
  rw [received_succ bits k (by omega)] at hb
  simp only [List.length_append,List.length_cons,List.length_nil,List.append_assoc,List.cons_append,List.nil_append] at hb
  have h1 : Prefix (machine limit) (pre++true::bits ⟨k,by omega⟩::tail).length 1
      (cfg ⟨2*k+1,by omega⟩ (received bits k) (pre++true::bits ⟨k,by omega⟩::tail) (pre.length+1))
      (cfg ⟨2*(k+1),by omega⟩ (received bits (k+1)) (pre++true::bits ⟨k,by omega⟩::tail) (pre.length+2)) :=
    Prefix.step (by simp) (by simp [machine,cfg]; omega) hb (Prefix.refl _ (by simp))
  have h0 := Prefix.step (by simp) (by simp [machine,cfg]; omega) hm h1
  simpa only [Nat.add_assoc] using h0

end NearCubicWires.RepairSource.VerifierDecoding.TagMachine
