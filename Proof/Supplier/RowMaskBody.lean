import Proof.Supplier.RowMaskBodyParts

/-! The mask bit itself controls whether its index is emitted. The common
tail advances the index and source and counts only selected occurrences. -/
namespace NearCubicWires.RepairOrdinary.RowMaskBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskBodyParts Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 4 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
def sizes : Fin 3→ℕ := ![1,5,11]
noncomputable def programs : (i : Fin 3)→Machine 4 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>appendMachine
  | ⟨2,_⟩=>tailMachine
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 4→Bool) : Option (Fin 3) :=
  ![some (if bits 0 then 1 else 2),some 2,none] i
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (i : Fin 3) (source : List Bool) (pos j count : ℕ) (out : List Bool) :=
  controlConfig (RecoveryCalls.code sizes i) (cfg (programs i).start source pos j count out)
noncomputable def finished (source : List Bool) (pos j count : ℕ) (out : List Bool) :=
  RecoveryCalls.stopped sizes (cfg idle.start source pos j count out).heads (cfg idle.start source pos j count out).tapes

theorem entry_eq (source : List Bool) (pos j count : ℕ) (out : List Bool) :
    boundary 0 source pos j count out=cfg machine.start source pos j count out := by
  apply configuration_ext
  · rfl
  · rfl
  · rfl

theorem probe (pre tail : List Bool) (bit : Bool) (j count : ℕ) (out : List Bool) :
    Timed machine 1 (boundary 0 (pre++bit::tail) pre.length j count out)
      (boundary (if bit then 1 else 2) (pre++bit::tail) pre.length j count out) := by
  have hn : next 0 (programs 0).start (cfg (programs 0).start (pre++bit::tail) pre.length j count out).scanned=
      some (if bit then 1 else 2) := by simp [next,cfg,Configuration.scanned,read_append]
  have he := RecoveryCalls.return_step sizes programs 0 next 0 (if bit then 1 else 2)
    (cfg (programs 0).start (pre++bit::tail) pre.length j count out) (by rfl) hn
  exact Timed.single (by simp [machine,boundary,RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he

theorem append_call (source : List Bool) (pos j count : ℕ) (out : List Bool) :
    Timed machine (2*j+5) (boundary 1 source pos j count out)
      (boundary 2 source pos j count (out++RowIndexField.word j)) := by
  obtain ⟨r,hr,rf,rs⟩ := RowMaskBodyParts.append_run source pos j count out
  obtain ⟨hp,hh⟩ := prefix_of_run appendMachine (2*j+4) _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next 1 ⟨r.peakTapeCells,hp⟩
  rw [rs] at hb
  have he := RecoveryCalls.return_step sizes programs 0 next 1 2 r.final hh (by rfl)
  rw [rf] at he hb
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  simpa only [show 2*j+4+1=2*j+5 by omega,machine,boundary,controlConfig,cfg,
    RecoveryCalls.restarted,programs] using h

theorem tail_stop (pre tail : List Bool) (bit : Bool) (j count : ℕ) (out : List Bool) :
    Timed machine (2*j+12) (boundary 2 (pre++bit::tail) pre.length j count out)
      (finished (pre++bit::tail) (pre.length+1) (j+1) (count+bit.toNat) out) := by
  obtain ⟨r,hr,rh,rt,rs⟩ := RowMaskBodyParts.tail_run pre tail bit j count out
  obtain ⟨hp,hh⟩ := prefix_of_run tailMachine (2*j+11) _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next 2 ⟨r.peakTapeCells,hp⟩
  rw [rs] at hb
  have he := RecoveryCalls.stop_step sizes programs 0 next 2 r.final hh (by rfl)
  rw [rh,rt] at he
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  simpa only [show 2*j+11+1=2*j+12 by omega,machine,boundary,finished,controlConfig,cfg,
    RecoveryCalls.restarted,programs] using h

def emitted (bit : Bool) (j : ℕ) : List Bool := if bit then RowIndexField.word j else []

theorem body_timed (pre tail : List Bool) (bit : Bool) (j count : ℕ) (out : List Bool) :
    ∃ n,n≤4*j+18 ∧ Timed machine n (cfg machine.start (pre++bit::tail) pre.length j count out)
      (finished (pre++bit::tail) (pre.length+1) (j+1) (count+bit.toNat) (out++emitted bit j)) := by
  have hp := probe pre tail bit j count out
  rw [entry_eq] at hp
  cases bit with
  | false =>
    have h := hp.trans (tail_stop pre tail false j count out)
    refine ⟨1+(2*j+12),by omega,?_⟩
    simpa only [Bool.false_eq_true,↓reduceIte,emitted,List.append_nil] using h
  | true =>
    have h := (hp.trans (append_call (pre++true::tail) pre.length j count out)).trans
      (tail_stop pre tail true j count (out++RowIndexField.word j))
    refine ⟨1+(2*j+5)+(2*j+12),by omega,?_⟩
    simpa only [↓reduceIte,emitted] using h

theorem body_run (pre tail : List Bool) (bit : Bool) (j count : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (4*j+18) (cfg machine.start (pre++bit::tail) pre.length j count out)=some r ∧
      r.final.heads=(cfg machine.start (pre++bit::tail) (pre.length+1) (j+1)
        (count+bit.toNat) (out++emitted bit j)).heads ∧
      r.final.tapes=(cfg machine.start (pre++bit::tail) (pre.length+1) (j+1)
        (count+bit.toNat) (out++emitted bit j)).tapes ∧ r.steps≤4*j+18 := by
  obtain ⟨n,hn,h⟩ := body_timed pre tail bit j count out
  obtain ⟨r,hr,rf,rs⟩ := h.run (by simp [machine,finished,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine n (4*j+18-n) _ r hr
  rw [Nat.add_sub_of_le hn] at more
  refine ⟨r,more,?_,?_,rs.le.trans hn⟩
  · rw [rf]; rfl
  · rw [rf]; rfl

end NearCubicWires.RepairOrdinary.RowMaskBody
