import SourceAdapters.Machine.CappedPrepared

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: the serialized cap request is unpacked
by a finite local machine. Tape 1 receives frame(word), tape 2 receives
the unary cap, and tape 3 receives the initial true status. -/
namespace NearCubicGates.Adapters.Machine.Capped.RequestLoader
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open Streaming (marks marks_length marks_append frame_append read_append write_append)
set_option autoImplicit false

def action (q : Fin 6) (im om cm : HeadMove) (ob cb sb : Option Bool) : Action 4 6 where
  nextControl := q
  write := fun i => if i.val=0 then none else if i.val=1 then ob else if i.val=2 then cb else sb
  move := fun i => if i.val=0 then im else if i.val=1 then om else if i.val=2 then cm else .stay

def machine : Machine 4 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==5
  rule := fun q scan =>
    if q.val=0 then some (action 1 .stay .stay .stay none none (some true))
    else if q.val=1 then
      if scan 0 then some (action 2 .right .stay .stay none none none)
      else some (action 3 .right .stay .stay none none none)
    else if q.val=2 then some (action 1 .right .stay .right none (some true) none)
    else if q.val=3 then
      if scan 0 then some (action 4 .right .right .stay (some true) none none)
      else some (action 5 .stay .stay .stay (some false) none none)
    else if q.val=4 then some (action 3 .right .right .stay (some (scan 0)) none none)
    else none

def config (q : Fin 6) (input : List Bool) (ih : ℕ) (output : List Bool)
    (oh : ℕ) (clock : List Bool) (ch : ℕ) (status : List Bool) : Configuration 4 6 where
  control := q
  heads := fun i => if i.val=0 then ih else if i.val=1 then oh else if i.val=2 then ch else 0
  tapes := fun i => if i.val=0 then input else if i.val=1 then output else if i.val=2 then clock else status

def wordConfig (pref pre bs : List Bool) (cap : ℕ) : Configuration 4 6 :=
  config 3 (pref ++ marks pre ++ frame bs) (pref.length+2*pre.length)
    (marks pre) (2*pre.length) (List.replicate cap true) cap [true]

def wordBitConfig (pref pre : List Bool) (b : Bool) (bs : List Bool) (cap : ℕ) : Configuration 4 6 :=
  config 4 (pref ++ marks pre ++ frame (b::bs)) (pref.length+2*pre.length+1)
    (marks pre ++ [true]) (2*pre.length+1) (List.replicate cap true) cap [true]

def finished (input output : List Bool) (cap : ℕ) : Configuration 4 6 :=
  config 5 input (input.length-1) output (output.length-1) (List.replicate cap true) cap [true]

theorem word_mark_step (pref pre : List Bool) (b : Bool) (bs : List Bool) (cap : ℕ) :
    step machine (wordConfig pref pre (b::bs) cap) =
      some (wordBitConfig pref pre b bs cap) := by
  have hr : readTapeBit (pref ++ marks pre ++ frame (b::bs)) (pref.length+2*pre.length) = true := by
    simpa [frame] using read_append (pref ++ marks pre) (b::frame bs) true
  have hs : (wordConfig pref pre (b::bs) cap).scanned 0 = true := hr
  have hRule : machine.rule (wordConfig pref pre (b::bs) cap).control
      (wordConfig pref pre (b::bs) cap).scanned =
      some (action 4 .right .right .stay (some true) none none) := by
    change (if (wordConfig pref pre (b::bs) cap).scanned 0 then _ else _) = _
    rw [hs]
    rfl
  rw [step, hRule]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, wordConfig, wordBitConfig, config, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, wordConfig, wordBitConfig, config, ← marks_length, write_append]

theorem word_bit_step (pref pre : List Bool) (b : Bool) (bs : List Bool) (cap : ℕ) :
    step machine (wordBitConfig pref pre b bs cap) =
      some (wordConfig pref (pre++[b]) bs cap) := by
  have hr : readTapeBit (pref ++ marks pre ++ frame (b::bs)) (pref.length+2*pre.length+1) = b := by
    simpa [frame, List.append_assoc, Nat.add_assoc] using read_append ((pref ++ marks pre) ++ [true]) (frame bs) b
  have hs : (wordBitConfig pref pre b bs cap).scanned 0 = b := hr
  have hRule : machine.rule (wordBitConfig pref pre b bs cap).control
      (wordBitConfig pref pre b bs cap).scanned =
      some (action 3 .right .right .stay (some b) none none) := by
    change some (action 3 .right .right .stay (some ((wordBitConfig pref pre b bs cap).scanned 0)) none none) = _
    rw [hs]
  rw [step, hRule]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, wordBitConfig, wordConfig, config, HeadMove.apply] <;> omega
  · funext i; fin_cases i <;>
      simp [applyAction, action, wordBitConfig, wordConfig, config, marks, frame, List.append_assoc]
    have hw := write_append (marks pre ++ [true]) b
    simpa [marks, List.append_assoc, Nat.mul_comm] using hw

theorem word_end_step (pref pre : List Bool) (cap : ℕ) :
    step machine (wordConfig pref pre [] cap) =
      some (finished (pref ++ marks pre ++ frame []) (frame pre) cap) := by
  have hr : readTapeBit (pref ++ marks pre ++ frame []) (pref.length+2*pre.length) = false := by
    simpa [frame] using read_append (pref ++ marks pre) [] false
  have hs : (wordConfig pref pre [] cap).scanned 0 = false := hr
  have hRule : machine.rule (wordConfig pref pre [] cap).control
      (wordConfig pref pre [] cap).scanned =
      some (action 5 .stay .stay .stay (some false) none none) := by
    change (if (wordConfig pref pre [] cap).scanned 0 then _ else _) = _
    rw [hs]
    rfl
  rw [step, hRule]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, wordConfig, finished, config, HeadMove.apply, frame_length]
  · funext i; fin_cases i <;> simp [applyAction, action, wordConfig, finished, config, ← marks_length, write_append]
    simpa [frame] using (frame_append pre []).symm

theorem word_run (pref pre bs : List Bool) (cap : ℕ) :
    ∃ r, runFrom machine (2*bs.length+1) (wordConfig pref pre bs cap) = some r ∧
      r.final = finished (pref ++ marks pre ++ frame bs) (frame (pre++bs)) cap ∧
      r.steps = 2*bs.length+1 := by
  induction bs generalizing pre with
  | nil =>
    let f := finished (pref ++ marks pre ++ frame []) (frame pre) cap
    let r : ExecutionReceipt 4 6 := ⟨f, 0, f.tapeCells⟩
    have hhalt : runFrom machine 0 f = some r := by rfl
    have h := runFrom_step machine (wordConfig pref pre [] cap) f r
      (by rfl) (word_end_step pref pre cap) hhalt
    exact ⟨_, h, by simp [r, f], rfl⟩
  | cons b bs ih =>
    obtain ⟨r, hr, hf, hs⟩ := ih (pre++[b])
    have h2 := runFrom_step machine (wordBitConfig pref pre b bs cap)
      (wordConfig pref (pre++[b]) bs cap) r (by rfl) (word_bit_step pref pre b bs cap) hr
    have h1 := runFrom_step machine (wordConfig pref pre (b::bs) cap)
      (wordBitConfig pref pre b bs cap) _ (by rfl) (word_mark_step pref pre b bs cap) h2
    refine ⟨⟨r.final, r.steps+1+1, max (wordConfig pref pre (b::bs) cap).tapeCells
      (max (wordBitConfig pref pre b bs cap).tapeCells r.peakTapeCells)⟩, ?_, ?_, ?_⟩
    · rw [show 2*(b::bs).length+1 = 2*bs.length+1+1+1 by simp only [List.length_cons]; omega]
      exact h1
    · simpa [marks, frame, List.append_assoc] using hf
    · dsimp only
      simp only [List.length_cons]
      omega

end NearCubicGates.Adapters.Machine.Capped.RequestLoader
