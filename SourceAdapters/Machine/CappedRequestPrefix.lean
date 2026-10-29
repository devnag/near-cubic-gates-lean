import SourceAdapters.Machine.CappedRequestLoader

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: physically copy the unary cap before the source word. -/
namespace NearCubicGates.Adapters.Machine.Capped.RequestLoader
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open Streaming (marks marks_length frame_append read_append write_append)
set_option autoImplicit false

def capConfig (done left : ℕ) (word : List Bool) : Configuration 4 6 :=
  config 1 (frame (List.replicate (done+left) true) ++ frame word) (2*done)
    [] 0 (List.replicate done true) done [true]

def capBitConfig (done left : ℕ) (word : List Bool) : Configuration 4 6 :=
  config 2 (frame (List.replicate (done+(left+1)) true) ++ frame word) (2*done+1)
    [] 0 (List.replicate done true) done [true]

theorem cap_mark_step (done left : ℕ) (word : List Bool) :
    step machine (capConfig done (left+1) word) = some (capBitConfig done left word) := by
  have hi : frame (List.replicate (done+(left+1)) true) ++ frame word =
      marks (List.replicate done true) ++ true::true::(frame (List.replicate left true) ++ frame word) := by
    rw [List.replicate_add, frame_append]
    simp [List.replicate_succ, frame, List.append_assoc]
  have hs : (capConfig done (left+1) word).scanned 0 = true := by
    change readTapeBit (frame (List.replicate (done+(left+1)) true) ++ frame word) (2*done) = true
    rw [hi]
    simpa using read_append (marks (List.replicate done true))
      (true::(frame (List.replicate left true) ++ frame word)) true
  have hRule : machine.rule (capConfig done (left+1) word).control
      (capConfig done (left+1) word).scanned = some (action 2 .right .stay .stay none none none) := by
    change (if (capConfig done (left+1) word).scanned 0 then _ else _) = _
    rw [hs]
    rfl
  rw [step, hRule]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, capConfig, capBitConfig, config, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, capConfig, capBitConfig, config]

theorem cap_bit_step (done left : ℕ) (word : List Bool) :
    step machine (capBitConfig done left word) = some (capConfig (done+1) left word) := by
  have hw : writeTapeBit (List.replicate done true) done true = List.replicate (done+1) true := by
    calc
      _ = List.replicate done true ++ [true] := by
        simpa only [List.length_replicate] using write_append (List.replicate done true) true
      _ = _ := by simp [List.replicate_add]
  have hRule : machine.rule (capBitConfig done left word).control
      (capBitConfig done left word).scanned = some (action 1 .right .stay .right none (some true) none) := rfl
  rw [step, hRule]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, capConfig, capBitConfig, config, HeadMove.apply]; omega
  · funext i; fin_cases i <;> simp [applyAction, action, capConfig, capBitConfig, config, hw, Nat.add_comm, Nat.add_left_comm]

theorem cap_end_step (done : ℕ) (word : List Bool) :
    step machine (capConfig done 0 word) =
      some (wordConfig (frame (List.replicate done true)) [] word done) := by
  have hi : frame (List.replicate done true) ++ frame word =
      marks (List.replicate done true) ++ false::frame word := by
    have h := frame_append (List.replicate done true) []
    simp only [List.append_nil, frame] at h
    rw [h]
    simp [List.append_assoc]
  have hs : (capConfig done 0 word).scanned 0 = false := by
    change readTapeBit (frame (List.replicate (done+0) true) ++ frame word) (2*done) = false
    rw [Nat.add_zero, hi]
    simpa using read_append (marks (List.replicate done true)) (frame word) false
  have hRule : machine.rule (capConfig done 0 word).control
      (capConfig done 0 word).scanned = some (action 3 .right .stay .stay none none none) := by
    change (if (capConfig done 0 word).scanned 0 then _ else _) = _
    rw [hs]
    rfl
  rw [step, hRule]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, capConfig, wordConfig, config, HeadMove.apply, frame_length]
  · funext i; fin_cases i <;> simp [applyAction, action, capConfig, wordConfig, config, marks]

theorem cap_run (done left : ℕ) (word : List Bool) :
    ∃ r, runFrom machine (2*left+2*word.length+2) (capConfig done left word) = some r ∧
      r.final = finished (frame (List.replicate (done+left) true) ++ frame word)
        (frame word) (done+left) ∧ r.steps = 2*left+2*word.length+2 := by
  induction left generalizing done with
  | zero =>
    obtain ⟨r, hr, hf, hs⟩ := word_run (frame (List.replicate done true)) [] word done
    have h := runFrom_step machine (capConfig done 0 word)
      (wordConfig (frame (List.replicate done true)) [] word done) r
      (by rfl) (cap_end_step done word) hr
    refine ⟨⟨r.final, r.steps+1, max (capConfig done 0 word).tapeCells r.peakTapeCells⟩, ?_, ?_, ?_⟩
    · rw [show 2*0+2*word.length+2 = 2*word.length+1+1 by omega]
      exact h
    · simpa [marks] using hf
    · dsimp only; omega
  | succ left ih =>
    obtain ⟨r, hr, hf, hs⟩ := ih (done+1)
    have h2 := runFrom_step machine (capBitConfig done left word)
      (capConfig (done+1) left word) r (by rfl) (cap_bit_step done left word) hr
    have h1 := runFrom_step machine (capConfig done (left+1) word)
      (capBitConfig done left word) _ (by rfl) (cap_mark_step done left word) h2
    refine ⟨⟨r.final, r.steps+1+1, max (capConfig done (left+1) word).tapeCells
      (max (capBitConfig done left word).tapeCells r.peakTapeCells)⟩, ?_, ?_, ?_⟩
    · rw [show 2*(left+1)+2*word.length+2 = 2*left+2*word.length+2+1+1 by omega]
      exact h1
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    · dsimp only; omega

/-- Actual raw request unpacking, prior to the separately charged head reset. -/
theorem loader_run (cap : ℕ) (word : List Bool) :
    ∃ r, run machine (2*cap+2*word.length+3)
        (fun i => if i.val=0 then frame (List.replicate cap true) ++ frame word else []) = some r ∧
      r.final = finished (frame (List.replicate cap true) ++ frame word) (frame word) cap ∧
      r.steps = 2*cap+2*word.length+3 := by
  obtain ⟨r, hr, hf, hs⟩ := cap_run 0 cap word
  let inp : Fin 4 → List Bool := fun i =>
    if i.val=0 then frame (List.replicate cap true) ++ frame word else []
  have hstep : step machine (initialConfiguration machine inp) = some (capConfig 0 cap word) := by
    rw [step]
    change some (applyAction (initialConfiguration machine inp)
      (action 1 .stay .stay .stay none none (some true))) = _
    congr 1
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, action, initialConfiguration, capConfig, config, HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction, action, initialConfiguration, capConfig, config, inp, writeTapeBit]
  have hj := runFrom_step machine (initialConfiguration machine inp) (capConfig 0 cap word)
    r (by rfl) hstep hr
  refine ⟨⟨r.final, r.steps+1, max (initialConfiguration machine inp).tapeCells r.peakTapeCells⟩, ?_, ?_, ?_⟩
  · change runFrom machine (2*cap+2*word.length+3) (initialConfiguration machine inp) = _
    rw [show 2*cap+2*word.length+3 = 2*cap+2*word.length+2+1 by omega]
    exact hj
  · simpa using hf
  · dsimp only; omega

end NearCubicGates.Adapters.Machine.Capped.RequestLoader
