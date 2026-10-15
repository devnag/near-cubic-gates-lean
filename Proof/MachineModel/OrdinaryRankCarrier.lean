import Proof.MachineModel.OrdinaryRankLoop

/-! Complete rank labelling in the shared ordinary carrier. Only the framed
record stream is supplied: every work tape really starts empty. -/
namespace NearCubicWires.RepairOrdinary.RankCarrier
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_zero (width : ℕ) : SignedSortKey.binary width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [SignedSortKey.binary, ih, List.replicate_succ]

def capacity (width : ℕ) : Fin 5 → ℕ := fun i => if i.val < 2 then 0 else width

theorem raw_run (width : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) (hn : words.length < 2 ^ width) :
    ∃ r : ExecutionReceipt 5 20,
      run RankLoop.machine (words.length * (7 * width + 14) + 1)
        (SourceHandoff.sourceTapes (RankLoop.stream words)) = some r ∧
      r.final.tapes 1 = RankLoop.labels width 0 words ++ [false] ∧
      r.steps ≤ words.length * (7 * width + 14) + 1 ∧
      r.peakTapeCells ≤ (RankLoop.stream words).length + words.length * (4 * width + 1) + 10 * width + 3 := by
  obtain ⟨base, hb, hf, hs, hp⟩ := RankLoop.loop_run width words [] [] 0 hw (by simpa using hn)
  have hi : ZeroPadding.config (capacity width)
      (initialConfiguration RankLoop.machine (SourceHandoff.sourceTapes (RankLoop.stream words))) =
      RankPlacement.config (RecordController.test 18) (RankLoop.stream words) 0 [] (SignedSortKey.binary width 0) 0
        (List.replicate width false) 0 (List.replicate width false) 0 := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, capacity, initialConfiguration, SourceHandoff.sourceTapes,
        RankPlacement.config, ZeroPadding.pad, binary_zero]
  have hb' : runFrom RankLoop.machine (words.length * (7 * width + 14) + 1)
      (ZeroPadding.config (capacity width)
        (initialConfiguration RankLoop.machine (SourceHandoff.sourceTapes (RankLoop.stream words)))) = some base := by
    rw [hi]
    simpa using hb
  obtain ⟨r, hr, hrf, hrs, hrp⟩ := ZeroPadding.run_unpad RankLoop.machine (capacity width) _ _ base hb'
  refine ⟨r, hr, ?_, hrs.le.trans hs, ?_⟩
  · have he := congrArg (fun c : Configuration 5 20 => c.tapes 1) hrf
    rw [hf] at he
    simpa [ZeroPadding.config, capacity, RankPlacement.config] using he
  · simp only [List.nil_append, List.length_nil, Nat.add_zero] at hp
    exact hrp.trans hp

structure Request where
  width : ℕ
  words : List (List Bool)
  uniform : ∀ word ∈ words, word.length = width
  fits : words.length < 2 ^ width

def carrier : WordFunction Request (fun req => RankLoop.stream req.words)
    (fun req => RankLoop.labels req.width 0 req.words ++ [false])
    (fun req => 4 * (RankLoop.stream req.words).length + 3 + (req.words.length * (7 * req.width + 14) + 1)) :=
  FramedSource.ofRaw (Request := Request) (t := 5) (s := 20) (by decide) RankLoop.machine (1 : Fin 5)
    (fun req => RankLoop.stream req.words) (fun req => RankLoop.labels req.width 0 req.words ++ [false])
    (fun req => req.words.length * (7 * req.width + 14) + 1) (by
      intro req
      obtain ⟨r, hr, ho, _, _⟩ := raw_run req.width req.words req.uniform req.fits
      exact ⟨r, hr, ho⟩)

theorem stream_length (width : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) :
    (RankLoop.stream words).length = words.length * (2 * width + 1) + 1 := by
  have h : (words.flatMap frame).length = words.length * (2 * width + 1) := by
    induction words with
    | nil => simp
    | cons word words ih =>
      have hword := hw word (by simp)
      have ht := ih (fun w hm => hw w (by simp [hm]))
      simp only [List.flatMap_cons, List.length_append, frame_length, hword, ht, List.length_cons,
        Nat.add_mul, one_mul]
      omega
  simp [RankLoop.stream, h]

theorem carrier_budget (req : Request) :
    4 * (RankLoop.stream req.words).length + 3 + (req.words.length * (7 * req.width + 14) + 1) ≤
      64 * (req.words.length + 1) * (req.width + 1) := by
  rw [stream_length req.width req.words req.uniform]
  nlinarith

def boundedCarrier : WordFunction Request (fun req => RankLoop.stream req.words)
    (fun req => RankLoop.labels req.width 0 req.words ++ [false])
    (fun req => 64 * (req.words.length + 1) * (req.width + 1)) := carrier.enlargeBudget carrier_budget

end NearCubicWires.RepairOrdinary.RankCarrier
