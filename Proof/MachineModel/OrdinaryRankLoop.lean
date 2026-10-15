import Proof.MachineModel.OrdinaryRecordController

/-! Complete actual record-rank scan. The fixed controller reads the framed
stream itself; neither its state count nor tape count depends on record count. -/
namespace NearCubicWires.RepairOrdinary.RankLoop
open LocalBitMultitape RankPlacement
open RankBody (Executes)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream (words : List (List Bool)) : List Bool := words.flatMap frame ++ [false]
def labels (width n : ℕ) : List (List Bool) → List Bool
  | [] => []
  | word :: words => frame (word ++ SignedSortKey.binary width n) ++ labels width (n + 1) words
def machine : Machine 5 20 := RecordController.machine RankBody.machine

theorem labels_length (width n : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) :
    (labels width n words).length = words.length * (4 * width + 1) := by
  induction words generalizing n with
  | nil => simp [labels]
  | cons word words ih =>
    have h := hw word (by simp)
    have ht := ih (n + 1) (fun w hm => hw w (by simp [hm]))
    simp only [labels, List.length_append, frame_length, SignedSortKey.binary_length, h, ht, List.length_cons,
      Nat.add_mul, one_mul]
    omega

theorem loop_run (width : ℕ) (words : List (List Bool)) (pre output : List Bool) (n : ℕ)
    (hw : ∀ word ∈ words, word.length = width) (hn : n + words.length < 2 ^ width) :
    Executes machine (words.length * (7 * width + 14) + 1)
      ((pre ++ stream words).length + output.length + words.length * (4 * width + 1) + 10 * width + 3)
      (config (RecordController.test 18) (pre ++ stream words) pre.length output (SignedSortKey.binary width n) 0
        (List.replicate width false) 0 (List.replicate width false) 0)
      (config (RecordController.stop 18) (pre ++ stream words) (pre.length + (words.flatMap frame).length)
        (output ++ labels width n words ++ [false]) (SignedSortKey.binary width (n + words.length)) 0
        (List.replicate width false) 0 (List.replicate width false) 0) := by
  induction words generalizing pre output n with
  | nil =>
    let c := config (RecordController.test 18) (pre ++ [false]) pre.length output (SignedSortKey.binary width n) 0
      (List.replicate width false) 0 (List.replicate width false) 0
    let d := config (RecordController.stop 18) (pre ++ [false]) pre.length (output ++ [false])
      (SignedSortKey.binary width n) 0 (List.replicate width false) 0 (List.replicate width false) 0
    let space := (pre ++ [false]).length + output.length + 10 * width + 3
    have hc : c.tapeCells ≤ space := by simp [c, space]; omega
    have hd : d.tapeCells ≤ space := by simp [d, space]; omega
    have hs : step machine c = some d :=
      RecordController.stop_step RankBody.machine (pre ++ [false]) output (SignedSortKey.binary width n)
        (List.replicate width false) (List.replicate width false) pre.length 0 0 0
        (Streaming.read_append pre [] false)
    have hp : Prefix machine space 1 c d := Prefix.step hc (RecordController.test_halted _)
      hs (Prefix.refl _ hd)
    obtain ⟨r, hr, hf, hsteps, hpeak⟩ := hp.run (RecordController.stop_halted _) hd
    refine ⟨r, by simpa [stream, c] using hr, by simpa [stream, labels, d] using hf,
      by simpa using hsteps.le, by simpa [stream, space] using hpeak⟩
  | cons word words ih =>
    have hword : word.length = width := hw word (by simp)
    have hwords : ∀ w ∈ words, w.length = width := fun w hm => hw w (by simp [hm])
    have hguard : n + 1 < 2 ^ width := by simp only [List.length_cons] at hn; omega
    have htailguard : n + 1 + words.length < 2 ^ width := by simp only [List.length_cons] at hn; omega
    let input := pre ++ stream (word :: words)
    let rank := SignedSortKey.binary width n
    let next := SignedSortKey.binary width (n + 1)
    let zeros := List.replicate width false
    let appended := output ++ frame (word ++ rank)
    let pos := pre.length + 2 * width + 1
    let space := input.length + output.length + (words.length + 1) * (4 * width + 1) + 10 * width + 3
    have hinput : pre ++ frame word ++ stream words = input := by simp [input, stream, List.append_assoc]
    have happended : appended.length = output.length + 4 * width + 1 := by simp [appended, rank, hword]; omega
    have hc : (config (RecordController.test 18) input pre.length output rank 0 zeros 0 zeros 0).tapeCells ≤ space := by
      simp only [config_cells, rank, SignedSortKey.binary_length, zeros, List.length_replicate]
      dsimp only [space]
      omega
    have hb : Executes RankBody.machine (7 * width + 12) space
        (config 0 input pre.length output rank 0 zeros 0 zeros 0)
        (config 17 input pos appended next 0 zeros 0 zeros 0) := by
      obtain ⟨r, hr, hf, hs, hp⟩ := RankBody.body_run pre word (stream words) output n (by simpa [hword] using hguard)
      simp only [hword, hinput] at hr hf hs hp
      refine ⟨r, hr, hf, hs, ?_⟩
      dsimp only [space]
      omega
    have ht : Executes machine (words.length * (7 * width + 14) + 1) space
        (config (RecordController.test 18) input pos appended next 0 zeros 0 zeros 0)
        (config (RecordController.stop 18) input (pre.length + ((word :: words).flatMap frame).length)
          (output ++ labels width n (word :: words) ++ [false])
          (SignedSortKey.binary width (n + (word :: words).length)) 0 zeros 0 zeros 0) := by
      have hi := ih (pre ++ frame word) appended (n + 1) hwords htailguard
      convert hi using 1 <;> simp [space, input, stream, labels, pos, appended, rank, next, zeros,
        hword, List.append_assoc, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    obtain ⟨body, hbody, hbf, hbs, hbp⟩ := hb
    obtain ⟨tail, htail, htf, hts, htp⟩ := ht
    obtain ⟨bodyPrefix, hhalt⟩ := RecordController.body_prefix RankBody.machine (7 * width + 12) _ body hbody
    have bodyPrefix' : Prefix machine space body.steps
        (controlConfig RecordController.code (config (0 : Fin 18) input pre.length output rank 0 zeros 0 zeros 0))
        (controlConfig RecordController.code (config (17 : Fin 18) input pos appended next 0 zeros 0 zeros 0)) := by
      rw [← hbf]
      exact bodyPrefix.enlarge hbp
    have hend : (config (RecordController.test 18) input pos appended next 0 zeros 0 zeros 0).tapeCells ≤ space := by
      simp only [config_cells, next, SignedSortKey.binary_length, zeros, List.length_replicate, happended]
      dsimp only [space]
      omega
    have hreturn : step machine
        (controlConfig RecordController.code (config (17 : Fin 18) input pos appended next 0 zeros 0 zeros 0)) =
        some (config (RecordController.test 18) input pos appended next 0 zeros 0 zeros 0) := by
      have hr := RecordController.return_step RankBody.machine body.final hhalt
      rw [hbf] at hr
      exact hr
    have returnPrefix : Prefix machine space 1
        (controlConfig RecordController.code (config (17 : Fin 18) input pos appended next 0 zeros 0 zeros 0))
        (config (RecordController.test 18) input pos appended next 0 zeros 0 zeros 0) :=
      Prefix.step hend (RecordController.body_halted _ _) hreturn (Prefix.refl _ hend)
    have hread : readTapeBit input pre.length = true := by
      have hwidth : 0 < width := by
        by_contra h
        have hz : width = 0 := by omega
        simp [hz] at hguard
      cases word with
      | nil => simp at hword; omega
      | cons bit bits =>
        have hr := Streaming.read_append pre (bit :: frame bits ++ stream words) true
        simpa [input, stream, frame, List.append_assoc] using hr
    have henter : step machine (config (RecordController.test 18) input pre.length output rank 0 zeros 0 zeros 0) =
        some (controlConfig RecordController.code (config (0 : Fin 18) input pre.length output rank 0 zeros 0 zeros 0)) :=
      RecordController.enter_step RankBody.machine input output rank zeros zeros pre.length 0 0 0 hread
    have phasePrefix := Prefix.step hc (RecordController.test_halted _) henter (bodyPrefix'.trans returnPrefix)
    obtain ⟨r, hr, hf, hs, hp⟩ := phasePrefix.followedBy tail htail
    have hbound : (body.steps + 1 + 1) + (words.length * (7 * width + 14) + 1) ≤
        (word :: words).length * (7 * width + 14) + 1 := by
      simp only [List.length_cons, Nat.add_mul]
      omega
    have hmore := runFrom_moreFuel machine ((body.steps + 1 + 1) + (words.length * (7 * width + 14) + 1))
      ((word :: words).length * (7 * width + 14) + 1 -
        ((body.steps + 1 + 1) + (words.length * (7 * width + 14) + 1))) _ r hr
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨r, hmore, hf.trans htf, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul]
      omega
    · exact hp.trans (max_le (Nat.le_refl _) htp)

end NearCubicWires.RepairOrdinary.RankLoop
