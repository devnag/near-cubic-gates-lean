import Proof.MachineModel.OrdinaryRankPlacement

/-! Complete one-record rank labelling, on five fixed physical tapes. Each
head adjustment and every inter-program handoff is an executed transition. -/
namespace NearCubicWires.RepairOrdinary.RankBody
open LocalBitMultitape RankPlacement
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Executes {t s : ℕ} (p : Machine t s) (fuel space : ℕ) (c d : Configuration t s) : Prop :=
  ∃ r, runFrom p fuel c = some r ∧ r.final = d ∧ r.steps ≤ fuel ∧ r.peakTapeCells ≤ space

theorem Executes.join {t a b fp fq space : ℕ} {p : Machine t a} {q : Machine t b}
    {c d : Configuration t a} {e f : Configuration t b}
    (hp : Executes p fp space c d) (hq : Executes q fq space e f)
    (hl : Composition.restart d q.start = e) :
    Executes (Composition.machine p q) (fp + 1 + fq) space
      (Composition.leftConfig b c) (Composition.rightConfig a f) := by
  obtain ⟨r, hr, hrf, hrs, hrp⟩ := hp
  obtain ⟨s, hs, hsf, hss, hsp⟩ := hq
  have hsq : runFrom q fq (Composition.restart r.final q.start) = some s := by rw [hrf, hl]; exact hs
  refine ⟨Composition.joinedReceipt r s, Composition.run_join p q fp fq c r s hr hsq, ?_, ?_, ?_⟩
  · simp only [Composition.joinedReceipt, hsf]
  · change r.steps + 1 + s.steps ≤ fp + 1 + fq
    omega
  · exact max_le hrp hsp

def moveLeft (scratch : Bool) : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state _ => if state.val = 0 then
    some ⟨1, fun _ => none, fun i => if i.val = (if scratch then 4 else 3) then .left else .stay⟩
    else none

theorem move_run (scratch : Bool) (input output rank marks saved : List Bool)
    (sourceHead rankHead marksHead savedHead : ℕ) :
    Executes (moveLeft scratch) 1 (input.length + output.length + rank.length + marks.length + saved.length)
      (config 0 input sourceHead output rank rankHead marks marksHead saved savedHead)
      (config 1 input sourceHead output rank rankHead marks
        (if scratch then marksHead else marksHead - 1) saved (if scratch then savedHead - 1 else savedHead)) := by
  let c := config (0 : Fin 2) input sourceHead output rank rankHead marks marksHead saved savedHead
  let d := config (1 : Fin 2) input sourceHead output rank rankHead marks
    (if scratch then marksHead else marksHead - 1) saved (if scratch then savedHead - 1 else savedHead)
  have hstep : step (moveLeft scratch) c = some d := by
    simp [step, moveLeft, c, config]
    apply configuration_ext
    · rfl
    · funext i
      cases scratch <;> fin_cases i <;> simp [applyAction, HeadMove.apply, d, config]
    · rfl
  have hp : Prefix (moveLeft scratch)
      (input.length + output.length + rank.length + marks.length + saved.length) 1 c d :=
    Prefix.step (by simp [c]) (by rfl : (moveLeft scratch).halted c.control = false)
      hstep (Prefix.refl d (by simp [d]))
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp [d])
  exact ⟨r, hr, hf, hs.le, hb⟩

def scalarTail : Machine 5 8 :=
  Composition.machine (scalarMachine RankScalar.reset) (scalarMachine (Rewind.machine BinaryIncrement.machine))
def finish : Machine 5 10 := Composition.machine (moveLeft true) scalarTail
def appendTail : Machine 5 13 := Composition.machine appendMachine finish
def recordTail : Machine 5 15 := Composition.machine (moveLeft false) appendTail
def machine : Machine 5 18 := Composition.machine copyMachine recordTail

theorem marks_frame (bits : List Bool) : Streaming.marks bits ++ [false] = frame bits := by
  simpa [frame] using (Streaming.frame_append bits []).symm

theorem body_run (pre bits suffix output : List Bool) (n : ℕ) (hn : n + 1 < 2 ^ bits.length) :
    Executes machine (7 * bits.length + 12)
      ((pre ++ frame bits ++ suffix).length + output.length + 10 * bits.length + 2)
      (config 0 (pre ++ frame bits ++ suffix) pre.length output (SignedSortKey.binary bits.length n) 0
        (List.replicate bits.length false) 0 (List.replicate bits.length false) 0)
      (config 17 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (output ++ frame (bits ++ SignedSortKey.binary bits.length n)) (SignedSortKey.binary bits.length (n + 1)) 0
        (List.replicate bits.length false) 0 (List.replicate bits.length false) 0) := by
  let width := bits.length
  let input := pre ++ frame bits ++ suffix
  let pos := pre.length + 2 * width + 1
  let rank := SignedSortKey.binary width n
  let next := SignedSortKey.binary width (n + 1)
  let zeros := List.replicate width false
  let trues := List.replicate width true
  let copied := output ++ Streaming.marks bits
  let full := copied ++ Streaming.marks rank ++ [false]
  let space := input.length + output.length + 10 * width + 2
  have hrlen : rank.length = width := SignedSortKey.binary_length _ _
  have hcopied : copied.length = output.length + 2 * width := by simp [copied, width]
  have hfull : full.length = output.length + 4 * width + 1 := by simp [full, hcopied, hrlen]; omega
  have hcopy : Executes copyMachine (2 * width + 1) space
      (config 0 input pre.length output rank 0 zeros 0 zeros 0)
      (config 2 input pos copied rank 0 trues width zeros 0) := by
    obtain ⟨r, hr, hf, hs, hp⟩ := RankPlacement.copy_run pre bits suffix output rank hrlen
    exact ⟨r, hr, hf, hs.le, by dsimp [space, input, width]; omega⟩
  have hmoveH : Executes (moveLeft false) 1 space
      (config 0 input pos copied rank 0 trues width zeros 0)
      (config 1 input pos copied rank 0 trues (width - 1) zeros 0) := by
    obtain ⟨r, hr, hf, hs, hp⟩ := move_run false input copied rank trues zeros pos 0 width 0
    refine ⟨r, hr, hf, hs, ?_⟩
    simp only [hrlen, trues, zeros, List.length_replicate, hcopied] at hp
    dsimp only [space]
    omega
  have happend : Executes appendMachine (2 * width + 1) space
      (config 0 input pos copied rank 0 trues (width - 1) zeros 0)
      (config 2 input pos full rank width zeros 0 trues width) := by
    obtain ⟨r, hr, hf, hs, hp⟩ := RankPlacement.append_run input copied rank pos
    simp only [hrlen] at hr hf hs hp
    refine ⟨r, hr, hf, hs.le, ?_⟩
    rw [hcopied] at hp
    dsimp only [space]
    omega
  have hmoveA : Executes (moveLeft true) 1 space
      (config 0 input pos full rank width zeros 0 trues width)
      (config 1 input pos full rank width zeros 0 trues (width - 1)) := by
    obtain ⟨r, hr, hf, hs, hp⟩ := move_run true input full rank zeros trues pos width 0 width
    refine ⟨r, hr, hf, hs, ?_⟩
    simp only [hrlen, trues, zeros, List.length_replicate, hfull] at hp
    dsimp only [space]
    omega
  have hreset : Executes (scalarMachine RankScalar.reset) (width + 1) space
      (config 2 input pos full rank width zeros 0 trues (width - 1))
      (config 3 input pos full rank 0 zeros 0 zeros 0) := by
    obtain ⟨base, hb, hf, hs, hp⟩ := RankScalar.reset_run rank
    simp only [hrlen] at hb hf hs hp
    obtain ⟨r, hr, hrf, hrs, hrp⟩ := scalar_run RankScalar.reset (width + 1) 2 3 input full rank zeros trues
      rank zeros pos width 0 (width - 1) 0 0 base hb hf
    refine ⟨r, hr, hrf, by omega, ?_⟩
    simp only [hfull, zeros, List.length_replicate] at hrp
    dsimp only [space]
    omega
  have hinc : Executes (scalarMachine (Rewind.machine BinaryIncrement.machine)) (2 * width + 2) space
      (config 0 input pos full rank 0 zeros 0 zeros 0)
      (config 3 input pos full next 0 zeros 0 zeros 0) := by
    obtain ⟨base, hb, hf, hs, hp⟩ := RankScalar.increment_run width n hn
    obtain ⟨r, hr, hrf, hrs, hrp⟩ := scalar_run (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
      0 3 input full rank zeros zeros next zeros pos 0 0 0 0 0 base hb hf
    refine ⟨r, hr, hrf, by omega, ?_⟩
    simp only [hfull, zeros, List.length_replicate] at hrp
    dsimp only [space]
    omega
  have htail := hreset.join hinc (by rfl)
  have hfinish := hmoveA.join htail (by rfl)
  have happendTail := happend.join hfinish (by rfl)
  have hrecordTail := hmoveH.join happendTail (by rfl)
  have hbody := hcopy.join hrecordTail (by rfl)
  have hout : full = output ++ frame (bits ++ rank) := by
    simp only [full, copied, List.append_assoc, marks_frame, Streaming.frame_append]
  have hbudget : (2 * width + 1) + 1 + (1 + 1 + ((2 * width + 1) + 1 +
      (1 + 1 + ((width + 1) + 1 + (2 * width + 2))))) = 7 * width + 12 := by omega
  rw [hbudget] at hbody
  have hstart : (0 : Fin 3).castAdd 15 = (0 : Fin 18) := by decide
  have hstop : (((((3 : Fin 4).natAdd 4).natAdd 2).natAdd 3).natAdd 2).natAdd 3 =
      (17 : Fin 18) := by decide
  simpa only [machine, recordTail, appendTail, finish, scalarTail, Composition.leftConfig,
    Composition.rightConfig, config, hout, width, input, pos, rank, next, zeros, space,
    hstart, hstop] using hbody

end NearCubicWires.RepairOrdinary.RankBody
