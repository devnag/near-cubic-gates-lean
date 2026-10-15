import Proof.MachineModel.OrdinaryKeyCell

/-! Whole keyed occurrence traversal. The controller reads the actual framed
annotated records and appends cell/inner/id records with no table rewind. -/
namespace NearCubicWires.RepairOrdinary.KeyLoop
open LocalBitMultitape SignedSortKey
open KeyCell (config)
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Record := ℤ × ℕ × ℕ
def word (S K : ℕ) (r : Record) : List Bool := RadixSemantics.word (encode S K r.1 r.2.1)
def fields (S K : ℕ) (records : List Record) : List Bool :=
  records.flatMap (fun r => frame (word S K r ++ binary (K + S + 1) r.2.2))
def stream (S K : ℕ) (records : List Record) : List Bool := fields S K records ++ [false]
def output (K I inner a b : ℕ) (mask : Bool) (records : List Record) : List Bool :=
  records.flatMap (fun r => frame (LeftCell.selected a b r.2.2 mask :: (binary I inner ++ binary K r.2.1)))
def machine : Machine 20 55 := StreamController.machine KeyCell.machine 15

@[simp] theorem word_length (S K : ℕ) (r : Record) : (word S K r).length = K + S + 1 := encode_width _ _ _ _
@[simp] theorem output_length (K I inner a b : ℕ) (mask : Bool) (records : List Record) :
    (output K I inner a b mask records).length = records.length * (2 * (I + K) + 3) := by
  induction records with
  | nil => simp [output]
  | cons r rs ih =>
    simp only [output, List.flatMap_cons, List.length_append] at *
    simp only [frame_length, List.length_cons, List.length_append, binary_length, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem loop_prefix (S K I inner cap a b initialRank : ℕ) (records : List Record)
    (pre upper recordBack cloneBack out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ (K + S + 1)) (hrecords : ∀ r ∈ records, r.2.2 < 2 ^ (K + S + 1))
    (hu : upper.length ≤ 2 * (K + S + 1) + 1) (hr : recordBack.length ≤ 4 * (K + S + 1) + 1)
    (hc : cloneBack.length ≤ 4 * (K + S + 1) + 1) (hci : 2 * I ≤ cap) (hck : 2 * K ≤ cap) :
    let W := K + S + 1
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * W + 1 ∧ finalRecord.length ≤ 4 * W + 1 ∧ finalClone.length ≤ 4 * W + 1 ∧
      ∃ steps, steps ≤ records.length * (68 * W + 4 * (I + K) + 63) + 1 ∧
      Prefix machine ((pre ++ stream S K records).length + 104 * W + 8 * I + 6 * K + out.length +
          records.length * (2 * (I + K) + 3) + cap + 64) steps
        (config (test 53) W a b initialRank upper recordBack cloneBack mask (pre ++ stream S K records) pre.length out K I inner cap)
        (config (stop 53) W a b finalRank finalUpper finalRecord finalClone mask (pre ++ stream S K records)
          (pre.length + (fields S K records).length) (out ++ output K I inner a b mask records) K I inner cap) := by
  let W := K + S + 1
  induction records generalizing pre initialRank upper recordBack cloneBack out with
  | nil =>
    let source := pre ++ [false]
    let c := config KeyCell.machine.start W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap
    have hread : c.scanned 15 = false := by
      change readTapeBit (pre ++ [false]) pre.length = false
      exact Streaming.read_append pre [] false
    have hstop := StreamController.stop_step KeyCell.machine 15 c hread
    let space := source.length + 104 * W + 8 * I + 6 * K + out.length + cap + 64
    have hstart : (controlConfig (fun _ => test 53) c).tapeCells ≤ space := by
      change (config (test 53) W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap).tapeCells ≤ space
      simp only [KeyCell.config_cells]
      dsimp only [space, W]
      omega
    have hend : (controlConfig (fun _ => stop 53) c).tapeCells ≤ space := hstart
    have hp : Prefix machine space 1 (controlConfig (fun _ => test 53) c) (controlConfig (fun _ => stop 53) c) :=
      Prefix.step hstart (StreamController.test_halted _ _) hstop (Prefix.refl _ hend)
    refine ⟨initialRank, upper, recordBack, cloneBack, hu, hr, hc, 1, by simp, ?_⟩
    simpa [stream, fields, output, source, space, c, controlConfig, config,
      RecordCell.config, TapeEmbedding.config, CellEmit.config] using hp
  | cons entry records ih =>
    let rank := entry.2.2
    have hrank : rank < 2 ^ W := hrecords entry (by simp)
    have htailRecords : ∀ r ∈ records, r.2.2 < 2 ^ W := fun r hm => hrecords r (by simp [hm])
    let source := pre ++ stream S K (entry :: records)
    let next := pre.length + 4 * W + 1
    let newUpper := frame (binary W (a + b))
    let stored := frame (word S K entry ++ binary W rank)
    let keyWord := frame (LeftCell.selected a b rank mask :: (binary I inner ++ binary K entry.2.1))
    let appended := out ++ keyWord
    let space := source.length + 104 * W + 8 * I + 6 * K + out.length +
      (records.length + 1) * (2 * (I + K) + 3) + cap + 64
    have hstored : stored.length = 4 * W + 1 := by simp [stored, W]; omega
    have hkey : keyWord.length = 2 * (I + K) + 3 := by simp [keyWord]; omega
    have hsource : pre ++ stored ++ stream S K records = source := by simp [source, stored, rank, W, stream, fields, List.append_assoc]
    obtain ⟨body, hbody, hbf, hbs, hbp⟩ := KeyCell.body_run S K I inner cap entry.2.1 entry.1 a b rank initialRank
      pre (stream S K records) upper recordBack cloneBack out mask hfit hrank hu hr hc hci hck
    change runFrom KeyCell.machine (68 * W + 4 * (I + K) + 61)
      (config 0 W a b initialRank upper recordBack cloneBack mask (pre ++ stored ++ stream S K records) pre.length out K I inner cap) = some body at hbody
    change body.final = config 52 W a b rank newUpper stored stored mask (pre ++ stored ++ stream S K records) next appended K I inner cap at hbf
    change body.peakTapeCells ≤ (pre ++ stored ++ stream S K records).length + 104 * W + 8 * I + 6 * K + out.length + cap + 64 at hbp
    rw [hsource] at hbody hbf hbp
    obtain ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, tailSteps, ht, tailPrefix⟩ :=
      ih rank (pre ++ stored) newUpper stored stored appended htailRecords
        (by simp [newUpper, W]) hstored.le hstored.le
    have tailPrefix' : Prefix machine space tailSteps
        (config (test 53) W a b rank newUpper stored stored mask source next appended K I inner cap)
        (config (stop 53) W a b finalRank finalUpper finalRecord finalClone mask source
          (pre.length + (fields S K (entry :: records)).length) (out ++ output K I inner a b mask (entry :: records)) K I inner cap) := by
      rw [hsource] at tailPrefix
      have hspace : source.length + 104 * W + 8 * I + 6 * K + appended.length +
          records.length * (2 * (I + K) + 3) + cap + 64 = space := by
        dsimp only [space, appended]
        simp only [List.length_append, hkey, Nat.add_mul, Nat.one_mul]
        omega
      have hpos : (pre ++ stored).length = next := by simp [next, hstored, Nat.add_assoc]
      have hfields : (fields S K (entry :: records)).length = stored.length + (fields S K records).length := by
        change (frame (word S K entry ++ binary (K + S + 1) entry.2.2) ++ fields S K records).length = _
        rw [List.length_append]
      have hendpos : (pre ++ stored).length + (fields S K records).length = pre.length + (fields S K (entry :: records)).length := by
        rw [List.length_append, hfields]
        omega
      have hout : appended ++ output K I inner a b mask records = out ++ output K I inner a b mask (entry :: records) := by
        simp only [appended, keyWord, output, List.flatMap_cons, List.append_assoc, rank]
      rw [hendpos, hspace, hpos, hout] at tailPrefix
      exact tailPrefix
    obtain ⟨bp, halted⟩ := StreamController.body_prefix KeyCell.machine 15 _ _ body hbody
    have bp' : Prefix machine space body.steps
        (controlConfig code (config KeyCell.machine.start W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap))
        (controlConfig code (config (52 : Fin 53) W a b rank newUpper stored stored mask source next appended K I inner cap)) := by
      rw [← hbf]
      exact bp.enlarge (by dsimp only [space]; omega)
    have hend : (config (test 53) W a b rank newUpper stored stored mask source next appended K I inner cap).tapeCells ≤ space := by
      simp only [KeyCell.config_cells, hstored]
      dsimp only [space, appended, newUpper]
      simp only [List.length_append, frame_length, binary_length, hkey]
      omega
    have hreturn : step machine (controlConfig code
        (config (52 : Fin 53) W a b rank newUpper stored stored mask source next appended K I inner cap)) =
        some (config (test 53) W a b rank newUpper stored stored mask source next appended K I inner cap) := by
      have h := StreamController.return_step KeyCell.machine 15 body.final halted
      rw [hbf] at h
      exact h
    have returned : Prefix machine space (tailSteps + 1)
        (controlConfig code (config (52 : Fin 53) W a b rank newUpper stored stored mask source next appended K I inner cap))
        (config (stop 53) W a b finalRank finalUpper finalRecord finalClone mask source
          (pre.length + (fields S K (entry :: records)).length) (out ++ output K I inner a b mask (entry :: records)) K I inner cap) :=
      Prefix.step hend (StreamController.body_halted _ _ _) hreturn tailPrefix'
    have hread : readTapeBit source pre.length = true := by
      rw [← hsource]
      have hw := word_length S K entry
      cases he : word S K entry with
      | nil => simp [he] at hw
      | cons bit ws =>
        simpa [stored, he, frame, List.append_assoc] using
          Streaming.read_append pre (bit :: frame (ws ++ binary W rank) ++ stream S K records) true
    have henter : step machine
        (config (test 53) W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap) =
        some (controlConfig code (config KeyCell.machine.start W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap)) :=
      StreamController.enter_step KeyCell.machine 15
        (config KeyCell.machine.start W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap) hread
    have hstart : (config (test 53) W a b initialRank upper recordBack cloneBack mask source pre.length out K I inner cap).tapeCells ≤ space := by
      simp only [KeyCell.config_cells]
      dsimp only [space, W]
      omega
    have joined := Prefix.step hstart (StreamController.test_halted _ _) henter (bp'.trans returned)
    refine ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, body.steps + (tailSteps + 1) + 1, ?_, joined⟩
    simp only [List.length_cons, Nat.add_mul]
    omega

theorem loop_run (S K I inner cap a b initialRank : ℕ) (records : List Record)
    (pre upper recordBack cloneBack out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ (K + S + 1)) (hrecords : ∀ r ∈ records, r.2.2 < 2 ^ (K + S + 1))
    (hu : upper.length ≤ 2 * (K + S + 1) + 1) (hr : recordBack.length ≤ 4 * (K + S + 1) + 1)
    (hc : cloneBack.length ≤ 4 * (K + S + 1) + 1) (hci : 2 * I ≤ cap) (hck : 2 * K ≤ cap) :
    let W := K + S + 1
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * W + 1 ∧ finalRecord.length ≤ 4 * W + 1 ∧ finalClone.length ≤ 4 * W + 1 ∧
      ∃ r : ExecutionReceipt 20 55,
        runFrom machine (records.length * (68 * W + 4 * (I + K) + 63) + 1)
          (config (test 53) W a b initialRank upper recordBack cloneBack mask (pre ++ stream S K records) pre.length out K I inner cap) = some r ∧
        r.final = config (stop 53) W a b finalRank finalUpper finalRecord finalClone mask (pre ++ stream S K records)
          (pre.length + (fields S K records).length) (out ++ output K I inner a b mask records) K I inner cap ∧
        r.steps ≤ records.length * (68 * W + 4 * (I + K) + 63) + 1 ∧
        r.peakTapeCells ≤ (pre ++ stream S K records).length + 104 * W + 8 * I + 6 * K + out.length +
          records.length * (2 * (I + K) + 3) + cap + 64 := by
  obtain ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, steps, hsteps, hp⟩ :=
    loop_prefix S K I inner cap a b initialRank records pre upper recordBack cloneBack out mask hfit hrecords hu hr hc hci hck
  obtain ⟨r, hr', hf, hs, hb⟩ := hp.run (StreamController.stop_halted _ _) (by simp; omega)
  have hrun := runFrom_moreFuel machine steps (records.length * (68 * (K + S + 1) + 4 * (I + K) + 63) + 1 - steps) _ r hr'
  rw [Nat.add_sub_of_le hsteps] at hrun
  exact ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, r, hrun, hf, hs.le.trans hsteps, hb⟩

end NearCubicWires.RepairOrdinary.KeyLoop
