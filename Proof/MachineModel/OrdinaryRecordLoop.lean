import Proof.MachineModel.OrdinaryRecordCell

/-! Complete cell evaluation on the actual annotated-record encoding. The
fixed controller consumes the table itself; every local rank extraction,
reset and output append is charged by the accepted record body. -/
namespace NearCubicWires.RepairOrdinary.RecordLoop
open LocalBitMultitape SignedSortKey
open RecordCell (config)
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Record := List Bool × ℕ
def fields (width : ℕ) (records : List Record) : List Bool :=
  records.flatMap (fun r => frame (r.1 ++ binary width r.2))
def stream (width : ℕ) (records : List Record) : List Bool := fields width records ++ [false]
def bits (a b : ℕ) (mask : Bool) (records : List Record) : List Bool :=
  records.map (fun r => LeftCell.selected a b r.2 mask)
def machine : Machine 16 43 := StreamController.machine RecordCell.machine 15

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (width a b rank : ℕ)
    (upper recordBack cloneBack : List Bool) (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (config state width a b rank upper recordBack cloneBack mask source pos out).tapeCells =
      source.length + out.length + upper.length + recordBack.length + cloneBack.length + 52 * width + 31 := by
  simp [config, TapeEmbedding.config, CellEmit.config, LocalCell.input, LocalCell.raw,
    RecordCell.recordTapes, Configuration.tapeCells, Fin.sum_univ_succ, Fin.addCases]
  omega

theorem loop_prefix (width a b initialRank : ℕ) (records : List Record)
    (pre upper recordBack cloneBack out : List Bool) (mask : Bool) (hw : 0 < width)
    (hfit : a + b < 2 ^ width)
    (hrecords : ∀ r ∈ records, r.1.length = width ∧ r.2 < 2 ^ width)
    (hu : upper.length ≤ 2 * width + 1) (hr : recordBack.length ≤ 4 * width + 1)
    (hc : cloneBack.length ≤ 4 * width + 1) :
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * width + 1 ∧ finalRecord.length ≤ 4 * width + 1 ∧ finalClone.length ≤ 4 * width + 1 ∧
      Prefix machine ((pre ++ stream width records).length + 104 * width + out.length + records.length + 53)
        (records.length * (68 * width + 53) + 1)
        (config (test 41) width a b initialRank upper recordBack cloneBack mask (pre ++ stream width records) pre.length out)
        (config (stop 41) width a b finalRank finalUpper finalRecord finalClone mask (pre ++ stream width records)
          (pre.length + (fields width records).length) (out ++ bits a b mask records)) := by
  induction records generalizing pre initialRank upper recordBack cloneBack out with
  | nil =>
    let source := pre ++ [false]
    let c := config RecordCell.machine.start width a b initialRank upper recordBack cloneBack mask source pre.length out
    have hread : c.scanned 15 = false := by
      change readTapeBit (pre ++ [false]) pre.length = false
      exact Streaming.read_append pre [] false
    have hstop := StreamController.stop_step RecordCell.machine 15 c hread
    let space := source.length + 104 * width + out.length + 53
    have hstart : (controlConfig (fun _ => test 41) c).tapeCells ≤ space := by
      change (config (test 41) width a b initialRank upper recordBack cloneBack mask source pre.length out).tapeCells ≤ space
      simp only [config_cells]
      dsimp only [space]
      omega
    have hend : (controlConfig (fun _ => stop 41) c).tapeCells ≤ space := hstart
    have hp : Prefix machine space 1 (controlConfig (fun _ => test 41) c) (controlConfig (fun _ => stop 41) c) :=
      Prefix.step hstart (StreamController.test_halted _ _) hstop (Prefix.refl _ hend)
    refine ⟨initialRank, upper, recordBack, cloneBack, hu, hr, hc, ?_⟩
    simpa [stream, fields, bits, source, space, c, controlConfig, config, TapeEmbedding.config, CellEmit.config] using hp
  | cons entry records ih =>
    rcases entry with ⟨word, rank⟩
    have hword : word.length = width := (hrecords (word, rank) (by simp)).1
    have hrank : rank < 2 ^ width := (hrecords (word, rank) (by simp)).2
    have htailRecords : ∀ r ∈ records, r.1.length = width ∧ r.2 < 2 ^ width :=
      fun r hm => hrecords r (by simp [hm])
    let source := pre ++ stream width ((word, rank) :: records)
    let next := pre.length + 4 * width + 1
    let newUpper := frame (binary width (a + b))
    let stored := frame (word ++ binary width rank)
    let appended := out ++ [LeftCell.selected a b rank mask]
    let space := source.length + 104 * width + out.length + (records.length + 1) + 53
    have hstored : stored.length = 4 * width + 1 := by simp [stored, hword]; omega
    have hdouble : 2 * (width + width) = 4 * width := by omega
    have hsource : pre ++ frame (word ++ binary width rank) ++ stream width records = source := by
      simp [source, stream, fields, List.append_assoc]
    obtain ⟨body, hbody, hbf, hbs, hbp⟩ := RecordCell.body_run word a b rank initialRank pre (stream width records)
      upper recordBack cloneBack out mask (by simpa [hword] using hfit) (by simpa [hword] using hrank)
      (by simpa [hword] using hu) (by simpa [hword] using hr) (by simpa [hword] using hc)
    simp only [hword, hsource] at hbody hbf hbs hbp
    obtain ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, tailPrefix⟩ :=
      ih rank (pre ++ frame (word ++ binary width rank)) newUpper stored stored appended htailRecords
        (by simp [newUpper]) hstored.le hstored.le
    have tailPrefix' : Prefix machine space (records.length * (68 * width + 53) + 1)
        (config (test 41) width a b rank newUpper stored stored mask source next appended)
        (config (stop 41) width a b finalRank finalUpper finalRecord finalClone mask source
          (pre.length + (fields width ((word, rank) :: records)).length) (out ++ bits a b mask ((word, rank) :: records))) := by
      convert tailPrefix using 1 <;> simp [space, source, stream, fields, bits, next, newUpper, stored, appended,
        hword, hdouble, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    obtain ⟨bp, halted⟩ := StreamController.body_prefix RecordCell.machine 15 (68 * width + 51) _ body hbody
    have bp' : Prefix machine space body.steps
        (controlConfig code (config RecordCell.machine.start width a b initialRank upper recordBack cloneBack mask source pre.length out))
        (controlConfig code (config (40 : Fin 41) width a b rank newUpper stored stored mask source next appended)) := by
      rw [← hbf]
      exact bp.enlarge (by dsimp only [space]; omega)
    have hend : (config (test 41) width a b rank newUpper stored stored mask source next appended).tapeCells ≤ space := by
      simp only [config_cells, hstored]
      dsimp [space, appended, newUpper]
      simp
      omega
    have hreturn : step machine (controlConfig code
        (config (40 : Fin 41) width a b rank newUpper stored stored mask source next appended)) =
        some (config (test 41) width a b rank newUpper stored stored mask source next appended) := by
      have h := StreamController.return_step RecordCell.machine 15 body.final halted
      rw [hbf] at h
      exact h
    have returned : Prefix machine space (records.length * (68 * width + 53) + 1 + 1)
        (controlConfig code (config (40 : Fin 41) width a b rank newUpper stored stored mask source next appended))
        (config (stop 41) width a b finalRank finalUpper finalRecord finalClone mask source
          (pre.length + (fields width ((word, rank) :: records)).length) (out ++ bits a b mask ((word, rank) :: records))) :=
      Prefix.step hend (StreamController.body_halted _ _ _) hreturn tailPrefix'
    have hread : readTapeBit source pre.length = true := by
      cases word with
      | nil => simp at hword; omega
      | cons bit word =>
        have h := Streaming.read_append pre (bit :: frame (word ++ binary width rank) ++ stream width records) true
        simpa [source, stream, fields, frame, List.append_assoc] using h
    have henter : step machine
        (config (test 41) width a b initialRank upper recordBack cloneBack mask source pre.length out) =
        some (controlConfig code (config RecordCell.machine.start width a b initialRank upper recordBack cloneBack mask source pre.length out)) := by
      exact StreamController.enter_step RecordCell.machine 15
        (config RecordCell.machine.start width a b initialRank upper recordBack cloneBack mask source pre.length out) hread
    have hstart : (config (test 41) width a b initialRank upper recordBack cloneBack mask source pre.length out).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp only [space]
      omega
    have joined := Prefix.step hstart (StreamController.test_halted _ _) henter (bp'.trans returned)
    refine ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, ?_⟩
    have htime : body.steps + (records.length * (68 * width + 53) + 1 + 1) + 1 =
        ((word, rank) :: records).length * (68 * width + 53) + 1 := by
      simp only [List.length_cons, Nat.add_mul]
      omega
    rw [htime] at joined
    exact joined

theorem loop_run (width a b initialRank : ℕ) (records : List Record)
    (pre upper recordBack cloneBack out : List Bool) (mask : Bool) (hw : 0 < width)
    (hfit : a + b < 2 ^ width)
    (hrecords : ∀ r ∈ records, r.1.length = width ∧ r.2 < 2 ^ width)
    (hu : upper.length ≤ 2 * width + 1) (hr : recordBack.length ≤ 4 * width + 1)
    (hc : cloneBack.length ≤ 4 * width + 1) :
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * width + 1 ∧ finalRecord.length ≤ 4 * width + 1 ∧ finalClone.length ≤ 4 * width + 1 ∧
      ∃ r : ExecutionReceipt 16 43,
        runFrom machine (records.length * (68 * width + 53) + 1)
          (config (test 41) width a b initialRank upper recordBack cloneBack mask (pre ++ stream width records) pre.length out) = some r ∧
        r.final = config (stop 41) width a b finalRank finalUpper finalRecord finalClone mask (pre ++ stream width records)
          (pre.length + (fields width records).length) (out ++ bits a b mask records) ∧
        r.steps = records.length * (68 * width + 53) + 1 ∧
        r.peakTapeCells ≤ (pre ++ stream width records).length + 104 * width + out.length + records.length + 53 := by
  obtain ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, hp⟩ :=
    loop_prefix width a b initialRank records pre upper recordBack cloneBack out mask hw hfit hrecords hu hr hc
  refine ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, ?_⟩
  exact hp.run (StreamController.stop_halted _ _) (by simp [bits]; omega)

end NearCubicWires.RepairOrdinary.RecordLoop
