import Proof.MachineModel.OrdinaryKeyCellLayout

/-! Actual annotated-record loading, signed-cell computation and coordinate
record emission on one fixed twenty-tape machine. -/
namespace NearCubicWires.RepairOrdinary.KeyCell
open LocalBitMultitape SignedSortKey Streaming RankBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem key_run (W a b rank : ℕ) (upper idBits recordTail clone : List Bool) (mask : Bool)
    (source : List Bool) (pos : ℕ) (out : List Bool) (I inner cap : ℕ)
    (hci : 2 * I ≤ cap) (hck : 2 * idBits.length ≤ cap) :
    Executes key (4 * (I + idBits.length) + 7)
      (source.length + out.length + upper.length + (marks idBits ++ recordTail).length + clone.length +
        52 * W + 8 * I + 6 * idBits.length + cap + 35)
      (config 0 W a b rank upper (marks idBits ++ recordTail) clone mask source pos out idBits.length I inner cap)
      (config 9 W a b rank upper (marks idBits ++ recordTail) clone mask source pos
        (out ++ frame (binary I inner ++ idBits)) idBits.length I inner cap) := by
  obtain ⟨r, hr, hf, hs, hp⟩ := KeyPair.pair_run (binary I inner) [false] (binary I 0)
    idBits recordTail (binary idBits.length 0) out cap (by simp) (by simp) (by simpa using hci) hck
  have hframe : marks (binary I inner) ++ [false] = frame (binary I inner) := marks_frame _
  rw [hframe] at hr hf hp
  let heads := keyHeads pos
  let tapes := keyTapes W a b rank upper clone mask source
  have he := TapeEmbedding.run_embed KeyPair.machine heads tapes _ _ r hr
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 14 KeyPair.machine) _ _ _ he
  refine ⟨TapeRenaming.receipt layout (TapeEmbedding.receipt heads tapes r), ?_, ?_, ?_, ?_⟩
  · simpa only [heads, tapes, place_key, key, binary_length] using hn
  · change TapeRenaming.config layout (TapeEmbedding.config heads tapes r.final) = _
    rw [hf]
    exact place_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · change r.steps ≤ _
    simpa only [binary_length] using hs
  · change r.peakTapeCells + TapeEmbedding.extraCells tapes ≤ _
    dsimp only [tapes]
    rw [key_cells]
    simp only [frame_length, binary_length] at hp
    omega

theorem cell_run (word : List Bool) (a b rank oldRank : ℕ) (pre suffix upper record clone out : List Bool)
    (mask : Bool) (K I inner cap : ℕ) (hfit : a + b < 2 ^ word.length) (hrank : rank < 2 ^ word.length)
    (hu : upper.length ≤ 2 * word.length + 1) (hr : record.length ≤ 4 * word.length + 1)
    (hc : clone.length ≤ 4 * word.length + 1) :
    Executes cell (68 * word.length + 51)
      ((pre ++ frame (word ++ binary word.length rank) ++ suffix).length + 104 * word.length +
        out.length + 2 * K + 4 * I + cap + 56)
      (config 0 word.length a b oldRank upper record clone mask
        (pre ++ frame (word ++ binary word.length rank) ++ suffix) pre.length out K I inner cap)
      (config 40 word.length a b rank (frame (binary word.length (a + b)))
        (frame (word ++ binary word.length rank)) (frame (word ++ binary word.length rank)) mask
        (pre ++ frame (word ++ binary word.length rank) ++ suffix) (pre.length + 4 * word.length + 1)
        (out ++ [LeftCell.selected a b rank mask]) K I inner cap) := by
  obtain ⟨r, hrun, hf, hs, hp⟩ := RecordCell.body_run word a b rank oldRank pre suffix upper record clone out mask hfit hrank hu hr hc
  have he := TapeEmbedding.run_embed RecordCell.machine (fun _ : Fin 4 => 0) (extraTapes K I inner cap) _ _ r hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4 => 0) (extraTapes K I inner cap) r, ?_, ?_, hs.le, ?_⟩
  · exact he
  · change TapeEmbedding.config _ _ r.final = _
    rw [hf]
    rfl
  · change r.peakTapeCells + TapeEmbedding.extraCells (extraTapes K I inner cap) ≤ _
    rw [extra_cells]
    omega

theorem body_run (S K I inner cap id : ℕ) (score : ℤ) (a b rank oldRank : ℕ)
    (pre suffix upper record clone out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ (K + S + 1)) (hrank : rank < 2 ^ (K + S + 1))
    (hu : upper.length ≤ 2 * (K + S + 1) + 1) (hr : record.length ≤ 4 * (K + S + 1) + 1)
    (hc : clone.length ≤ 4 * (K + S + 1) + 1) (hci : 2 * I ≤ cap) (hck : 2 * K ≤ cap) :
    let W := K + S + 1
    let word := RadixSemantics.word (encode S K score id)
    let source := pre ++ frame (word ++ binary W rank) ++ suffix
    Executes machine (68 * W + 4 * (I + K) + 61)
      (source.length + 104 * W + 8 * I + 6 * K + out.length + cap + 64)
      (config 0 W a b oldRank upper record clone mask source pre.length out K I inner cap)
      (config 52 W a b rank (frame (binary W (a + b))) (frame (word ++ binary W rank))
        (frame (word ++ binary W rank)) mask source (pre.length + 4 * W + 1)
        (out ++ frame (LeftCell.selected a b rank mask :: (binary I inner ++ binary K id))) K I inner cap) := by
  let W := K + S + 1
  let word := RadixSemantics.word (encode S K score id)
  let stored := frame (word ++ binary W rank)
  let source := pre ++ stored ++ suffix
  let space := source.length + 104 * W + 8 * I + 6 * K + out.length + cap + 64
  let next := pre.length + 4 * W + 1
  let selected := LeftCell.selected a b rank mask
  let upper' := frame (binary W (a + b))
  have hw : word.length = W := encode_width _ _ _ _
  have hstored : stored.length = 4 * W + 1 := by simp [stored, hw]; omega
  have hp : Executes mark 1 space
      (config 0 W a b oldRank upper record clone mask source pre.length out K I inner cap)
      (config 1 W a b oldRank upper record clone mask source pre.length (out ++ [true]) K I inner cap) := by
    obtain ⟨r, hr, hf, hs, hb⟩ := mark_run W a b oldRank upper record clone mask source pre.length out K I inner cap
    refine ⟨r, hr, hf, hs, ?_⟩
    dsimp only [space, W] at *
    omega
  have hq : Executes cell (68 * W + 51) space
      (config 0 W a b oldRank upper record clone mask source pre.length (out ++ [true]) K I inner cap)
      (config 40 W a b rank upper' stored stored mask source next (out ++ [true, selected]) K I inner cap) := by
    obtain ⟨r, hr', hf, hs, hb⟩ := cell_run word a b rank oldRank pre suffix upper record clone (out ++ [true]) mask
      K I inner cap (by simpa only [hw] using hfit) (by simpa only [hw] using hrank)
        (by simpa only [hw] using hu) (by simpa only [hw] using hr) (by simpa only [hw] using hc)
    simp only [hw] at hr' hf hs hb
    refine ⟨r, hr', ?_, hs, ?_⟩
    · simpa only [upper', stored, source, next, selected, List.append_assoc, List.cons_append, List.nil_append] using hf
    · dsimp only [space, source, stored]
      simp only [List.length_append, List.length_cons, List.length_nil] at hb ⊢
      omega
  let recordTail := frame (binary (S + 1) (shifted S score) ++ binary W rank)
  have hrecord : marks (binary K id) ++ recordTail = stored := by
    dsimp only [stored, word, recordTail]
    simp only [encode_word, List.append_assoc, frame_append]
  have hk : Executes key (4 * (I + K) + 7) space
      (config 0 W a b rank upper' stored stored mask source next (out ++ [true, selected]) K I inner cap)
      (config 9 W a b rank upper' stored stored mask source next
        (out ++ [true, selected] ++ frame (binary I inner ++ binary K id)) K I inner cap) := by
    obtain ⟨r, hr', hf, hs, hb⟩ := key_run W a b rank upper' (binary K id) recordTail stored mask source next
      (out ++ [true, selected]) I inner cap hci (by simpa using hck)
    rw [hrecord] at hr' hf hb
    simp only [binary_length] at hr' hf hs hb
    refine ⟨r, hr', hf, hs, ?_⟩
    dsimp only [space, upper'] at hb ⊢
    simp only [List.length_append, List.length_cons, List.length_nil, frame_length, binary_length, hstored] at hb ⊢
    omega
  have htail := hq.join hk rfl
  have hj := hp.join htail rfl
  have he : 1 + 1 + ((68 * W + 51) + 1 + (4 * (I + K) + 7)) = 68 * W + 4 * (I + K) + 61 := by omega
  rw [he] at hj
  have hzero : Fin.castAdd 51 (0 : Fin 2) = (0 : Fin 53) := by decide
  have hlast : Fin.natAdd 2 (Fin.natAdd 41 (9 : Fin 10)) = (52 : Fin 53) := by decide
  have ho : out ++ [true, selected] ++ frame (binary I inner ++ binary K id) =
      out ++ frame (selected :: (binary I inner ++ binary K id)) := by simp [frame, List.append_assoc]
  simpa only [ho, machine, tail, Composition.leftConfig, Composition.rightConfig, config,
    RecordCell.config, CellEmit.config, TapeEmbedding.config, hzero, hlast,
    W, word, stored, source, space, next, selected, upper'] using hj

end NearCubicWires.RepairOrdinary.KeyCell
