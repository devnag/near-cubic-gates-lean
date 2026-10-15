import Proof.MachineModel.OrdinaryKeyAdvance

/-! One complete repeatable bucket body: emit all keyed records, rewind only
the source, and advance the framed inner coordinate and lower boundary. -/
namespace NearCubicWires.RepairOrdinary.KeyBucketBody
open LocalBitMultitape SignedSortKey RankBody
open KeyAdvance (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scan : Machine 22 57 := TapeEmbedding.machine 1 KeyReset.machine
def machine : Machine 22 75 := Composition.machine scan KeyAdvance.machine

theorem body_run (S K I inner keyCap resetCap a b initialRank : ℕ) (records : List KeyLoop.Record)
    (upper recordBack cloneBack out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ (K + S + 1)) (hrecords : ∀ r ∈ records, r.2.2 < 2 ^ (K + S + 1))
    (hu : upper.length ≤ 2 * (K + S + 1) + 1) (hr : recordBack.length ≤ 4 * (K + S + 1) + 1)
    (hc : cloneBack.length ≤ 4 * (K + S + 1) + 1) (hci : 2 * I ≤ keyCap) (hck : 2 * K ≤ keyCap)
    (hinner : inner + 1 < 2 ^ I)
    (hreset : records.length * (68 * (K + S + 1) + 4 * (I + K) + 63) + 1 ≤ resetCap) :
    let W := K + S + 1
    let F := records.length * (68 * W + 4 * (I + K) + 63) + 1
    ∃ finalRank finalRecord finalClone,
      finalRecord.length ≤ 4 * W + 1 ∧ finalClone.length ≤ 4 * W + 1 ∧
      Executes machine (2*F + 12*W + 4*I + 19)
        ((KeyLoop.stream S K records).length + out.length + records.length * (2*(I+K)+3) +
          108*W + 8*I + 6*K + keyCap + resetCap + F + 67)
        (config machine.start W a b initialRank upper recordBack cloneBack mask (KeyLoop.stream S K records) out
          K I inner keyCap resetCap)
        (config 74 W (a+b) b finalRank (frame (binary W (a+b))) finalRecord finalClone mask (KeyLoop.stream S K records)
          (out ++ KeyLoop.output K I inner a b mask records) K I (inner+1) keyCap resetCap) := by
  dsimp only
  let W := K + S + 1
  let F := records.length * (68 * W + 4 * (I + K) + 63) + 1
  let source := KeyLoop.stream S K records
  let appended := out ++ KeyLoop.output K I inner a b mask records
  let space := source.length + out.length + records.length * (2*(I+K)+3) +
    108*W + 8*I + 6*K + keyCap + resetCap + F + 67
  obtain ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, first, hrun, hfinal, hsteps, hpeak⟩ :=
    KeyReset.scan_run S K I inner keyCap resetCap a b initialRank records upper recordBack cloneBack out mask
      hfit hrecords hu hr hc hci hck hreset
  let extra := fun _ : Fin 1 => List.replicate (4*W+3) false
  have he := TapeEmbedding.run_embed KeyReset.machine (fun _ : Fin 1 => 0) extra _ _ first hrun
  have firstRun : Executes scan (2*F+2) space
      (config scan.start W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap)
      (config 56 W a b finalRank finalUpper finalRecord finalClone mask source appended K I inner keyCap resetCap) := by
    refine ⟨TapeEmbedding.receipt (fun _ : Fin 1 => 0) extra first, he, ?_, hsteps, ?_⟩
    · change TapeEmbedding.config (fun _ : Fin 1 => 0) extra first.final = _
      rw [hfinal]
      rfl
    · change first.peakTapeCells + TapeEmbedding.extraCells extra ≤ space
      simp only [TapeEmbedding.extraCells, extra, Fin.sum_univ_one, List.length_replicate]
      dsimp only [space, source, F, W]
      omega
  obtain ⟨second, hs, hf, ht, hp⟩ := KeyAdvance.advance_run W a b finalRank finalUpper finalRecord finalClone mask
    source appended K I inner keyCap resetCap hinner hci hfit hfu
  have secondRun : Executes KeyAdvance.machine (12*W+4*I+16) space
      (config KeyAdvance.machine.start W a b finalRank finalUpper finalRecord finalClone mask source appended K I inner keyCap resetCap)
      (config 17 W (a+b) b finalRank (frame (binary W (a+b))) finalRecord finalClone mask source appended K I (inner+1) keyCap resetCap) := by
    refine ⟨second, hs, hf, ht, ?_⟩
    dsimp only [space, appended] at hp ⊢
    simp only [List.length_append, KeyLoop.output_length] at hp
    dsimp only [W] at hp ⊢
    omega
  have joined := firstRun.join secondRun rfl
  have htime : 2*F+2+1+(12*W+4*I+16) = 2*F+12*W+4*I+19 := by omega
  rw [htime] at joined
  exact ⟨finalRank, finalRecord, finalClone, hfr, hfc, joined⟩

end NearCubicWires.RepairOrdinary.KeyBucketBody
