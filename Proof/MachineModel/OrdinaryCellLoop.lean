import Proof.MachineModel.OrdinaryStreamController

/-! A whole bucket's cell scan over a framed rank stream. The fixed program
loads each rank, computes and appends its bit, and retains bounded workspace
for the next record. Production of this rank stream is a separate caller. -/
namespace NearCubicWires.RepairOrdinary.CellLoop
open LocalBitMultitape SignedSortKey
open CellLoad (config)
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (width : ℕ) (ranks : List ℕ) : List Bool := ranks.flatMap (fun rank => frame (binary width rank))
def stream (width : ℕ) (ranks : List ℕ) : List Bool := fields width ranks ++ [false]
def bits (a b : ℕ) (mask : Bool) (ranks : List ℕ) : List Bool := ranks.map (fun rank => LeftCell.selected a b rank mask)
def machine : Machine 10 26 := StreamController.machine CellLoad.machine 9

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (width a b rank : ℕ) (backing : List Bool)
    (mask : Bool) (source : List Bool) (position : ℕ) (out : List Bool) :
    (config state width a b rank backing mask source position out).tapeCells =
      source.length + out.length + backing.length + 14 * width + 12 := by
  simp [config, TapeEmbedding.config, CellEmit.config, LocalCell.input, LocalCell.raw,
    Configuration.tapeCells, Fin.sum_univ_succ, Fin.addCases]
  omega

theorem loop_prefix (width a b initialRank : ℕ) (ranks : List ℕ) (pre backing out : List Bool) (mask : Bool)
    (hw : 0 < width) (hfit : a + b < 2 ^ width) (hranks : ∀ rank ∈ ranks, rank < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) :
    ∃ finalRank finalBacking, finalBacking.length ≤ 2 * width + 1 ∧
      Prefix machine ((pre ++ stream width ranks).length + 26 * width + out.length + ranks.length + 22)
        (ranks.length * (16 * width + 22) + 1)
        (config (test 24) width a b initialRank backing mask (pre ++ stream width ranks) pre.length out)
        (config (stop 24) width a b finalRank finalBacking mask (pre ++ stream width ranks)
          (pre.length + (fields width ranks).length) (out ++ bits a b mask ranks)) := by
  induction ranks generalizing pre initialRank backing out with
  | nil =>
    let source := pre ++ [false]
    let c := config CellLoad.machine.start width a b initialRank backing mask source pre.length out
    have hread : c.scanned 9 = false := by
      change readTapeBit (pre ++ [false]) pre.length = false
      exact Streaming.read_append pre [] false
    have hstop := StreamController.stop_step CellLoad.machine 9 c hread
    let space := source.length + 26 * width + out.length + 22
    have hc : (controlConfig (fun _ => test 24) c).tapeCells ≤ space := by
      change (config (test 24) width a b initialRank backing mask source pre.length out).tapeCells ≤ space
      simp only [config_cells]
      dsimp only [space]
      omega
    have hd : (controlConfig (fun _ => stop 24) c).tapeCells ≤ space := hc
    have hp : Prefix machine space 1 (controlConfig (fun _ => test 24) c) (controlConfig (fun _ => stop 24) c) :=
      Prefix.step hc (StreamController.test_halted _ _) hstop (Prefix.refl _ hd)
    refine ⟨initialRank, backing, hb, ?_⟩
    simpa [stream, fields, bits, source, space, c, controlConfig, config, TapeEmbedding.config, CellEmit.config] using hp
  | cons rank ranks ih =>
    have hrank : rank < 2 ^ width := hranks rank (by simp)
    have htailRanks : ∀ r ∈ ranks, r < 2 ^ width := fun r hm => hranks r (by simp [hm])
    let source := pre ++ stream width (rank :: ranks)
    let next := pre.length + 2 * width + 1
    let upper := frame (binary width (a + b))
    let appended := out ++ [LeftCell.selected a b rank mask]
    let space := source.length + 26 * width + out.length + (ranks.length + 1) + 22
    have hsource : pre ++ frame (binary width rank) ++ stream width ranks = source := by
      simp [source, stream, fields, List.append_assoc]
    obtain ⟨body, hbody, hbf, hbs, hbp⟩ := CellLoad.body_run width a b rank initialRank pre
      (stream width ranks) backing out mask hfit hrank hb
    rw [hsource] at hbody hbf hbp
    obtain ⟨finalRank, finalBacking, hback, tailPrefix⟩ := ih rank (pre ++ frame (binary width rank))
      upper appended htailRanks (by simp [upper])
    have tailPrefix' : Prefix machine space (ranks.length * (16 * width + 22) + 1)
        (config (test 24) width a b rank upper mask source next appended)
        (config (stop 24) width a b finalRank finalBacking mask source
          (pre.length + (fields width (rank :: ranks)).length) (out ++ bits a b mask (rank :: ranks))) := by
      convert tailPrefix using 1 <;> simp [space, source, stream, fields, bits, next, upper, appended,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    obtain ⟨bp, halted⟩ := StreamController.body_prefix CellLoad.machine 9 (16 * width + 20) _ body hbody
    have bp' : Prefix machine space body.steps
        (controlConfig code (config CellLoad.machine.start width a b initialRank backing mask source pre.length out))
        (controlConfig code (config (23 : Fin 24) width a b rank upper mask source next appended)) := by
      rw [← hbf]
      exact bp.enlarge (by dsimp only [space]; omega)
    have hend : (config (test 24) width a b rank upper mask source next appended).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp [space, appended, upper]
      simp
      omega
    have hreturn : step machine (controlConfig code
        (config (23 : Fin 24) width a b rank upper mask source next appended)) =
        some (config (test 24) width a b rank upper mask source next appended) := by
      have h := StreamController.return_step CellLoad.machine 9 body.final halted
      rw [hbf] at h
      exact h
    have returned : Prefix machine space (ranks.length * (16 * width + 22) + 1 + 1)
        (controlConfig code (config (23 : Fin 24) width a b rank upper mask source next appended))
        (config (stop 24) width a b finalRank finalBacking mask source
          (pre.length + (fields width (rank :: ranks)).length) (out ++ bits a b mask (rank :: ranks))) :=
      Prefix.step hend (StreamController.body_halted _ _ _) hreturn tailPrefix'
    have hread : readTapeBit source pre.length = true := by
      cases width with
      | zero => omega
      | succ w =>
        have h := Streaming.read_append pre ((rank % 2 == 1) :: frame (binary w (rank / 2)) ++ stream (w + 1) ranks) true
        simpa [source, stream, fields, binary, frame, List.append_assoc] using h
    have henter : step machine (config (test 24) width a b initialRank backing mask source pre.length out) =
        some (controlConfig code (config CellLoad.machine.start width a b initialRank backing mask source pre.length out)) := by
      exact StreamController.enter_step CellLoad.machine 9
        (config CellLoad.machine.start width a b initialRank backing mask source pre.length out) hread
    have hstart : (config (test 24) width a b initialRank backing mask source pre.length out).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp only [space]
      omega
    have joined := Prefix.step hstart (StreamController.test_halted _ _) henter (bp'.trans returned)
    refine ⟨finalRank, finalBacking, hback, ?_⟩
    have htime : body.steps + (ranks.length * (16 * width + 22) + 1 + 1) + 1 =
        (rank :: ranks).length * (16 * width + 22) + 1 := by
      simp only [List.length_cons, Nat.add_mul]
      omega
    rw [htime] at joined
    exact joined

theorem loop_run (width a b initialRank : ℕ) (ranks : List ℕ) (pre backing out : List Bool) (mask : Bool)
    (hw : 0 < width) (hfit : a + b < 2 ^ width) (hranks : ∀ rank ∈ ranks, rank < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) :
    ∃ finalRank finalBacking, finalBacking.length ≤ 2 * width + 1 ∧
      ∃ r : ExecutionReceipt 10 26,
        runFrom machine (ranks.length * (16 * width + 22) + 1)
          (config (test 24) width a b initialRank backing mask (pre ++ stream width ranks) pre.length out) = some r ∧
        r.final = config (stop 24) width a b finalRank finalBacking mask (pre ++ stream width ranks)
          (pre.length + (fields width ranks).length) (out ++ bits a b mask ranks) ∧
        r.steps = ranks.length * (16 * width + 22) + 1 ∧
        r.peakTapeCells ≤ (pre ++ stream width ranks).length + 26 * width + out.length + ranks.length + 22 := by
  obtain ⟨finalRank, finalBacking, hback, hp⟩ := loop_prefix width a b initialRank ranks pre backing out mask hw hfit hranks hb
  refine ⟨finalRank, finalBacking, hback, ?_⟩
  exact hp.run (StreamController.stop_halted _ _) (by simp [bits]; omega)

end NearCubicWires.RepairOrdinary.CellLoop
