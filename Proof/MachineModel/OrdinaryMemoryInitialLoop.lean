import Proof.MachineModel.OrdinaryMemoryInitialPair
import Proof.Foundations.OrdinaryRewindCarrier

/-! Entire physical initialization stream: two events per framed payload bit,
then one event for its final false delimiter. All counters and source/output
cursors are the actual ones used by the accepted record emitter. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitialLoop
open LocalBitMultitape SignedSortKey
open RecordController (code test stop)
open MemoryInitialCell (config)
open MemoryInitialPair (records)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loop : Machine 9 52 := StreamController.machine MemoryInitialPair.machine 8
def machine : Machine 9 77 := Composition.machine loop MemoryInitialCell.machine
def loopBudget (I K n : ℕ) : ℕ := n*(MemoryInitialPair.budget I K+2)+1
def budget (I K n : ℕ) : ℕ := loopBudget I K n+1+(6*I+6*K+22)

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (body : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control = p.start)
    (hread : c.scanned tape = true) (hbody : runFrom p fuel c = some body)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => test s) body.final) = some tail) :
    ∃ r, runFrom (StreamController.machine p tape) (fuel+tailFuel+2)
      (controlConfig (fun _ => test s) c) = some r ∧ r.final = tail.final := by
  obtain ⟨bodyPrefix, halted⟩ := StreamController.body_prefix p tape fuel c body hbody
  let returned : ExecutionReceipt t (s+2) :=
    ⟨tail.final, tail.steps+1, max body.final.tapeCells tail.peakTapeCells⟩
  have hr : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig code body.final) = some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle, hm, hmf, _, _⟩ := bodyPrefix.followedBy returned hr
  have hrestart : Composition.restart c p.start = c := by
    cases c with
    | mk control heads tapes => cases hc; rfl
  have he := StreamController.enter_step p tape c hread
  rw [hrestart] at he
  let result : ExecutionReceipt t (s+2) :=
    ⟨middle.final, middle.steps+1, max c.tapeCells middle.peakTapeCells⟩
  have hrun : runFrom (StreamController.machine p tape) ((body.steps+(tailFuel+1))+1)
      (controlConfig (fun _ => test s) c) = some result :=
    runFrom_step (StreamController.machine p tape) _ _ middle
      (StreamController.test_halted p tape) he hm
  have hs := runFrom_steps_le p fuel c body hbody
  have hmore := runFrom_moreFuel (StreamController.machine p tape) _ (fuel-body.steps) _ result hrun
  have ht : ((body.steps+(tailFuel+1))+1)+(fuel-body.steps) = fuel+tailFuel+2 := by omega
  rw [ht] at hmore
  exact ⟨result, hmore, hmf⟩

theorem loop_run (I K serial cell cap : ℕ) (out pre bits post : List Bool) (after : Bool)
    (hs : serial+2*bits.length < 2^I) (hk : cell+2*bits.length < 2^K)
    (hI : 2*I+1 ≤ cap) (hK : 2*K+1 ≤ cap) :
    ∃ lastAfter, ∃ r : ExecutionReceipt 9 52,
      runFrom loop (loopBudget I K bits.length)
        (config (test 50) I K serial cell cap out (pre++frame bits++post) pre.length after) = some r ∧
      r.final = config (stop 50) I K (serial+2*bits.length) (cell+2*bits.length) cap
        (out++records I K serial cell (Streaming.marks bits))
        (pre++frame bits++post) (pre.length+2*bits.length) lastAfter := by
  induction bits generalizing serial cell out pre after with
  | nil =>
    let c := config MemoryInitialPair.machine.start I K serial cell cap out (pre++[false]++post) pre.length after
    have hread : c.scanned 8 = false := by
      change readTapeBit (pre++[false]++post) pre.length = false
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        Streaming.read_append pre post false
    let endpoint := controlConfig (fun _ => stop 50) c
    let tail : ExecutionReceipt 9 52 := ⟨endpoint,0,endpoint.tapeCells⟩
    have ht : runFrom loop 0 endpoint = some tail :=
      runFrom_zero_of_halted loop endpoint (StreamController.stop_halted _ _)
    have hr := runFrom_step loop (controlConfig (fun _ => test 50) c) endpoint tail
      (StreamController.test_halted _ _)
      (StreamController.stop_step MemoryInitialPair.machine 8 c hread) ht
    refine ⟨after, ⟨tail.final,tail.steps+1,
      max (controlConfig (fun _ => test 50) c).tapeCells tail.peakTapeCells⟩, ?_, ?_⟩
    · simpa only [loopBudget, List.length_nil, Nat.zero_mul, Nat.zero_add, frame,
        c, controlConfig, config, TapeEmbedding.config, MemoryRecordEmitter.config] using hr
    · simp [tail, endpoint, c, records, Streaming.marks, frame, controlConfig, config,
        TapeEmbedding.config, MemoryRecordEmitter.config]
  | cons b bs ih =>
    let source := pre++frame (b::bs)++post
    let pairOut := out++records I K serial cell [true,b]
    have hfirst : readTapeBit source pre.length = true := by
      dsimp only [source]
      simp only [frame, List.cons_append, List.append_assoc]
      exact Streaming.read_append pre _ true
    have hsecond : readTapeBit source (pre.length+1) = b := by
      have he : source = (pre++[true])++(b::frame bs++post) := by
        simp [source, frame, List.append_assoc]
      rw [he]
      have hl : pre.length+1 = (pre++[true]).length := by simp
      rw [hl]
      exact Streaming.read_append (pre++[true]) _ b
    obtain ⟨body, hb, hbf⟩ := MemoryInitialPair.pair_run I K serial cell cap out source pre.length after
      (by simp only [List.length_cons] at hs; omega)
      (by simp only [List.length_cons] at hk; omega) hI hK
    rw [hfirst, hsecond] at hbf
    have hsource : (pre++[true,b])++frame bs++post = source := by
      simp [source, frame, List.append_assoc]
    have hcursor : (pre++[true,b]).length = pre.length+2 := by simp
    obtain ⟨lastAfter, tail, ht, htf⟩ := ih (serial+2) (cell+2) pairOut (pre++[true,b]) b
      (by simp only [List.length_cons] at hs; omega)
      (by simp only [List.length_cons] at hk; omega)
    rw [hsource, hcursor] at ht htf
    have htail : runFrom loop (loopBudget I K bs.length)
        (controlConfig (fun _ => test 50) body.final) = some tail := by rw [hbf]; exact ht
    obtain ⟨r, hr, hrf⟩ := round_run MemoryInitialPair.machine 8
      (MemoryInitialPair.budget I K) (loopBudget I K bs.length)
      (config MemoryInitialPair.machine.start I K serial cell cap out source pre.length after)
      body tail rfl hfirst hb htail
    have htime : MemoryInitialPair.budget I K+loopBudget I K bs.length+2 =
        loopBudget I K (b::bs).length := by simp only [loopBudget, List.length_cons]; ring
    rw [htime] at hr
    refine ⟨lastAfter, r, hr, ?_⟩
    rw [hrf, htf]
    have hserial : serial+2+2*bs.length = serial+2*(b::bs).length := by simp; omega
    have hcell : cell+2+2*bs.length = cell+2*(b::bs).length := by simp; omega
    have hcursor' : pre.length+2+2*bs.length = pre.length+2*(b::bs).length := by simp; omega
    rw [hserial, hcell, hcursor']
    have hout : pairOut++records I K (serial+2) (cell+2) (Streaming.marks bs) =
        out++records I K serial cell (Streaming.marks (b::bs)) := by
      simp [pairOut, records, Streaming.marks, List.append_assoc, Nat.add_assoc]
    rw [hout]

theorem frame_run (I K serial cell cap : ℕ) (out pre bits post : List Bool) (after : Bool)
    (hs : serial+(frame bits).length < 2^I) (hk : cell+(frame bits).length < 2^K)
    (hI : 2*I+1 ≤ cap) (hK : 2*K+1 ≤ cap) :
    ∃ r : ExecutionReceipt 9 77,
      runFrom machine (budget I K bits.length)
        (config machine.start I K serial cell cap out (pre++frame bits++post) pre.length after) = some r ∧
      r.final = config 76 I K (serial+(frame bits).length) (cell+(frame bits).length) cap
        (out++records I K serial cell (frame bits)) (pre++frame bits++post)
        (pre.length+(frame bits).length) false := by
  obtain ⟨lastAfter, first, hf, hff⟩ := loop_run I K serial cell cap out pre bits post after
    (by simp at hs; omega) (by simp at hk; omega) hI hK
  let nextOut := out++records I K serial cell (Streaming.marks bits)
  have hread : readTapeBit (pre++frame bits++post) (pre.length+2*bits.length) = false := by
    have he : pre++frame bits++post = (pre++Streaming.marks bits)++(false::post) := by
      have he : frame bits = Streaming.marks bits++[false] := by
        simpa only [List.append_nil, frame] using Streaming.frame_append bits []
      rw [he]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [he]
    have hl : pre.length+2*bits.length = (pre++Streaming.marks bits).length := by simp
    rw [hl]
    exact Streaming.read_append _ post false
  obtain ⟨last, hl, hlf⟩ := MemoryInitialCell.cell_run I K (serial+2*bits.length) (cell+2*bits.length)
    cap nextOut (pre++frame bits++post) (pre.length+2*bits.length) lastAfter
    (by simpa only [frame_length, Nat.add_assoc] using hs)
    (by simpa only [frame_length, Nat.add_assoc] using hk) hI hK
  rw [hread] at hlf
  have hi : Composition.restart first.final MemoryInitialCell.machine.start =
      config 0 I K (serial+2*bits.length) (cell+2*bits.length) cap nextOut
        (pre++frame bits++post) (pre.length+2*bits.length) lastAfter := by rw [hff]; rfl
  rw [← hi] at hl
  have hr := Composition.run_join loop MemoryInitialCell.machine (loopBudget I K bits.length)
    (6*I+6*K+22)
    (config (test 50) I K serial cell cap out (pre++frame bits++post) pre.length after)
    first last hf hl
  refine ⟨Composition.joinedReceipt first last, hr, ?_⟩
  simp only [Composition.joinedReceipt, hlf]
  have hout : nextOut++frame (false::false::binary I (serial+2*bits.length)++
        binary K (cell+2*bits.length)) = out++records I K serial cell (frame bits) := by
    have he : frame bits = Streaming.marks bits++[false] := by
      simpa only [List.append_nil, frame] using Streaming.frame_append bits []
    rw [he, MemoryInitialPair.records_append]
    simp [nextOut, records, List.append_assoc]
  rw [hout]
  simp only [frame_length, Nat.add_assoc]
  rfl

end NearCubicWires.RepairOrdinary.MemoryInitialLoop
