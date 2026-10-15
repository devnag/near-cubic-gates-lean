import Proof.MachineModel.OrdinaryMemoryBody
import Proof.MachineModel.OrdinaryStreamController

/-! Entire actual sorted-memory traversal. Each record costs the accepted
body plus two controller steps; termination costs one step. Space is not
optimized: this consumer needs actual ordinary time and final configurations. -/
namespace NearCubicWires.RepairOrdinary.MemoryLoop
open LocalBitMultitape MemoryLog MemorySort MemoryCompare StablePartition SignedSortKey
open RecordController (code test stop)
open MemoryBody (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Record := ℕ × Event
def word (I W : ℕ) (r : Record) : List Bool := recordBits (encoded I (I+2) W r.1 r.2)
def fields (I W : ℕ) (rs : List Record) : List Bool := rs.flatMap (word I W)
def stream (I W : ℕ) (rs : List Record) : List Bool := fields I W rs ++ [false]
def checks : Event → List Record → List Bool
  | _, [] => []
  | previous, r :: rs => MemoryCheck.passed previous r.2 :: checks r.2 rs
def machine : Machine 14 43 := StreamController.machine MemoryBody.machine 7
def cost (I : ℕ) (rs : List Record) : ℕ := rs.length*(MemoryBody.bodyCost I+2)+1

@[simp] theorem word_length (I W : ℕ) (r : Record) :
    (word I W r).length = 4*(I+2)+1 := by
  simp [word, record_frame]
  omega

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (body : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control = p.start)
    (hread : c.scanned tape = true) (hbody : runFrom p fuel c = some body)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => test s) body.final) = some tail) :
    ∃ r, runFrom (StreamController.machine p tape) (body.steps+tailFuel+2)
      (controlConfig (fun _ => test s) c) = some r ∧
      r.final = tail.final ∧ r.steps = body.steps+tail.steps+2 := by
  obtain ⟨bodyPrefix, halted⟩ := StreamController.body_prefix p tape fuel c body hbody
  let returned : ExecutionReceipt t (s+2) :=
    ⟨tail.final, tail.steps+1, max body.final.tapeCells tail.peakTapeCells⟩
  have hr : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig code body.final) = some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle, hm, hmf, hms, _⟩ := bodyPrefix.followedBy returned hr
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
  refine ⟨result, ?_, hmf, ?_⟩
  · simpa only [Nat.add_assoc] using hrun
  · dsimp only [result, returned] at *
    omega

theorem loop_run (I W : ℕ) (rs : List Record) (previous : Event)
    (pre record clone rank flags : List Bool) (accepted : Bool)
    (hrecord : record.length ≤ 4*(I+2)+1) (hclone : clone.length ≤ 4*(I+2)+1)
    (hrank : rank.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2)) (hap : previous.cell.2 < 2^W)
    (fits : ∀ r ∈ rs, cellCode W r.2.cell < 2^(I+2) ∧ r.2.cell.2 < 2^W)
    (before : ∀ r ∈ rs, cellCode W previous.cell ≤ cellCode W r.2.cell)
    (ordered : rs.Pairwise (fun r s => cellCode W r.2.cell ≤ cellCode W s.2.cell)) :
    ∃ finalEvent finalRecord finalClone finalRank,
      finalRecord.length ≤ 4*(I+2)+1 ∧ finalClone.length ≤ 4*(I+2)+1 ∧
      finalRank.length ≤ 2*(I+2)+1 ∧
      ∃ r : ExecutionReceipt 14 43,
        runFrom machine (cost I rs)
          (config (test 41) I record clone rank (pre ++ stream I W rs) pre.length
            (key I W previous) previous.after flags accepted) = some r ∧
        r.final = config (stop 41) I finalRecord finalClone finalRank
          (pre ++ stream I W rs) (pre.length+(fields I W rs).length)
          (key I W finalEvent) finalEvent.after (flags ++ checks previous rs)
          (accepted && (checks previous rs).all id) ∧ r.steps = cost I rs := by
  induction rs generalizing previous pre record clone rank flags accepted with
  | nil =>
    let c := config MemoryBody.machine.start I record clone rank (pre ++ [false]) pre.length
      (key I W previous) previous.after flags accepted
    have hread : c.scanned 7 = false := by
      change readTapeBit (pre ++ [false]) pre.length = false
      exact Streaming.read_append pre [] false
    let endpoint := controlConfig (fun _ => stop 41) c
    let suffix : ExecutionReceipt 14 43 := ⟨endpoint,0,endpoint.tapeCells⟩
    have ht : runFrom machine 0 endpoint = some suffix :=
      runFrom_zero_of_halted machine endpoint (StreamController.stop_halted _ _)
    let r : ExecutionReceipt 14 43 := ⟨endpoint,1,max c.tapeCells endpoint.tapeCells⟩
    have hr : runFrom machine 1 (controlConfig (fun _ => test 41) c) = some r :=
      runFrom_step machine _ _ suffix (StreamController.test_halted _ _)
        (StreamController.stop_step MemoryBody.machine 7 c hread) ht
    refine ⟨previous, record, clone, rank, hrecord, hclone, hrank, r, ?_, ?_, by simp [r, cost]⟩
    · simpa only [c, cost, stream, fields, List.flatMap_nil, List.nil_append, List.length_nil,
        Nat.zero_mul, Nat.zero_add, controlConfig, MemoryBody.config, MemoryCycle.ready,
        MemoryCycle.config, TapeEmbedding.config] using hr
    · simp [r, endpoint, c, stream, fields, checks, controlConfig, MemoryBody.config,
        MemoryCycle.ready, MemoryCycle.config, TapeEmbedding.config]
  | cons entry rs ih =>
    obtain ⟨hcurrent, haddress⟩ := fits entry (by simp)
    obtain ⟨headOrder, tailOrder⟩ := List.pairwise_cons.mp ordered
    let source := pre ++ stream I W (entry::rs)
    let stored := word I W entry
    let pass := MemoryCheck.passed previous entry.2
    let next := pre.length+4*(I+2)+1
    have hstored : stored.length = 4*(I+2)+1 := word_length I W entry
    have hstoredFrame : stored = frame (front I entry.1 entry.2 ++ key I W entry.2) :=
      record_frame I W entry.1 entry.2
    have hsource : (pre ++ stored) ++ stream I W rs = source := by
      simp [source, stored, stream, fields, List.append_assoc]
    have hnext : (pre ++ stored).length = next := by simp [next, hstored, Nat.add_assoc]
    obtain ⟨body, hb, hbf, hbs⟩ := MemoryBody.body_run I W entry.1 previous entry.2 pre
      (stream I W rs) record clone rank flags accepted hrecord hclone hrank hp hcurrent
      hap haddress (before entry (by simp))
    rw [← hstoredFrame] at hbf
    change runFrom MemoryBody.machine (MemoryBody.bodyCost I)
      (config MemoryBody.machine.start I record clone rank ((pre ++ stored) ++ stream I W rs)
        pre.length (key I W previous) previous.after flags accepted) = some body at hb
    change body.final = config 40 I stored stored (frame (key I W entry.2))
      ((pre ++ stored) ++ stream I W rs) next (key I W entry.2) entry.2.after
      (flags ++ [pass]) (accepted && pass) at hbf
    rw [hsource] at hb hbf
    obtain ⟨finalEvent, finalRecord, finalClone, finalRank, hfr, hfc, hfk, tail, ht, htf, hts⟩ :=
      ih entry.2 (pre ++ stored) stored stored (frame (key I W entry.2))
        (flags ++ [pass]) (accepted && pass) hstored.le hstored.le
        (by simp) hcurrent haddress (fun r hr => fits r (by simp [hr])) headOrder tailOrder
    rw [hsource, hnext] at ht htf
    let c := config MemoryBody.machine.start I record clone rank source pre.length
      (key I W previous) previous.after flags accepted
    have hread : c.scanned 7 = true := by
      change readTapeBit source pre.length = true
      have hword : stored = true :: (encoded I (I+2) W entry.1 entry.2).1 ::
          frame (encoded I (I+2) W entry.1 entry.2).2 := rfl
      rw [← hsource, hword, List.append_assoc]
      exact Streaming.read_append pre _ true
    have ht' : runFrom machine (cost I rs)
        (controlConfig (fun _ => test 41) body.final) = some tail := by
      rw [hbf]
      exact ht
    obtain ⟨result, hresult, hresultFinal, hresultSteps⟩ := round_run MemoryBody.machine 7
      (MemoryBody.bodyCost I) (cost I rs) c body tail rfl hread hb ht'
    have htime : body.steps+cost I rs+2 = cost I (entry::rs) := by
      rw [hbs]
      simp only [cost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    refine ⟨finalEvent, finalRecord, finalClone, finalRank, hfr, hfc, hfk,
      result, ?_, ?_, ?_⟩
    · rw [htime] at hresult
      exact hresult
    · rw [hresultFinal, htf]
      have hfields : next+(fields I W rs).length = pre.length+(fields I W (entry::rs)).length := by
        simp only [fields, List.flatMap_cons, List.length_append]
        change next+(fields I W rs).length = pre.length+(stored.length+(fields I W rs).length)
        rw [hstored]
        dsimp [next]
        omega
      rw [hfields]
      simp [checks, pass, source, List.append_assoc, Bool.and_assoc]
    · rw [hresultSteps, hts]
      exact htime

theorem checks_scan (previous : Event) (rs : List Record) :
    (checks previous rs).all id = MemoryScan.scan previous (rs.map Prod.snd) := by
  induction rs generalizing previous with
  | nil => rfl
  | cons r rs ih =>
    simp only [checks, List.all_cons, id_eq, List.map_cons, MemoryScan.scan,
      MemoryCheck.passed, ih]
    split <;> simp_all

end NearCubicWires.RepairOrdinary.MemoryLoop
