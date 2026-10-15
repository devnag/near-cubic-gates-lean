import Proof.MachineModel.OrdinaryKeyBucketBody

/-! Actual counted traversal of consecutive buckets of one dominance table.
Both labels advance, local storage is reused, and output grows sequentially. -/
namespace NearCubicWires.RepairOrdinary.KeyBucketLoop
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def family : Bool → Machine 22 75 := fun _ => KeyBucketBody.machine
def machine : Machine 23 154 := UnaryController.machine family
def output (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) : ℕ → List Bool
  | 0 => []
  | n+1 => KeyLoop.output K I inner a b mask records ++ output K I (inner+1) (a+b) b mask records n
@[simp] theorem output_length (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) (count : ℕ) :
    (output K I inner a b mask records count).length = count * (records.length * (2*(I+K)+3)) := by
  induction count generalizing inner a with
  | zero => simp [output]
  | succ count ih => simp [output, ih, Nat.add_mul, Nat.add_comm]

def config {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap head count : ℕ) : Configuration 23 s :=
  TapeEmbedding.config (fun _ : Fin 1 => head) (fun _ : Fin 1 => UnaryTemplate.tape count)
    (KeyAdvance.config state W a b rank upper record clone mask source out K I inner keyCap resetCap)
theorem config_cells {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap head count : ℕ) :
    (config state W a b rank upper record clone mask source out K I inner keyCap resetCap head count).tapeCells =
      source.length + out.length + upper.length + record.length + clone.length +
        56*W + 2*K + 4*I + keyCap + resetCap + count + 39 := by
  simp only [config, KeyAdvance.config, KeyReset.config, TapeEmbedding.config_cells,
    KeyCell.config_cells, TapeEmbedding.extraCells, Fin.sum_univ_one, List.length_replicate, UnaryTemplate.tape_length]
  omega

theorem loop_prefix (S K I keyCap resetCap b : ℕ) (records : List KeyLoop.Record) (mask : Bool)
    (hrecords : ∀ r ∈ records, r.2.2 < 2 ^ (K+S+1)) (hci : 2*I ≤ keyCap) (hck : 2*K ≤ keyCap)
    (hreset : records.length * (68*(K+S+1)+4*(I+K)+63)+1 ≤ resetCap)
    (count remaining processed inner a initialRank : ℕ) (phase : Bool)
    (upper recordBack cloneBack out : List Bool)
    (hcount : processed+remaining = count) (hinner : inner+remaining < 2^I)
    (hfit : a+remaining*b < 2^(K+S+1))
    (hu : upper.length ≤ 2*(K+S+1)+1) (hr : recordBack.length ≤ 4*(K+S+1)+1) (hc : cloneBack.length ≤ 4*(K+S+1)+1) :
    let W := K+S+1
    let F := records.length * (68*W+4*(I+K)+63)+1
    let G := 2*F+12*W+4*I+21
    ∃ finalPhase finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2*W+1 ∧ finalRecord.length ≤ 4*W+1 ∧ finalClone.length ≤ 4*W+1 ∧
      ∃ steps, steps ≤ remaining*G+1 ∧
      Prefix machine ((KeyLoop.stream S K records).length + out.length + remaining*(records.length*(2*(I+K)+3)) +
        108*W+8*I+6*K+keyCap+resetCap+F+count+69) steps
        (config (UnaryController.test (s := 75) phase) W a b initialRank upper recordBack cloneBack mask
          (KeyLoop.stream S K records) out K I inner keyCap resetCap (processed+1) count)
        (config (UnaryController.stop (s := 75) finalPhase) W (a+remaining*b) b finalRank finalUpper finalRecord finalClone mask
          (KeyLoop.stream S K records) (out ++ output K I inner a b mask records remaining)
          K I (inner+remaining) keyCap resetCap (count+1) count) := by
  dsimp only
  let W := K+S+1
  let F := records.length * (68*W+4*(I+K)+63)+1
  let G := 2*F+12*W+4*I+21
  let source := KeyLoop.stream S K records
  induction remaining generalizing processed inner a initialRank phase upper recordBack cloneBack out with
  | zero =>
    have he : processed = count := by simpa using hcount
    subst processed
    let core := KeyAdvance.config KeyBucketBody.machine.start W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap
    have hs := UnaryController.stop_step family phase core.heads core.tapes (count+1) (UnaryTemplate.tape count) (UnaryTemplate.tape_end count)
    change step machine (config (UnaryController.test (s := 75) phase) W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap (count+1) count) =
      some (config (UnaryController.stop (s := 75) phase) W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap (count+1) count) at hs
    let space := source.length+out.length+108*W+8*I+6*K+keyCap+resetCap+F+count+69
    have hb : (config (UnaryController.test (s := 75) phase) W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap (count+1) count).tapeCells ≤ space := by
      rw [config_cells]
      dsimp only [space, W]
      omega
    have ht : (config (UnaryController.stop (s := 75) phase) W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap (count+1) count).tapeCells ≤ space := hb
    have hp := Prefix.step hb (UnaryController.test_halted _ _) hs (Prefix.refl _ ht)
    refine ⟨phase, initialRank, upper, recordBack, cloneBack, hu, hr, hc, 1, by simp, ?_⟩
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, output, List.append_nil, space, W, F, source, machine] using hp
  | succ remaining ih =>
    let appended := out ++ KeyLoop.output K I inner a b mask records
    let space := source.length+out.length+(remaining+1)*(records.length*(2*(I+K)+3))+
      108*W+8*I+6*K+keyCap+resetCap+F+count+69
    have hbodyFit : a+b < 2^W := by
      have hm : b ≤ (remaining+1)*b := Nat.le_mul_of_pos_left _ (by omega)
      exact lt_of_le_of_lt (by omega) hfit
    have hbodyInner : inner+1 < 2^I := by omega
    obtain ⟨nextRank, nextRecord, nextClone, hnr, hnc, body, hbody, hbf, hbs, hbp⟩ :=
      KeyBucketBody.body_run S K I inner keyCap resetCap a b initialRank records upper recordBack cloneBack out mask
        hbodyFit hrecords hu hr hc hci hck hbodyInner hreset
    let nextUpper := frame (binary W (a+b))
    have hnu : nextUpper.length ≤ 2*W+1 := by simp [nextUpper]
    have hnextFit : a+b+remaining*b < 2^W := by
      have he : a+b+remaining*b = a+(remaining+1)*b := by ring
      rw [he]
      exact hfit
    obtain ⟨finalPhase, finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, tailSteps, htailSteps, tailPrefix⟩ :=
      ih (processed+1) (inner+1) (a+b) nextRank (!phase) nextUpper nextRecord nextClone appended
        (by omega) (by omega) hnextFit hnu hnr hnc
    have ht : Prefix machine space tailSteps
        (config (UnaryController.test (s := 75) (!phase)) W (a+b) b nextRank nextUpper nextRecord nextClone mask source appended
          K I (inner+1) keyCap resetCap (processed+2) count)
        (config (UnaryController.stop (s := 75) finalPhase) W (a+(remaining+1)*b) b finalRank finalUpper finalRecord finalClone mask source
          (out ++ output K I inner a b mask records (remaining+1)) K I (inner+(remaining+1)) keyCap resetCap (count+1) count) := by
      have hspace : source.length+appended.length+remaining*(records.length*(2*(I+K)+3))+
          108*W+8*I+6*K+keyCap+resetCap+F+count+69 = space := by
        simp only [appended, List.length_append, KeyLoop.output_length, space, Nat.add_mul]
        omega
      have he : a+b+remaining*b = a+(remaining+1)*b := by ring
      have ho : appended ++ output K I (inner+1) (a+b) b mask records remaining = out ++ output K I inner a b mask records (remaining+1) := by
        simp only [appended, output, List.append_assoc]
      change Prefix machine _ _ _ _ at tailPrefix
      rw [hspace, he, ho] at tailPrefix
      simpa only [Nat.add_assoc, Nat.add_comm 1 remaining, W, source] using tailPrefix
    obtain ⟨bp, halted⟩ := UnaryController.body_prefix family phase _ _ body hbody (processed+2) (UnaryTemplate.tape count)
    have bp' : Prefix machine space body.steps
        (controlConfig (UnaryController.code (s := 75) phase) (config KeyBucketBody.machine.start W a b initialRank upper recordBack cloneBack mask source out
          K I inner keyCap resetCap (processed+2) count))
        (controlConfig (UnaryController.code (s := 75) phase) (config (74 : Fin 75) W (a+b) b nextRank nextUpper nextRecord nextClone mask source appended
          K I (inner+1) keyCap resetCap (processed+2) count)) := by
      have h := bp.enlarge (large := space) (by
        rw [UnaryTemplate.tape_length]
        have hm : records.length*(2*(I+K)+3) ≤ (remaining+1)*(records.length*(2*(I+K)+3)) := Nat.le_mul_of_pos_left _ (by omega)
        dsimp only [space, source, F, W]
        omega)
      rw [hbf] at h
      exact h
    have hbEnd : (controlConfig (UnaryController.code (s := 75) phase)
        (config (74 : Fin 75) W (a+b) b nextRank nextUpper nextRecord nextClone mask source appended K I (inner+1) keyCap resetCap (processed+2) count)).tapeCells ≤ space := by
      change (config (74 : Fin 75) W (a+b) b nextRank nextUpper nextRecord nextClone mask source appended K I (inner+1) keyCap resetCap (processed+2) count).tapeCells ≤ space
      rw [config_cells]
      dsimp only [space, appended]
      simp only [List.length_append, KeyLoop.output_length, Nat.add_mul]
      dsimp only [W] at hnu ⊢
      omega
    have hreturn : step machine
        (controlConfig (UnaryController.code (s := 75) phase) (config (74 : Fin 75) W (a+b) b nextRank nextUpper nextRecord nextClone mask source appended
          K I (inner+1) keyCap resetCap (processed+2) count)) =
        some (config (UnaryController.test (s := 75) (!phase)) W (a+b) b nextRank nextUpper nextRecord nextClone mask source appended
          K I (inner+1) keyCap resetCap (processed+2) count) := by
      have h := UnaryController.return_step family phase body.final (processed+2) (UnaryTemplate.tape count) halted
      rw [hbf] at h
      exact h
    have returned := Prefix.step hbEnd (UnaryController.body_halted _ _ _) hreturn ht
    let core := KeyAdvance.config KeyBucketBody.machine.start W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap
    have henter : step machine
        (config (UnaryController.test (s := 75) phase) W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap (processed+1) count) =
        some (controlConfig (UnaryController.code (s := 75) phase) (config KeyBucketBody.machine.start W a b initialRank upper recordBack cloneBack mask source out
          K I inner keyCap resetCap (processed+2) count)) :=
      UnaryController.enter_step family phase core.heads core.tapes (processed+1) (UnaryTemplate.tape count)
        (UnaryTemplate.tape_mark count processed (by omega))
    have hbStart : (config (UnaryController.test (s := 75) phase) W a b initialRank upper recordBack cloneBack mask source out K I inner keyCap resetCap (processed+1) count).tapeCells ≤ space := by
      rw [config_cells]
      dsimp only [space, W]
      omega
    have joined := Prefix.step hbStart (UnaryController.test_halted _ _) henter (bp'.trans returned)
    refine ⟨finalPhase, finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, body.steps+(tailSteps+1)+1, ?_, joined⟩
    simp only [Nat.add_mul]
    omega

end NearCubicWires.RepairOrdinary.KeyBucketLoop
