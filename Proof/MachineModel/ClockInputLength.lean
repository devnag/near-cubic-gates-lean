import Proof.MachineModel.ClockBinary
import Proof.MachineModel.OrdinaryStreamController
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! Count a literal framed input with a dynamically growing binary counter.
The input is retained and every carry, head reset and stream advance is paid. -/
namespace NearCubicWires.RepairOrdinary.ClockInputLength
open LocalBitMultitape
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (bits : List Bool) (cap : ℕ)
    (source : List Bool) (position : ℕ) : Configuration 3 s :=
  ⟨state, ![0,0,position], ![frame bits,List.replicate cap false,source]⟩
@[simp] theorem config_cells {s : ℕ} (state : Fin s) (bits : List Bool) (cap : ℕ)
    (source : List Bool) (position : ℕ) :
    (config state bits cap source position).tapeCells = 2*bits.length+1+cap+source.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

def increment : Machine 3 7 := TapeEmbedding.machine 1 ClockIncrement.machine

def advance : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state _ => if state.val = 0 then
      some ⟨1, fun _ => none, fun i => if i.val = 2 then .right else .stay⟩
    else if state.val = 1 then
      some ⟨2, fun _ => none, fun i => if i.val = 2 then .right else .stay⟩
    else none

def body : Machine 3 10 := Composition.machine increment advance
def machine : Machine 3 12 := StreamController.machine body 2

theorem advance_run (bits : List Bool) (cap : ℕ) (source : List Bool) (position : ℕ) :
    ∃ r : ExecutionReceipt 3 3,
      runFrom advance 2 (config 0 bits cap source position) = some r ∧
      r.final = config 2 bits cap source (position+2) ∧ r.steps = 2 := by
  have h0 : step advance (config 0 bits cap source position) =
      some (config 1 bits cap source (position+1)) := by
    simp [step, advance, config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have h1 : step advance (config 1 bits cap source (position+1)) =
      some (config 2 bits cap source (position+2)) := by
    simp [step, advance, config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨r, hr, hf, ht, _⟩ :=
    (Prefix.step (Nat.le_refl _) (by rfl : advance.halted (0 : Fin 3) = false) h0
      (Prefix.step (by simp) (by rfl : advance.halted (1 : Fin 3) = false) h1
        (Prefix.refl _ (by simp)))).run (by rfl) (by simp)
  exact ⟨r, hr, hf, ht⟩

theorem body_run (bits : List Bool) (cap : ℕ) (source : List Bool) (position : ℕ) :
    ∃ r : ExecutionReceipt 3 10,
      runFrom body (2*ClockIncrement.work bits+5) (config 0 bits cap source position) = some r ∧
      r.final = config 9 (ClockIncrement.next bits) (max cap (ClockIncrement.work bits)) source (position+2) ∧
      r.steps = 2*ClockIncrement.work bits+5 := by
  obtain ⟨base, hb, hbits, hcap, hh, hsteps, _⟩ := ClockIncrement.increment_run bits cap
  have hhalt := (prefix_of_run ClockIncrement.machine _ _ base hb).2
  have hcontrol : base.final.control = 6 := by
    have he : ∀ s : Fin 7, ClockIncrement.machine.halted s = true → s=6 := by
      intro s
      fin_cases s <;> simp [ClockIncrement.machine, Rewind.machine, Fin.addCases]
    exact he _ hhalt
  let c := initialConfiguration ClockIncrement.machine
    (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame bits) (fun _ : Fin 1 => List.replicate cap false))
  let heads := fun _ : Fin 1 => position
  let tapes := fun _ : Fin 1 => source
  let r := TapeEmbedding.receipt heads tapes base
  have hr := TapeEmbedding.run_embed ClockIncrement.machine heads tapes _ c base hb
  have hi : TapeEmbedding.config heads tapes c = config 0 bits cap source position := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have hf : r.final = config 6 (ClockIncrement.next bits) (max cap (ClockIncrement.work bits)) source position := by
    apply configuration_ext
    · exact hcontrol
    · funext i; fin_cases i <;> simp [r, TapeEmbedding.receipt, TapeEmbedding.config, config, heads, hh, Fin.addCases]
    · funext i; fin_cases i <;> simp [r, TapeEmbedding.receipt, TapeEmbedding.config, config, tapes, hbits, hcap, Fin.addCases]
  rw [hi] at hr
  obtain ⟨last, hl, hlf, hls⟩ := advance_run (ClockIncrement.next bits) (max cap (ClockIncrement.work bits)) source position
  have hl' : runFrom advance 2 (Composition.restart r.final advance.start) = some last := by
    rw [hf]
    exact hl
  have hj := Composition.run_join increment advance (2*ClockIncrement.work bits+2) 2 _ r last hr hl'
  refine ⟨Composition.joinedReceipt r last, ?_, ?_, ?_⟩
  · simpa [body, Composition.leftConfig, config, Nat.add_assoc] using hj
  · rw [Composition.joinedReceipt, hlf]
    rfl
  · simp only [Composition.joinedReceipt, r, TapeEmbedding.receipt, hsteps, hls]

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control = p.start)
    (hread : c.scanned tape = true) (hr : runFrom p fuel c = some r)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => test s) r.final) = some tail) :
    ∃ result, runFrom (StreamController.machine p tape) (r.steps+tailFuel+2)
      (controlConfig (fun _ => test s) c) = some result ∧
      result.final = tail.final ∧ result.steps = r.steps+tail.steps+2 := by
  obtain ⟨segment, halted⟩ := StreamController.body_prefix p tape fuel c r hr
  let returned : ExecutionReceipt t (s+2) :=
    ⟨tail.final, tail.steps+1, max r.final.tapeCells tail.peakTapeCells⟩
  have hreturn : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig code r.final) = some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle, hm, hmf, hms, _⟩ := segment.followedBy returned hreturn
  have hrestart : Composition.restart c p.start = c := by
    cases c with
    | mk control heads tapes => cases hc; rfl
  have he := StreamController.enter_step p tape c hread
  rw [hrestart] at he
  let result : ExecutionReceipt t (s+2) :=
    ⟨middle.final, middle.steps+1, max c.tapeCells middle.peakTapeCells⟩
  have hrun : runFrom (StreamController.machine p tape) ((r.steps+(tailFuel+1))+1)
      (controlConfig (fun _ => test s) c) = some result :=
    runFrom_step (StreamController.machine p tape) _ _ middle
      (StreamController.test_halted p tape) he hm
  refine ⟨result, ?_, hmf, ?_⟩
  · simpa only [Nat.add_assoc] using hrun
  · dsimp only [result, returned] at *
    omega

def cost (N : ℕ) (bits : List Bool) : ℕ := bits.length*(4*PCPResourceLedger.ell N+13)+1

theorem loop_run (N n cap : ℕ) (pre bits suffix : List Bool)
    (hbound : n+bits.length≤N) (hcap : cap≤2*PCPResourceLedger.ell N+3) :
    ∃ finalCap, finalCap≤2*PCPResourceLedger.ell N+3 ∧
      ∃ r : ExecutionReceipt 3 12,
        runFrom machine (cost N bits)
          (config (test 10) (ClockBinary.word n) cap (pre++frame bits++suffix) pre.length) = some r ∧
        r.final = config (stop 10) (ClockBinary.word (n+bits.length)) finalCap
          (pre++frame bits++suffix) (pre.length+2*bits.length) ∧ r.steps≤cost N bits := by
  induction bits generalizing n cap pre with
  | nil =>
    let c := config body.start (ClockBinary.word n) cap (pre++frame []++suffix) pre.length
    have hread : c.scanned 2 = false := by
      change readTapeBit (pre++frame []++suffix) pre.length = false
      simpa [frame, List.append_assoc] using Streaming.read_append pre suffix false
    let final := controlConfig (fun _ => stop 10) c
    let tail : ExecutionReceipt 3 12 := ⟨final,0,final.tapeCells⟩
    have ht : runFrom machine 0 final = some tail :=
      runFrom_zero_of_halted machine final (StreamController.stop_halted _ _)
    let r : ExecutionReceipt 3 12 := ⟨final,1,max c.tapeCells final.tapeCells⟩
    have hr : runFrom machine 1 (controlConfig (fun _ => test 10) c) = some r :=
      runFrom_step machine _ _ tail (StreamController.test_halted _ _)
        (StreamController.stop_step body 2 c hread) ht
    exact ⟨cap,hcap,r,by simpa [cost, c, config, controlConfig] using hr,
      by simp [r, final, c, config, controlConfig], by simp [r,cost]⟩
  | cons bit bits ih =>
    let source := pre++frame (bit::bits)++suffix
    let w := ClockIncrement.work (ClockBinary.word n)
    have hw : w≤2*PCPResourceLedger.ell N+3 := ClockBinary.work_bound n N (by simp at hbound; omega)
    obtain ⟨br, hb, hbf, hbs⟩ := body_run (ClockBinary.word n) cap source pre.length
    obtain ⟨finalCap, hfinalCap, tail, ht, htf, hts⟩ :=
      ih (n+1) (max cap w) (pre++[true,bit]) (by simp at hbound; omega) (max_le hcap hw)
    have hsource : (pre++[true,bit])++frame bits++suffix = source := by
      simp [source, frame, List.append_assoc]
    have hpos : (pre++[true,bit]).length = pre.length+2 := by simp
    rw [hsource,hpos] at ht htf
    let c := config body.start (ClockBinary.word n) cap source pre.length
    have hread : c.scanned 2 = true := by
      change readTapeBit source pre.length = true
      simpa [source, frame, List.append_assoc] using Streaming.read_append pre (bit::frame bits++suffix) true
    have ht' : runFrom machine (cost N bits)
        (controlConfig (fun _ => test 10) br.final) = some tail := by
      rw [hbf]
      exact ht
    obtain ⟨r, hr, hrf, hrs⟩ := round_run body 2 (2*w+5) (cost N bits) c br tail rfl hread hb ht'
    have htime : br.steps+cost N bits+2 ≤ cost N (bit::bits) := by
      rw [hbs]
      simp only [cost, List.length_cons, Nat.add_mul, Nat.one_mul]
      change 2*w+5+_+2 ≤ _
      omega
    have hmore := runFrom_moreFuel machine (br.steps+cost N bits+2)
      (cost N (bit::bits)-(br.steps+cost N bits+2)) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨finalCap,hfinalCap,r,hmore,?_,?_⟩
    · rw [hrf,htf]
      simp [source, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add]
    · rw [hrs]
      omega

end NearCubicWires.RepairOrdinary.ClockInputLength
