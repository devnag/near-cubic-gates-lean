import Proof.MachineModel.OrdinaryMatrixMaskReplicate

/-! The physical Gates loop expands raw coefficient mask bits into the
original gate/bucket coordinate order. Every zero bit is replicated as
well, and the Buckets/Gates sentinels are returned for reuse. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskExpand
open LocalBitMultitape RecoveryExecution
open MatrixRawBlock (config)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def output (B : ℕ) (bits : List Bool) := bits.flatMap (List.replicate B)
def accepted (_ : Fin 5) (_ : Fin 3 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixMaskReplicate.machine accepted
def budget (B remaining total : ℕ) := remaining*(2*B+6)+total+3

theorem output_length (B : ℕ) (bits : List Bool) : (output B bits).length=bits.length*B := by
  simp [output,List.length_flatMap]

theorem loop_run (B : ℕ) (bits pre suffix out : List Bool) (total done : ℕ) (hcount : done+bits.length=total) : ∃ actual,
    runFrom machine (budget B bits.length total)
      (RepeatMachine.cfg 0 (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1
        (pre++bits++suffix) pre.length out) total (done+1))=some actual ∧
    actual.final=RepeatMachine.cfg 3 (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1
      (pre++bits++suffix) (pre.length+bits.length) (out++output B bits)) total 1 ∧
    actual.steps≤budget B bits.length total := by
  induction bits generalizing done pre out with
  | nil =>
    have hd : done=total := by simpa using hcount
    obtain ⟨actual,ha,hf,hs⟩ := (RepeatMachine.exhaust MatrixMaskReplicate.machine accepted
      (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1 (pre++[]++suffix) pre.length out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [machine,budget,List.length_nil,Nat.zero_mul,Nat.zero_add,hd] using ha
    · simpa only [output,List.flatMap_nil,List.length_nil,Nat.add_zero,List.append_nil] using hf
    · simpa only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons bit bits ih =>
    have hn : done<total := by simp only [List.length_cons] at hcount; omega
    obtain ⟨body,hb,bf,bs⟩ := MatrixMaskReplicate.replicate_run bit pre (bits++suffix) out B
    have iteration := RepeatMachine.iteration MatrixMaskReplicate.machine accepted
      (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1 (pre++bit::(bits++suffix)) pre.length out)
      total done body rfl hn hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final total (done+2)=
        RepeatMachine.cfg 0 (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1
          ((pre++[bit])++bits++suffix) (pre++[bit]).length (out++List.replicate B bit)) total (done+2) := by
      rw [bf]
      simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,config,List.append_assoc]
    rw [hi] at iteration
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++[bit]) (out++List.replicate B bit) (done+1)
      (by simp only [List.length_cons] at hcount; omega)
    have ht' : runFrom machine (budget B bits.length total)
        (RepeatMachine.cfg 0 (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1
          ((pre++[bit])++bits++suffix) (pre++[bit]).length (out++List.replicate B bit)) total (done+2))=some tail := by
      simpa only [Nat.add_assoc] using ht
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,hf,hs,_⟩ := hprefix.followedBy tail ht'
    have hc : body.steps+2+budget B bits.length total=budget B (bit::bits).length total := by
      rw [bs]
      unfold budget
      simp only [List.length_cons]
      ring
    rw [hc] at ha
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [machine,List.append_assoc,List.cons_append] using ha
    · rw [hf,tf]
      simp [output,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
    · rw [hs]
      omega

def padding (count : ℕ) : Fin 4 → ℕ := ![0,0,0,count+2]
noncomputable def cfg (B : ℕ) (bits : List Bool) (phase : Fin 5) (pos : ℕ) (out : List Bool) :=
  ZeroPadding.config (padding bits.length) (RepeatMachine.cfg phase
    (config MatrixMaskReplicate.machine.start (UnaryTemplate.tape B) 1 bits pos out) bits.length 1)
def nativeBudget (B count : ℕ) := count*(2*B+7)+3

theorem cfg_heads (B : ℕ) (bits : List Bool) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (cfg B bits phase pos out).heads=![1,pos,out.length,1] := by
  funext i; fin_cases i <;> rfl

theorem cfg_tapes (B : ℕ) (bits : List Bool) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (cfg B bits phase pos out).tapes=![UnaryTemplate.tape B,bits,out,UnaryTemplate.tape bits.length] := by
  funext i
  fin_cases i <;> simp [cfg,padding,ZeroPadding.config,ZeroPadding.pad,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,config,Fin.addCases,CompareMachine.word,UnaryTemplate.tape]

theorem all_run (B : ℕ) (bits out : List Bool) : ∃ actual,
    runFrom machine (nativeBudget B bits.length) (cfg B bits 0 0 out)=some actual ∧
    actual.final=cfg B bits 3 bits.length (out++output B bits) ∧ actual.steps≤nativeBudget B bits.length := by
  obtain ⟨base,hb,bf,bs⟩ := loop_run B bits [] [] out bits.length 0 (by omega)
  have hc : budget B bits.length bits.length=nativeBudget B bits.length := by unfold budget nativeBudget; ring
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb bf
  rw [hc] at hb bs
  obtain ⟨actual,ha,af,as,_⟩ := ZeroPadding.run_config machine (padding bits.length) _ _ base hb
  exact ⟨actual,ha,by rw [af,bf]; rfl,as.trans_le bs⟩

end NearCubicWires.RepairOrdinary.MatrixMaskExpand
