import Proof.Hierarchy.CompetitorCountAccumulator
import Proof.PCP.VerifierDecodingRepeat

/-! Whole sequential natural-count accumulation from the native raw matrix
word. The physical unary driver counts cells, and its final rewind is paid.
No division by the number of cells or by child tuples occurs in this loop. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountFold
open LocalBitMultitape RecoveryExecution SignedSortKey CompetitorCountAccumulator
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (b : ℕ) (xs : List ℕ) : List Bool := xs.flatMap (binary b)
def update (s : Store) (w x : ℕ) : Store := accumulated (added (loaded s w x) w x) x
def folded (w : ℕ) : Store → List ℕ → Store
  | s,[] => s
  | s,x::xs => folded w (update s w x) xs
def accepted (_ : Fin 17) (_ : Fin 8 → Bool) : Bool := true
noncomputable def machine := RepeatMachine.machine CompetitorCountAccumulator.machine accepted

theorem raw_cons (b x : ℕ) (xs : List ℕ) : raw b (x::xs)=binary b x++raw b xs := rfl
theorem raw_length (b : ℕ) (xs : List ℕ) : (raw b xs).length=b*xs.length := by
  induction xs with
  | nil => simp [raw]
  | cons x xs ih => simp [raw_cons,ih,Nat.mul_add,Nat.add_comm]

theorem accumulator_folded (w : ℕ) (s : Store) (xs : List ℕ) :
    (folded w s xs).accumulator=s.accumulator+xs.sum := by
  induction xs generalizing s with
  | nil => simp [folded]
  | cons x xs ih =>
    rw [folded,ih]
    simp [update,accumulated,added,loaded]
    omega

theorem repeat_config_eq (phase : Fin 5) (c d : Configuration 8 17) (total head : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) : RepeatMachine.cfg phase c total head=RepeatMachine.cfg phase d total head := by
  apply configuration_ext
  · rfl
  · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem fold_timed (pre suffix : List Bool) (b w : ℕ) (s : Store) (xs : List ℕ)
    (total pos : ℕ) (hn : pos+xs.length=total)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : s.accumulator+xs.sum<2^w)
    (hf : s.field.length≤2*w+1) (hs : s.sum.length≤2*w+1) :
    Timed machine (xs.length*(16*w+19)+total+3)
      (RepeatMachine.cfg 0 (cfg CompetitorCountAccumulator.machine.start s b w (pre++raw b xs++suffix) pre.length) total (pos+1))
      (RepeatMachine.cfg 3 (cfg CompetitorCountAccumulator.machine.start (folded w s xs) b w
        (pre++raw b xs++suffix) (pre.length+b*xs.length)) total 1) := by
  induction xs generalizing pre s pos with
  | nil =>
    have he : pos=total := by simpa using hn
    subst pos
    simpa [machine,folded] using RepeatMachine.exhaust CompetitorCountAccumulator.machine accepted
      (cfg CompetitorCountAccumulator.machine.start s b w (pre++raw b []++suffix) pre.length) total
  | cons x xs ih =>
    have hcell : x+s.accumulator<2^w := by simp only [List.sum_cons] at hfit; omega
    obtain ⟨r,hr,hrh,hrt,hrs⟩ := accumulate_run s pre (raw b xs++suffix) b w x hw
      (hx x (by simp)) hcell hf hs
    have hnpos : pos<total := by simp only [List.length_cons] at hn; omega
    have hi := RepeatMachine.iteration CompetitorCountAccumulator.machine accepted
      (cfg CompetitorCountAccumulator.machine.start s b w (pre++binary b x++(raw b xs++suffix)) pre.length)
      total pos r rfl hnpos hr
    simp only [accepted,if_true,hrs] at hi
    let source := pre++raw b (x::xs)++suffix
    have hsource : (pre++binary b x)++raw b xs++suffix=source := by simp [source,raw_cons,List.append_assoc]
    have hcfg : RepeatMachine.cfg 0 r.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg CompetitorCountAccumulator.machine.start (update s w x) b w
          source (pre.length+b)) total (pos+2) := by
      apply repeat_config_eq
      · exact hrh
      · simpa [cfg,update,source,raw_cons,List.append_assoc] using hrt
    rw [hcfg] at hi
    have hnextfit : (update s w x).accumulator+xs.sum<2^w := by
      simp only [update,accumulated,added,loaded,List.sum_cons] at *
      omega
    have hnextf : (update s w x).field.length≤2*w+1 := by simp [update,accumulated,added,loaded]
    have hnexts : (update s w x).sum.length≤2*w+1 := by simp [update,accumulated,added,loaded]
    have ht := ih (pre++binary b x) (update s w x) (pos+1) (by simp only [List.length_cons] at hn; omega)
      (fun y hy => hx y (by simp [hy])) hnextfit hnextf hnexts
    rw [hsource] at ht
    have hall := hi.trans (by simpa [machine,Nat.add_assoc] using ht)
    convert hall using 1 <;> simp [machine,source,raw_cons,folded,List.append_assoc,Nat.mul_add,Nat.add_mul,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega

theorem count_fold_run (pre suffix : List Bool) (b w : ℕ) (s : Store) (xs : List ℕ)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : s.accumulator+xs.sum<2^w)
    (hf : s.field.length≤2*w+1) (hs : s.sum.length≤2*w+1) :
    ∃ r : ExecutionReceipt 9 (Fintype.card (RepeatMachine.Control 17)),
      runFrom machine (xs.length*(16*w+20)+3)
        (RepeatMachine.cfg 0 (cfg CompetitorCountAccumulator.machine.start s b w
          (pre++raw b xs++suffix) pre.length) xs.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (cfg CompetitorCountAccumulator.machine.start (folded w s xs) b w
        (pre++raw b xs++suffix) (pre.length+b*xs.length)) xs.length 1 ∧
      r.steps=xs.length*(16*w+20)+3 ∧
      (folded w s xs).accumulator=s.accumulator+xs.sum := by
  have hp := fold_timed pre suffix b w s xs xs.length 0 (by omega) hw hx hfit hf hs
  have he : xs.length*(16*w+19)+xs.length+3=xs.length*(16*w+20)+3 := by ring
  rw [he] at hp
  obtain ⟨r,hr,hfinal,hsteps⟩ := hp.run (by simp [machine,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  exact ⟨r,hr,hfinal,hsteps,accumulator_folded w s xs⟩

end NearCubicWires.RepairOrdinary.CompetitorCountFold
