import Proof.MachineModel.OrdinaryMatrixCoefficientBitCanonical

/-! A literal gate-count loop reads every coefficient frame and emits one
raw signed mask bit per gate, including zeros. Source/output cursors stream,
the byte offset is reused, and only one outer return is needed. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open MatrixCoefficientBitLeaf (cfg)
open MatrixCoefficientBitCanonical (signMatch value)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def output (negative : Bool) (t : ℕ) (zs : List ℤ) := zs.map (value negative t)
def finalFlag (negative flag : Bool) (zs : List ℤ) := zs.foldl (fun _ z => signMatch negative z) flag
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 4 → Bool) := true
noncomputable def machine (negative : Bool) := RepeatMachine.machine (MatrixCoefficientBitBody.machine negative) accepted
def budget (p remaining total : ℕ) := remaining*(MatrixCoefficientBitCanonical.budget p+2)+total+3

theorem loop_run (negative flag : Bool) (p t : ℕ) (ht : t<p) (zs : List ℤ)
    (pre suffix out : List Bool) (total done : ℕ) (hcount : done+zs.length=total) : ∃ actual,
    runFrom (machine negative) (budget p zs.length total)
      (RepeatMachine.cfg 0 (cfg (MatrixCoefficientBitBody.machine negative).start
        (pre++MatrixScoreCanonical.fields p zs++suffix) pre.length (2*t) flag out) total (done+1))=some actual ∧
    actual.final=RepeatMachine.cfg 3 (cfg (MatrixCoefficientBitBody.machine negative).start
      (pre++MatrixScoreCanonical.fields p zs++suffix) (pre.length+(MatrixScoreCanonical.fields p zs).length)
      (2*t) (finalFlag negative flag zs) (out++output negative t zs)) total 1 ∧
    actual.steps≤budget p zs.length total := by
  induction zs generalizing flag done pre out with
  | nil =>
    have hd : done=total := by simpa using hcount
    obtain ⟨actual,ha,hf,hs⟩ := (RepeatMachine.exhaust (MatrixCoefficientBitBody.machine negative) accepted
      (cfg (MatrixCoefficientBitBody.machine negative).start (pre++MatrixScoreCanonical.fields p []++suffix)
        pre.length (2*t) flag out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [machine,budget,List.length_nil,Nat.zero_mul,Nat.zero_add,hd] using ha
    · simpa only [output,finalFlag,List.map_nil,List.foldl_nil,MatrixScoreCanonical.fields,
        List.flatMap_nil,List.length_nil,Nat.add_zero,List.append_nil] using hf
    · simpa only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons z zs ih =>
    have hn : done<total := by simp only [List.length_cons] at hcount; omega
    obtain ⟨body,hb,bf,bs⟩ := MatrixCoefficientBitCanonical.bit_run negative flag p t ht z pre
      (MatrixScoreCanonical.fields p zs++suffix) out
    have iteration := RepeatMachine.iteration (MatrixCoefficientBitBody.machine negative) accepted
      (cfg (MatrixCoefficientBitBody.machine negative).start
        (pre++frame (signMagnitude p z)++(MatrixScoreCanonical.fields p zs++suffix)) pre.length (2*t) flag out)
      total done body rfl hn hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final total (done+2)=
        RepeatMachine.cfg 0 (cfg (MatrixCoefficientBitBody.machine negative).start
          ((pre++frame (signMagnitude p z))++MatrixScoreCanonical.fields p zs++suffix)
          (pre++frame (signMagnitude p z)).length (2*t) (signMatch negative z)
          (out++[value negative t z])) total (done+2) := by
      rw [bf]
      simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,List.append_assoc,List.length_append]
    rw [hi] at iteration
    obtain ⟨tail,hrt,tf,ts⟩ := ih (signMatch negative z) (pre++frame (signMagnitude p z))
      (out++[value negative t z]) (done+1) (by simp only [List.length_cons] at hcount; omega)
    have hrt' : runFrom (machine negative) (budget p zs.length total)
        (RepeatMachine.cfg 0 (cfg (MatrixCoefficientBitBody.machine negative).start
          ((pre++frame (signMagnitude p z))++MatrixScoreCanonical.fields p zs++suffix)
          (pre++frame (signMagnitude p z)).length (2*t) (signMatch negative z)
          (out++[value negative t z])) total (done+2))=some tail := by
      simpa only [Nat.add_assoc] using hrt
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,hf,hs,_⟩ := hprefix.followedBy tail hrt'
    have hsmall : body.steps+2+budget p zs.length total≤budget p (z::zs).length total := by
      unfold budget
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have he := runFrom_moreFuel (machine negative) _
      (budget p (z::zs).length total-(body.steps+2+budget p zs.length total)) _ actual ha
    rw [Nat.add_sub_of_le hsmall] at he
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [MatrixScoreCanonical.fields,List.flatMap_cons,List.append_assoc] using he
    · rw [hf,tf]
      simp only [output,finalFlag,List.map_cons,List.foldl_cons,MatrixScoreCanonical.fields,List.flatMap_cons,
        List.length_append,List.append_assoc,List.singleton_append,Nat.add_assoc]
    · rw [hs]
      omega

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitLoop
