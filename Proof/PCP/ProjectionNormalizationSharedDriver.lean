import Proof.PCP.ProjectionNormalizationSuffixRestore
import Proof.MachineModel.OrdinaryStreamController

namespace NearCubicWires.RepairSource.ProjectionNormalization.SharedDriverProbe
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev size := 2+ProbeReuse.size
def cfg {s : ℕ} (q : Fin s) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap count driver : ℕ) :=
  TapeEmbedding.config (fun _ : Fin 1 => driver) (fun _ => CompareMachine.word count)
    (ProbeReuse.cfg q left right lp rp eq found cap)
def advance : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=5 then .right else .stay⟩ else none
noncomputable def probe := TapeEmbedding.machine 1 ClauseProbe.machine
noncomputable def machine := Composition.machine advance probe
noncomputable def finalCode : Fin size := ProbeReuse.finalCode.natAdd 2

theorem advance_run (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap count driver : ℕ) :
    ∃ r,runFrom advance 1 (cfg 0 left right lp rp eq found cap count driver)=some r ∧
      r.final=cfg 1 left right lp rp eq found cap count (driver+1) ∧ r.steps=1 := by
  have h : step advance (cfg 0 left right lp rp eq found cap count driver)=
      some (cfg 1 left right lp rp eq found cap count (driver+1)) := by
    simp [step,advance,cfg,TapeEmbedding.config,ProbeReuse.cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,Fin.addCases,HeadMove.apply]
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem probe_run (left right : SuffixScan.Clause) (candidatePrefix pre tail : List Bool)
    (eq found : Bool) (cap count driver : ℕ) (hcap : ClauseProbe.budget left right ≤ cap) :
    ∃ r,runFrom machine (2*ClauseProbe.budget left right+4)
      (cfg machine.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length pre.length eq found cap count driver)=some r ∧
      r.steps ≤ 2*ClauseProbe.budget left right+4 ∧
      r.final=cfg finalCode (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length (pre.length+(ClauseEquality.stream right).length) (decide (left=right))
        (found||decide (left=right)) cap count (driver+1) := by
  classical
  obtain ⟨a,ha,haf,hat⟩ := advance_run (candidatePrefix++ClauseEquality.stream left)
    (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found cap count driver
  obtain ⟨base,hb,hbs,hbf⟩ := ProbeReuse.probe_run left right candidatePrefix pre tail eq found cap hcap
  have hp := TapeEmbedding.run_embed ClauseProbe.machine (fun _ : Fin 1 => driver+1)
    (fun _ => CompareMachine.word count) _ _ base hb
  let b := TapeEmbedding.receipt (fun _ : Fin 1 => driver+1) (fun _ => CompareMachine.word count) base
  have hmid : Composition.restart a.final probe.start=
      cfg probe.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length pre.length eq found cap count (driver+1) := by rw [haf]; rfl
  change runFrom probe _ (cfg probe.start _ _ _ _ _ _ _ _ _)=some b at hp
  rw [←hmid] at hp
  have hall := Composition.run_join advance probe _ _ _ a b ha hp
  have ht : 1+1+(2*ClauseProbe.budget left right+2)=2*ClauseProbe.budget left right+4 := by omega
  rw [ht] at hall
  refine ⟨Composition.joinedReceipt a b,hall,?_,?_⟩
  · change a.steps+1+base.steps ≤ _
    omega
  · change Composition.rightConfig 2 (TapeEmbedding.config _ _ base.final)=_
    rw [hbf]
    rfl

end NearCubicWires.RepairSource.ProjectionNormalization.SharedDriverProbe
