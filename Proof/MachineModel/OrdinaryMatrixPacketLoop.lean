import Proof.MachineModel.OrdinaryMatrixPacketSignPair

/-! The actual retained p-sentinel executes every remaining sign pair.
The append stream is never rewound between packets. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch RepairRepresentation
open RepairSource.VerifierDecoding
open MatrixPacketState (State)
open private cfg_eq from Proof.PCP.VerifierDecodingRepeat
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def appendPackets (r : Request) : ℕ → ℕ → List Bool → List Bool
  | _,0,out => out
  | bit,k+1,out => appendPackets r (bit+1) k (out++MatrixPacketSignPair.wordPair r bit)
def accepted {t s : ℕ} (_ : Fin s) (_ : Fin t → Bool) := true
noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) :=
  RepeatMachine.machine (MatrixPacketSignPair.machine a E) accepted
def bodyBudget (r : Request) (cap : ℕ) := 6*cap+16*(word r).length+8*r.p+47
def budget (r : Request) (cap remaining : ℕ) := remaining*(bodyBudget r cap+2)+r.p+3

theorem loop_run (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (remaining bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) (hcount : bit+remaining=r.p)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤cap) :
    ∃ final : State a E cap r r.p (appendPackets r bit remaining out),∃ actual,
      runFrom (machine a E) (budget r cap remaining)
        (RepeatMachine.cfg 0 (MatrixPacketSignPair.input a E cap r bit out st) r.p (bit+1))=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (MatrixPacketSignPair.input a E cap r r.p (appendPackets r bit remaining out) final) r.p 1 ∧
      actual.steps≤budget r cap remaining := by
  induction remaining generalizing bit out st with
  | zero =>
    have he : bit=r.p := by omega
    subst bit
    obtain ⟨actual,ha,hf,hs⟩ := (RepeatMachine.exhaust (MatrixPacketSignPair.machine a E) accepted
      (MatrixPacketSignPair.input a E cap r r.p out st) r.p).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    have hz : budget r cap 0=r.p+3 := by unfold budget; omega
    refine ⟨st,actual,?_,hf,?_⟩
    · rw [hz]
      exact ha
    · rw [hz]
      exact hs.le
  | succ remaining ih =>
    have ht : bit<r.p := by omega
    obtain ⟨next,body,hb,bh,bt,bs⟩ := MatrixPacketSignPair.pair_run a E cap r bit out st ht (hcap bit ht)
    have bbound : body.steps≤bodyBudget r cap := bs.trans (MatrixPacketSignPair.budget_bound a r bit cap ht (hcap bit ht))
    have iteration := RepeatMachine.iteration (MatrixPacketSignPair.machine a E) accepted
      (MatrixPacketSignPair.input a E cap r bit out st) r.p bit body rfl ht hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final r.p (bit+2)=
        RepeatMachine.cfg 0 (MatrixPacketSignPair.input a E cap r (bit+1)
          (out++MatrixPacketSignPair.wordPair r bit) next) r.p (bit+2) :=
      cfg_eq 0 body.final (MatrixPacketSignPair.input a E cap r (bit+1)
        (out++MatrixPacketSignPair.wordPair r bit) next) r.p (bit+2) bh bt
    rw [hi] at iteration
    obtain ⟨final,tail,htail,tf,ts⟩ := ih (bit+1) (out++MatrixPacketSignPair.wordPair r bit) next (by omega)
    have htail' : runFrom (machine a E) (budget r cap remaining)
        (RepeatMachine.cfg 0 (MatrixPacketSignPair.input a E cap r (bit+1)
          (out++MatrixPacketSignPair.wordPair r bit) next) r.p (bit+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have hsmall : body.steps+2+budget r cap remaining≤budget r cap (remaining+1) := by
      unfold budget
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel (machine a E) _
      (budget r cap (remaining+1)-(body.steps+2+budget r cap remaining)) _ actual ha
    rw [Nat.add_sub_of_le hsmall] at more
    refine ⟨final,actual,more,hf.trans tf,?_⟩
    rw [hs]
    omega

end NearCubicWires.RepairOrdinary.MatrixPacketLoop
