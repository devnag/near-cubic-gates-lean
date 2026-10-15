import Proof.Hierarchy.CompetitorSameBucketGateReferences

/-! The complete zero grid consumes the two physical unary U templates.
Only the final false cell of the row counter differs from RepeatMachine's
logical counter, and finite zero padding transports the actual run. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGridNative
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CompetitorSameBucketZeroGrid.machine
def padding (u : ℕ) (i : Fin 14):=if i=13 then u+2 else 0
noncomputable def cfg (phase : Fin 5) (p m u left cap : ℕ) (out : List Bool):=
  ZeroPadding.config (padding u) (RepeatMachine.cfg phase
    (CompetitorSameBucketZeroBody.cfg CompetitorSameBucketZeroBody.machine.start p m u left cap out) u 1)
def heads (out : List Bool) : Fin 14 → ℕ :=
  Fin.addCases (m := 13) (n := 1) (motive := fun _ => ℕ)
    (CompetitorSameBucketZeroFinish.heads out) (fun _ => 1)
def data (p m u left cap : ℕ) (out : List Bool) : Fin 14 → List Bool :=
  Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
    (CompetitorSameBucketZeroFinish.data p m u left cap out (ZeroPadding.pad cap (frame (binary m u))))
    (fun _ => UnaryTemplate.tape u)

theorem cfg_heads (phase : Fin 5) (p m u left cap : ℕ) (out : List Bool) :
    (cfg phase p m u left cap out).heads=heads out := rfl

theorem cfg_tapes (phase : Fin 5) (p m u left cap : ℕ) (out : List Bool) :
    (cfg phase p m u left cap out).tapes=data p m u left cap out := by
  funext i
  fin_cases i <;> simp [cfg,ZeroPadding.config,padding,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    data,CompetitorSameBucketZeroBody.cfg,CompetitorSameBucketZeroFinish.cfg,
    Fin.addCases,CompareMachine.word,UnaryTemplate.tape,ZeroPadding.pad]

theorem grid_run (p m u cap : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hc : 4*m+3≤cap) (hu : u+u<2^m) :
    ∃ actual,runFrom machine (CompetitorSameBucketZeroGrid.budget p m u cap u)
        (cfg 0 p m u 0 cap out)=some actual ∧
      actual.final.heads=heads (out++CompetitorSameBucketZeroGrid.bits p m u 0 u) ∧
      actual.final.tapes=data p m u u cap (out++CompetitorSameBucketZeroGrid.bits p m u 0 u) ∧
      actual.steps≤CompetitorSameBucketZeroGrid.budget p m u cap u := by
  obtain ⟨base,hb,bs,bf⟩:=CompetitorSameBucketZeroGrid.grid_run p m u 0 cap u out hp hc hu (by omega)
  obtain ⟨actual,ha,af,ast,_⟩:=ZeroPadding.run_config CompetitorSameBucketZeroGrid.machine (padding u) _ _ base hb
  refine ⟨actual,ha,?_,?_,ast.trans_le bs⟩
  · rw [af,bf]
    exact cfg_heads 3 p m u (0+u) cap (out++CompetitorSameBucketZeroGrid.bits p m u 0 u)
  · rw [af,bf]
    simpa only [cfg,Nat.zero_add] using cfg_tapes 3 p m u (0+u) cap (out++CompetitorSameBucketZeroGrid.bits p m u 0 u)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGridNative
