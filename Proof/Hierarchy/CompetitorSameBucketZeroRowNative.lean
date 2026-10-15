import Proof.Hierarchy.CompetitorSameBucketZeroFinish

/-! The row repeat is docked to its physically present U sentinel and the
retained reference/capacity fields used by the following row reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroRowNative
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorSameBucketZeroFinish (cfg data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 9) : Fin 13:=i.castAdd 4
theorem slots_injective : Function.Injective slots := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)
noncomputable def machine:=RecoveryFocus.machine slots CompetitorSameBucketZeroRow.machine
def padding (u : ℕ) (i : Fin 9):=if i=8 then u+2 else 0
noncomputable def localCfg (phase : Fin 5) (p m u right left cap : ℕ) (out : List Bool):=
  ZeroPadding.config (padding u) (RepeatMachine.cfg phase
    (CompetitorSameBucketZeroCell.cfg CompetitorSameBucketZeroCell.machine.start p m right left cap out) u 1)

theorem local_heads (phase : Fin 5) (p m u right left cap : ℕ) (out : List Bool) :
    (localCfg phase p m u right left cap out).heads=
      Fin.addCases (m := 8) (n := 1) (motive := fun _ => ℕ)
        (fun i : Fin 8 => if i=6 then out.length else 0) (fun _ => 1) := rfl

theorem local_tapes (phase : Fin 5) (p m u right left cap : ℕ) (out : List Bool) :
    (localCfg phase p m u right left cap out).tapes=
      Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool)
        (CompetitorSameBucketZeroCell.cfg CompetitorSameBucketZeroCell.machine.start p m right left cap out).tapes
        (fun _ => UnaryTemplate.tape u) := by
  funext i
  fin_cases i <;> simp [localCfg,ZeroPadding.config,padding,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases,CompareMachine.word,UnaryTemplate.tape,ZeroPadding.pad]

theorem pick_slots (i : Fin 13) : RecoveryFocus.pick slots i=
    (![some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,none,none,none,none] : Fin 13 → Option (Fin 9)) i := by
  fin_cases i
  all_goals first | decide | exact RecoveryFocus.pick_slot slots slots_injective 0 |
    exact RecoveryFocus.pick_slot slots slots_injective 1 | exact RecoveryFocus.pick_slot slots slots_injective 2 |
    exact RecoveryFocus.pick_slot slots slots_injective 3 | exact RecoveryFocus.pick_slot slots slots_injective 4 |
    exact RecoveryFocus.pick_slot slots slots_injective 5 | exact RecoveryFocus.pick_slot slots slots_injective 6 |
    exact RecoveryFocus.pick_slot slots slots_injective 7 | exact RecoveryFocus.pick_slot slots slots_injective 8

theorem row_run (p m u left cap : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hm : 2*m≤cap) (hu : u+u<2^m) :
    ∃ actual,runFrom machine (CompetitorSameBucketZeroRow.budget p m u)
        (cfg machine.start p m u left cap out (ZeroPadding.pad cap (frame (binary m u))))=some actual ∧
      actual.final.heads=heads (out++CompetitorSameBucketZeroRow.bits p m left u u) ∧
      actual.final.tapes=data p m u left cap (out++CompetitorSameBucketZeroRow.bits p m left u u)
        (ZeroPadding.pad cap (frame (binary m (u+u)))) ∧
      actual.steps≤CompetitorSameBucketZeroRow.budget p m u := by
  obtain ⟨base,hb,bs,bf⟩:=CompetitorSameBucketZeroRow.row_run p m left u cap u out hp hm hu
  obtain ⟨native,hn,nf,ns,_⟩:=ZeroPadding.run_config CompetitorSameBucketZeroRow.machine (padding u) _ _ base hb
  let start:=cfg machine.start p m u left cap out (ZeroPadding.pad cap (frame (binary m u)))
  have hi : RecoveryFocus.config slots start.heads start.tapes (localCfg 0 p m u u left cap out)=start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [local_heads]
      fin_cases i <;> rfl
    · intro i
      rw [local_tapes]
      fin_cases i <;> simp [start,cfg,data,slots,Fin.addCases,CompetitorSameBucketZeroCell.cfg,
        CompetitorSameBucketKeyAppend.paddedCfg,CompetitorSameBucketKeyAppend.cfg,
        CompetitorSameBucketKeyAppend.capacities,ZeroPadding.config,Rewind.Workspace.pad_zeros]
  obtain ⟨actual,ha,af,ast⟩:=RecoveryFocus.run_config slots slots_injective CompetitorSameBucketZeroRow.machine
    start.heads start.tapes _ (localCfg 0 p m u u left cap out) native hn
  rw [hi] at ha
  have nf' : native.final=localCfg 3 p m u (u+u) left cap (out++CompetitorSameBucketZeroRow.bits p m left u u) := by
    rw [nf,bf]
    rfl
  refine ⟨actual,ha,?_,?_,ast.trans_le (ns.trans_le bs)⟩
  · rw [af,nf']
    funext i
    simp only [RecoveryFocus.config,pick_slots,local_heads]
    fin_cases i <;> simp [start,cfg,heads,Fin.addCases]
  · rw [af,nf']
    funext i
    simp only [RecoveryFocus.config,pick_slots,local_tapes]
    fin_cases i <;> simp [start,cfg,data,CompetitorSameBucketZeroCell.cfg,
      CompetitorSameBucketKeyAppend.paddedCfg,CompetitorSameBucketKeyAppend.cfg,
      CompetitorSameBucketKeyAppend.capacities,ZeroPadding.config,Fin.addCases,Rewind.Workspace.pad_zeros]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroRowNative
