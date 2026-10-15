import Proof.Hierarchy.CompetitorSameBucketGateScan

/-! A second pass of the existing bucket counter returns the local packet
cursor. Each iteration uses the already retained B/H drivers for B ranked
fields; no new count driver and no global source rewind is introduced. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPacketReturn
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 50 := ![43,42,45]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def body := RecoveryFocus.machine slots MatrixRankRowReverse.machine
def localCfg {s : ℕ} (q : Fin s) (pos outPos : ℕ) (ambient : Fin 50 → List Bool) : Configuration 50 s :=
  ⟨q,CompetitorSameBucketBucketPrepare.heads pos outPos,ambient⟩
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 50 → Bool) := true
noncomputable def machine := RepeatMachine.machine body accepted
def budget (h b n : ℕ) := n*(MatrixRankRowReverse.budget h b+3)+3
def tapes (ambient : Fin 50 → List Bool) (n : ℕ) : Fin 51 → List Bool :=
  Fin.addCases (m := 50) (n := 1) (motive := fun _ => List Bool) ambient (fun _ => UnaryTemplate.tape n)
def cfg {s : ℕ} (q : Fin s) (pos outPos n : ℕ) (ambient : Fin 50 → List Bool) : Configuration 51 s :=
  ⟨q,CompetitorSameBucketGateScan.heads pos outPos,tapes ambient n⟩

theorem body_run (h b pos outPos : ℕ) (ambient : Fin 50 → List Bool)
    (hH : ambient 42=UnaryTemplate.tape h) (hB : ambient 45=UnaryTemplate.tape b) :
    ∃ actual,runFrom body (MatrixRankRowReverse.budget h b) (localCfg body.start pos outPos ambient)=some actual ∧
      actual.steps≤MatrixRankRowReverse.budget h b ∧
      actual.final.heads=CompetitorSameBucketBucketPrepare.heads (pos-b*(4*h+1)) outPos ∧ actual.final.tapes=ambient := by
  obtain ⟨base,hb,bs,bf⟩ := MatrixRankRowReverse.row_run (ambient 43) h b pos
  let entry := localCfg body.start pos outPos ambient
  have hi : RecoveryFocus.config slots entry.heads entry.tapes (MatrixRankRowReverse.cfg 0 (ambient 43) h b pos)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [MatrixRankRowReverse.cfg_heads]; fin_cases i <;> rfl
    · intro i; rw [MatrixRankRowReverse.cfg_tapes]; fin_cases i <;> first | exact hH | exact hB | rfl
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config slots slots_injective MatrixRankRowReverse.machine entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  have pick43 : RecoveryFocus.pick slots 43=some 0 := RecoveryFocus.pick_slot slots slots_injective 0
  refine ⟨actual,hr,hs.trans_le bs,?_,?_⟩
  · rw [hf,bf]
    funext i
    cases he : RecoveryFocus.pick slots i with
    | none =>
      have hn : i≠43 := by intro hh; subst i; rw [pick43] at he; contradiction
      simp [RecoveryFocus.config,he,entry,localCfg,CompetitorSameBucketBucketPrepare.heads,hn]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots he
      simp only [RecoveryFocus.config,he]
      rw [←hj]
      fin_cases j <;> simp [MatrixRankRowReverse.cfg_heads,slots,CompetitorSameBucketBucketPrepare.heads,MatrixRankFieldReverse.distance]
  · rw [hf,bf]
    funext i
    cases he : RecoveryFocus.pick slots i with
    | none => simp [RecoveryFocus.config,he,entry,localCfg]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots he
      simp only [RecoveryFocus.config,he]
      rw [←hj]
      fin_cases j <;> simp [MatrixRankRowReverse.cfg_tapes,slots,hH,hB]

theorem pad_cfg (phase : Fin 5) (pos outPos n : ℕ) (ambient : Fin 50 → List Bool) :
    ZeroPadding.config (CompetitorSameBucketGateScan.capacities n)
      (RepeatMachine.cfg phase (localCfg body.start pos outPos ambient) n 1)=
      cfg (RepeatMachine.cfg phase (localCfg body.start pos outPos ambient) n 1).control pos outPos n ambient := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,CompetitorSameBucketGateScan.capacities,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      localCfg,cfg,tapes,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem return_run (h b n pos outPos : ℕ) (ambient : Fin 50 → List Bool)
    (hH : ambient 42=UnaryTemplate.tape h) (hB : ambient 45=UnaryTemplate.tape b) :
    ∃ actual,runFrom machine (budget h b n) (cfg machine.start pos outPos n ambient)=some actual ∧
      actual.steps≤budget h b n ∧ actual.final.heads=CompetitorSameBucketGateScan.heads (pos-n*(b*(4*h+1))) outPos ∧
      actual.final.tapes=tapes ambient n := by
  let state := fun p => localCfg body.start p outPos ambient
  let next := fun p : ℕ => (true,p-b*(4*h+1))
  obtain ⟨base,hb,bs,bf⟩ := RepeatMachine.repeat_run body accepted state next (fun _ => True)
    (MatrixRankRowReverse.budget h b) (by intros; rfl)
    (by
      intro p _
      obtain ⟨actual,ha,ast,ah,atapes⟩ := body_run h b p outPos ambient hH hB
      exact ⟨actual,ha,ast,ah,atapes,rfl,by intros; trivial⟩) n pos trivial
  have hfinal : base.final=RepeatMachine.cfg 3 (state (pos-n*(b*(4*h+1)))) n 1 := by
    simpa only [RepeatMachine.Result,next,MatrixRankRowReverse.iterate_sub,ite_true] using bf
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (CompetitorSameBucketGateScan.capacities n) _ _ base hb
  change runFrom machine (budget h b n) (ZeroPadding.config _ (RepeatMachine.cfg 0 (localCfg body.start pos outPos ambient) n 1))=some actual at ha
  rw [pad_cfg] at ha
  refine ⟨actual,ha,hs.trans_le bs,?_,?_⟩
  · rw [hf,hfinal]
    change (ZeroPadding.config _ (RepeatMachine.cfg 3 (localCfg body.start _ outPos ambient) n 1)).heads=_
    rw [pad_cfg]
    rfl
  · rw [hf,hfinal]
    change (ZeroPadding.config _ (RepeatMachine.cfg 3 (localCfg body.start _ outPos ambient) n 1)).tapes=_
    rw [pad_cfg]
    rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPacketReturn
