import Proof.Hierarchy.CompetitorSameBucketZeroPrepareCopies

/-! Complete19-tape zero-grid appender from five retained reference fields
and blank local work. Allocation, copying, both counter advances, all U²
key emissions, and every increment/reset are executed and charged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGridCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorSameBucketZeroPrepareCopies (initialized)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 14 → Fin 19 := ![6,7,8,9,10,11,5,12,0,1,4,13,14,17]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def grid:=RecoveryFocus.machine slots CompetitorSameBucketZeroGridNative.machine

def advances (i : Fin 19):Prop:=i=0 ∨ i=17
instance (i : Fin 19) : Decidable (advances i):=inferInstanceAs (Decidable (i=0 ∨ i=17))
def advance : Machine 19 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if advances i then .right else .stay⟩ else none
def advanced {s : ℕ} (c : Configuration 19 s) : Configuration 19 2 :=
  ⟨1,fun i=>if advances i then c.heads i+1 else c.heads i,c.tapes⟩
theorem advance_run {s : ℕ} (c : Configuration 19 s) : ∃ actual,
    runFrom advance 1 (Composition.restart c advance.start)=some actual ∧ actual.final=advanced c ∧ actual.steps=1 := by
  have h : step advance (Composition.restart c advance.start)=some (advanced c) := by
    simp only [step,advance,Composition.restart]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : advances i <;> simp [applyAction,advanced,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) h).run (by rfl)

def heads (out : List Bool) (i : Fin 19):=if advances i then 1 else if i=5 then out.length else 0
def result (p m u cap : ℕ) (out log : List Bool):=
  Function.update (initialized p m u cap out log) 10 (ZeroPadding.pad cap (frame (binary m u)))
def cfg {s : ℕ} (q : Fin s) (p m u cap : ℕ) (out log : List Bool) : Configuration 19 s :=
  ⟨q,heads out,initialized p m u cap out log⟩

theorem selected (p m u cap : ℕ) (out log : List Bool) :
    (∀ j,heads out (slots j)=CompetitorSameBucketZeroGridNative.heads out j) ∧
    (∀ j,initialized p m u cap out log (slots j)=CompetitorSameBucketZeroGridNative.data p m u 0 cap out j) := by
  constructor
  · intro j; fin_cases j <;> rfl
  · intro j
    fin_cases j <;> simp [initialized,slots,CompetitorSameBucketZeroGridNative.data,Fin.addCases,
      CompetitorSameBucketZeroFinish.data,MatrixScoreBatch.signMagnitude,RankCarrier.binary_zero,List.replicate_succ]

private theorem pick_slots (i : Fin 19) : RecoveryFocus.pick slots i=
    (![some 8,some 9,none,none,some 10,some 6,some 0,some 1,some 2,some 3,some 4,some 5,
      some 7,some 11,some 12,none,none,some 13,none] : Fin 19 → Option (Fin 14)) i := by
  fin_cases i
  all_goals first | decide | exact RecoveryFocus.pick_slot slots slots_injective 0 | exact RecoveryFocus.pick_slot slots slots_injective 1 | exact RecoveryFocus.pick_slot slots slots_injective 2 | exact RecoveryFocus.pick_slot slots slots_injective 3 | exact RecoveryFocus.pick_slot slots slots_injective 4 | exact RecoveryFocus.pick_slot slots slots_injective 5 | exact RecoveryFocus.pick_slot slots slots_injective 6 | exact RecoveryFocus.pick_slot slots slots_injective 7 | exact RecoveryFocus.pick_slot slots slots_injective 8 | exact RecoveryFocus.pick_slot slots slots_injective 9 | exact RecoveryFocus.pick_slot slots slots_injective 10 | exact RecoveryFocus.pick_slot slots slots_injective 11 | exact RecoveryFocus.pick_slot slots slots_injective 12 | exact RecoveryFocus.pick_slot slots slots_injective 13

private theorem grid_install (p m u cap : ℕ) (out log : List Bool) (more : List Bool) :
    install slots (initialized p m u cap out log) (CompetitorSameBucketZeroGridNative.data p m u u cap more)=
      result p m u cap more log := by
  apply HierarchyAllocation.install_eq _ slots_injective
  · intro j
    fin_cases j <;> simp [result,initialized,slots,CompetitorSameBucketZeroGridNative.data,Fin.addCases,
      CompetitorSameBucketZeroFinish.data,MatrixScoreBatch.signMagnitude,RankCarrier.binary_zero,List.replicate_succ]
  · intro i hi
    have h5 : i≠5 := fun h=>hi 6 h.symm
    have h10 : i≠10 := fun h=>hi 4 h.symm
    rw [result,Function.update_of_ne h10]
    fin_cases i <;> first | rfl | exact False.elim (h5 rfl)

theorem grid_run (p m u cap : ℕ) (out log : List Bool)
    (hp : 2*(p+1)≤cap) (hc : 4*m+3≤cap) (hu : u+u<2^m) :
    ∃ actual,runFrom grid (CompetitorSameBucketZeroGrid.budget p m u cap u)
        (cfg grid.start p m u cap out log)=some actual ∧
      actual.final.heads=heads (out++CompetitorSameBucketZeroGrid.bits p m u 0 u) ∧
      actual.final.tapes=result p m u cap (out++CompetitorSameBucketZeroGrid.bits p m u 0 u) log ∧
      actual.steps≤CompetitorSameBucketZeroGrid.budget p m u cap u := by
  obtain ⟨base,hb,bh,bt,bs⟩:=CompetitorSameBucketZeroGridNative.grid_run p m u cap out hp hc hu
  have inputEq : RecoveryFocus.config slots (heads out) (initialized p m u cap out log)
      (CompetitorSameBucketZeroGridNative.cfg 0 p m u 0 cap out)=cfg grid.start p m u cap out log := by
    apply WilliamsSourceCrop.focus_same slots (cfg grid.start p m u cap out log)
    · rw [CompetitorSameBucketZeroGridNative.cfg_heads]
      exact (selected p m u cap out log).1
    · rw [CompetitorSameBucketZeroGridNative.cfg_tapes]
      exact (selected p m u cap out log).2
  obtain ⟨actual,ha,af,ast⟩:=RecoveryFocus.run_config slots slots_injective CompetitorSameBucketZeroGridNative.machine
    (heads out) (initialized p m u cap out log) _ _ base hb
  rw [inputEq] at ha
  refine ⟨actual,ha,?_,?_,ast.trans_le bs⟩
  · rw [af]
    funext i
    simp only [RecoveryFocus.config,pick_slots,bh]
    fin_cases i <;> simp [heads,advances,CompetitorSameBucketZeroGridNative.heads,
      CompetitorSameBucketZeroFinish.heads,Fin.addCases]
  · rw [af]
    change install slots (initialized p m u cap out log) base.final.tapes=_
    rw [bt]
    exact grid_install p m u cap out log _

noncomputable def tail:=Composition.machine advance grid
noncomputable def machine:=Composition.machine CompetitorSameBucketZeroPrepareCopies.machine tail
def budget (p m u cap : ℕ):=CompetitorSameBucketZeroPrepareCopies.budget p m u cap+1+
  (1+1+CompetitorSameBucketZeroGrid.budget p m u cap u)

theorem cold_run (p m u cap : ℕ) (out : List Bool)
    (hp : 4*(p+1)+3≤cap) (hm : 4*m+3≤cap) (hu : u+u<2^m) :
    ∃ actual log,runFrom machine (budget p m u cap)
        (CompetitorSameBucketZeroPrepareSpace.cfg machine.start out
          (CompetitorSameBucketZeroPrepareSpace.input p m u cap out))=some actual ∧
      actual.final.heads=heads (out++CompetitorSameBucketZeroGrid.bits p m u 0 u) ∧
      actual.final.tapes=result p m u cap (out++CompetitorSameBucketZeroGrid.bits p m u 0 u) log ∧
      actual.steps≤budget p m u cap := by
  obtain ⟨prepared,log,hpRun,ph,pt,ps⟩:=CompetitorSameBucketZeroPrepareCopies.prepared_run p m u cap out hp hm
  obtain ⟨advancedRun,ha,af,ast⟩:=advance_run prepared.final
  obtain ⟨done,hd,dh,dt,ds⟩:=grid_run p m u cap out log (by omega) hm hu
  have hi : Composition.restart advancedRun.final grid.start=cfg grid.start p m u cap out log := by
    rw [af]
    apply configuration_ext
    · rfl
    · funext i
      simp only [Composition.restart,advanced,ph,cfg,heads]
      by_cases h : advances i
      · have ne : i≠5 := by unfold advances at h; rcases h with h|h <;> subst i <;> decide
        simp [h,CompetitorSameBucketZeroPrepareSpace.heads,ne]
      · simp [h,CompetitorSameBucketZeroPrepareSpace.heads]
    · exact pt
  rw [←hi] at hd
  have joinedTail:=Composition.run_join advance grid _ _ _ advancedRun done ha hd
  have ht : Composition.leftConfig _ (Composition.restart prepared.final advance.start)=
      Composition.restart prepared.final tail.start := rfl
  rw [ht] at joinedTail
  have joined:=Composition.run_join CompetitorSameBucketZeroPrepareCopies.machine tail _ _ _ prepared
    (Composition.joinedReceipt advancedRun done) hpRun joinedTail
  refine ⟨Composition.joinedReceipt prepared (Composition.joinedReceipt advancedRun done),log,joined,dh,dt,?_⟩
  change prepared.steps+1+(advancedRun.steps+1+done.steps)≤budget p m u cap
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGridCold
