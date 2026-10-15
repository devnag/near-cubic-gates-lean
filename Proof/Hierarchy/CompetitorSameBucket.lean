import Proof.Hierarchy.CompetitorSameBucketBounds
import Proof.MachineModel.OrdinaryMatrixBatchRankReverseBounds
import Proof.MachineModel.OrdinaryMatrixCoefficientBounds

/-! Actual cold same-bucket preparation from the original Request and raw W.
The ranked stream is already reset by the accepted counted rewind; the
coefficient bank is produced independently from that same retained Request.
No ranked stream, dimensions, or coefficient bank is an extra input. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCold
open LocalBitMultitape MatrixScoreBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rankSlots (i : Fin 306) : Fin 342 := if i=0 then 0 else ⟨i.val+2,by omega⟩
def coefficientSlots (i : Fin 35) : Fin 342 := if i=0 then 0 else ⟨i.val+307,by omega⟩
theorem rank_injective : Function.Injective rankSlots := by decide
theorem coefficient_injective : Function.Injective coefficientSlots := by decide

theorem rank_fresh (i : Fin 342) (hi : 308 ≤ i.val) : RecoveryFocus.pick rankSlots i=none := by
  classical
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  unfold rankSlots at hv
  split at hv <;> (try dsimp only at hv) <;> omega

theorem coefficient_rank (i : Fin 306) (hi : i≠0) :
    RecoveryFocus.pick coefficientSlots (rankSlots i)=none := by
  classical
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp only [rankSlots,hi,ite_false] at hv
  unfold coefficientSlots at hv
  split at hv <;> (try dsimp only at hv) <;> omega

theorem source_request (r : Request) (ranked : ExecutionReceipt 306 _)
    (hr : run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r)
      (MatrixBatchRankReverse.input r)=some ranked) :
    ranked.final.tapes 0=physicalInput r ∧ ranked.final.heads 0=0 := by
  obtain ⟨state,raw,used,_,_,_,hu,ut,uh,t0,h0,_,_,_,_,_,_,_,_,_⟩ :=
    MatrixBatchRetainedFields.retained_run r
  obtain ⟨same,endpoints,hs,he,et,eh,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchBucketEndpoints.raw_run r
  have heq : same=used := Option.some.inj (hs.symm.trans hu)
  subst same
  obtain ⟨same,actual,hs,ha,atapes,ah,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchRankReverse.raw_run r
  have heq : same=endpoints := Option.some.inj (hs.symm.trans he)
  subst same
  have heq : actual=ranked := Option.some.inj (ha.symm.trans hr)
  subst actual
  constructor
  · exact (atapes 0 (by decide)).trans ((et 0).trans ((ut 0).trans t0))
  · have h := (ah 0).trans ((eh 0).trans ((uh 0).trans h0))
    simpa using h

noncomputable def first := RecoveryFocus.machine rankSlots MatrixBatchRankReverse.machine
noncomputable def last := RecoveryFocus.machine coefficientSlots MatrixCoefficientCold.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) (w : ℕ) : Fin 342 → List Bool :=
  fun i => if i=0 then physicalInput r else if i=1 then List.replicate w true else []
def budget (r : Request) := MatrixBatchRankReverse.budget r+1+MatrixCoefficientCold.budget r

theorem cold_run (r : Request) (w : ℕ) : ∃ ranked : ExecutionReceipt 306 _,∃ actual,
    run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r)
      (MatrixBatchRankReverse.input r)=some ranked ∧
    run machine (budget r) (input r w)=some actual ∧
    (∀ i,actual.final.tapes (rankSlots i)=ranked.final.tapes i) ∧
    (∀ i,actual.final.heads (rankSlots i)=ranked.final.heads i) ∧
    actual.final.tapes 340=MatrixCoefficientLoop.output r.p r.cuts ∧ actual.final.heads 340=0 ∧
    actual.final.tapes 1=List.replicate w true ∧ actual.final.heads 1=0 ∧
    actual.final.tapes 2=[] ∧ actual.final.heads 2=0 ∧ actual.steps≤budget r := by
  obtain ⟨_,ranked,_,hr,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rs⟩ := MatrixBatchRankReverse.raw_run r
  obtain ⟨r0,rh0⟩ := source_request r ranked hr
  obtain ⟨prepared,hp,pf,ps⟩ := RecoveryFocus.run_config rankSlots rank_injective
    MatrixBatchRankReverse.machine (fun _ : Fin 342 => 0) (input r w) _
    (initialConfiguration MatrixBatchRankReverse.machine (MatrixBatchRankReverse.input r)) ranked hr
  have hi : RecoveryFocus.config rankSlots (fun _ : Fin 342 => 0) (input r w)
      (initialConfiguration MatrixBatchRankReverse.machine (MatrixBatchRankReverse.input r))=
      initialConfiguration first (input r w) := by
    apply configuration_ext
    · rfl
    · funext i
      cases h : RecoveryFocus.pick rankSlots i <;> simp [RecoveryFocus.config,h,initialConfiguration]
    · exact install_existing rankSlots (input r w) (MatrixBatchRankReverse.input r)
        (by intro i; fin_cases i <;> rfl)
  rw [hi] at hp
  have localT (i : Fin 306) : prepared.final.tapes (rankSlots i)=ranked.final.tapes i := by
    rw [pf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rankSlots rank_injective]
  have localH (i : Fin 306) : prepared.final.heads (rankSlots i)=ranked.final.heads i := by
    rw [pf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rankSlots rank_injective]
  obtain ⟨coeff,hc,c0,c33,ch,cs⟩ := MatrixCoefficientCold.cold_run r
  have hcInput : RecoveryFocus.config coefficientSlots prepared.final.heads prepared.final.tapes
      (initialConfiguration MatrixCoefficientCold.machine (MatrixCoefficientCold.input r))=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      by_cases h0 : i=0
      · subst i; exact (localH 0).trans rh0
      rw [pf]
      have hf : 308 ≤ (coefficientSlots i).val := by
        simp only [coefficientSlots,h0,ite_false]
        have hn : i.val≠0 := by simpa using h0
        omega
      simp only [RecoveryFocus.config,rank_fresh _ hf,initialConfiguration]
    · intro i
      by_cases h0 : i=0
      · subst i; exact (localT 0).trans r0
      rw [pf]
      have hf : 308 ≤ (coefficientSlots i).val := by
        simp only [coefficientSlots,h0,ite_false]
        have hn : i.val≠0 := by simpa using h0
        omega
      simp only [RecoveryFocus.config,rank_fresh _ hf,initialConfiguration,MatrixCoefficientCold.input,h0,ite_false]
      have hs0 : coefficientSlots i≠0 := by intro h; have hv := congrArg Fin.val h; omega
      have hs1 : coefficientSlots i≠1 := by intro h; have hv := congrArg Fin.val h; omega
      simp [input,hs0,hs1]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config coefficientSlots coefficient_injective
    MatrixCoefficientCold.machine prepared.final.heads prepared.final.tapes _
    (initialConfiguration MatrixCoefficientCold.machine (MatrixCoefficientCold.input r)) coeff hc
  rw [hcInput] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused hp hf
  have localCT (i : Fin 35) : focused.final.tapes (coefficientSlots i)=coeff.final.tapes i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot coefficientSlots coefficient_injective]
  have localCH (i : Fin 35) : focused.final.heads (coefficientSlots i)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot coefficientSlots coefficient_injective,ch]
  refine ⟨ranked,Composition.joinedReceipt prepared focused,hr,hj,?_,?_,
    (localCT 33).trans c33,localCH 33,?_,?_,?_,?_,?_⟩
  · intro i
    change focused.final.tapes (rankSlots i)=_
    by_cases h0 : i=0
    · subst i; exact (localCT 0).trans (c0.trans r0.symm)
    rw [ff]
    simp only [RecoveryFocus.config,coefficient_rank i h0]
    exact localT i
  · intro i
    change focused.final.heads (rankSlots i)=_
    by_cases h0 : i=0
    · subst i; exact (localCH 0).trans rh0.symm
    rw [ff]
    simp only [RecoveryFocus.config,coefficient_rank i h0]
    exact localH i
  · change focused.final.tapes 1=_
    rw [ff,pf]
    simp only [RecoveryFocus.config,show RecoveryFocus.pick coefficientSlots (1 : Fin 342)=none from by decide,
      show RecoveryFocus.pick rankSlots (1 : Fin 342)=none from by decide]
    rfl
  · change focused.final.heads 1=_
    rw [ff,pf]
    simp only [RecoveryFocus.config,show RecoveryFocus.pick coefficientSlots (1 : Fin 342)=none from by decide,
      show RecoveryFocus.pick rankSlots (1 : Fin 342)=none from by decide]
  · change focused.final.tapes 2=_
    rw [ff,pf]
    simp only [RecoveryFocus.config,show RecoveryFocus.pick coefficientSlots (2 : Fin 342)=none from by decide,
      show RecoveryFocus.pick rankSlots (2 : Fin 342)=none from by decide]
    rfl
  · change focused.final.heads 2=_
    rw [ff,pf]
    simp only [RecoveryFocus.config,show RecoveryFocus.pick coefficientSlots (2 : Fin 342)=none from by decide,
      show RecoveryFocus.pick rankSlots (2 : Fin 342)=none from by decide]
  · change prepared.steps+1+focused.steps≤budget r
    rw [ps,fs]
    unfold budget
    omega

theorem budget_le (r : Request) : budget r≤6*10^10*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hr := MatrixBatchRankReverseBounds.budget_le r
  have hc := MatrixCoefficientBounds.coefficient_budget r
  have hu : r.U+1≤(r.U+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_right ((r.d+r.p+1)^2) hu
  have hpos : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCold
