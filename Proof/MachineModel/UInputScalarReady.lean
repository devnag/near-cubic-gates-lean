import Proof.MachineModel.UInputScalars

/-! Scalar guard semantics, the paid floor-log sentinel, and the complete
literal scalar-preparation boundary. -/
namespace NearCubicWires.RepairOrdinary.UInputScalars
open LocalBitMultitape RecoveryRootRound ClockDyadicLedger ClockUniversalBound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Guards (raw x bound : List Bool) : Prop :=
  bound.length ≤ width raw.length ∧ x.length ≤ value bound ∧ value bound ≤ limit raw.length

theorem input_word_fits (raw x : List Bool) (hn : 0 < raw.length) (hx : x.length ≤ raw.length) :
    (ClockBinary.word x.length).length ≤ width raw.length := by
  apply boundWord_fits
  exact hx.trans ((Nat.le_self_pow (by simp [PowerSlice.degree]) raw.length).trans
    (limit_bounds raw.length hn).1)

theorem flag_iff (raw x bound : List Bool) (hn : 0 < raw.length) (hx : x.length ≤ raw.length) :
    flag raw x bound=true ↔ Guards raw x bound := by
  have hnorm : (normalized raw bound).length ≤ width raw.length := by
    simp [normalized,ClockBoundGuard.normalized]
  have hu := ClockBoundGuard.accepted_iff (width raw.length) bound (limitWord raw.length)
    (limitWord_fits raw.length)
  have hl := ClockBoundGuard.accepted_iff (width raw.length) (ClockBinary.word x.length)
    (normalized raw bound) hnorm
  have hfit := input_word_fits raw x hn hx
  constructor
  · intro h
    have hh : upperFlag raw bound=true ∧ lowerFlag raw x bound=true := by simpa [flag] using h
    obtain ⟨a,b⟩ := hh
    change ClockBoundGuard.accepted _ _ _=true at a b
    rw [hu] at a
    have ha : bound.length ≤ width raw.length ∧ value bound ≤ limit raw.length := by simpa using a
    rw [hl] at b
    have hb : x.length ≤ value bound := by
      simpa [hfit,normalized,ClockBoundGuard.normalized,
        ClockScalarFields.resize_value _ _ ha.1] using b
    exact ⟨ha.1,hb,ha.2⟩
  · rintro ⟨hb,hxB,hBL⟩
    change (upperFlag raw bound && lowerFlag raw x bound)=true
    simp only [Bool.and_eq_true]
    constructor
    · change ClockBoundGuard.accepted _ _ _=true
      rw [hu]
      simp [hb,hBL]
    · change ClockBoundGuard.accepted _ _ _=true
      rw [hl]
      simp [hfit,normalized,ClockBoundGuard.normalized,ClockScalarFields.resize_value _ _ hb,hxB]

def logHeads : Fin 40 → ℕ := fun i => if i.val=38 then 1 else 0
def fullOutput (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) : Store := fun i =>
  if i.val=38 then RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 raw.length)
  else if i.val=39 then List.replicate (2*PCPResourceLedger.ell raw.length+2) false
  else output raw x bound carry reset degree cap scratch i

theorem log_pick (i : Fin 40) : RecoveryFocus.pick logSlots i=
    (if i.val=3 then some 0 else if i.val=38 then some 1 else if i.val=39 then some 2 else none) := by
  by_cases h3 : i.val=3
  · have he : i=logSlots 0 := Fin.ext h3
    rw [he,RecoveryFocus.pick_slot _ log_injective]
    rfl
  by_cases h38 : i.val=38
  · have he : i=logSlots 1 := Fin.ext h38
    rw [he,RecoveryFocus.pick_slot _ log_injective]
    rfl
  by_cases h39 : i.val=39
  · have he : i=logSlots 2 := Fin.ext h39
    rw [he,RecoveryFocus.pick_slot _ log_injective]
    rfl
  have hn : ¬∃ j,logSlots j=i := by
    rintro ⟨j,hj⟩
    fin_cases j <;> simp_all [logSlots,Fin.ext_iff]
  simp [RecoveryFocus.pick,hn,h3,h38,h39]

theorem log_run (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) :
    ∃ r,run logPhase (4*PCPResourceLedger.ell raw.length+8)
        (output raw x bound carry reset degree cap scratch)=some r ∧
      r.final.tapes=fullOutput raw x bound carry reset degree cap scratch ∧
      r.final.heads=logHeads ∧ r.steps=4*PCPResourceLedger.ell raw.length+8 := by
  obtain ⟨base,hb,h0,h1,h2,hh,hs⟩ := ClockFloorLog.binary_run raw.length
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config logSlots log_injective ClockFloorLog.machine
    (fun _ => 0) (output raw x bound carry reset degree cap scratch)
    (4*PCPResourceLedger.ell raw.length+8) _ base hb
  have hi : RecoveryFocus.config logSlots (fun _ => 0) (output raw x bound carry reset degree cap scratch)
      (initialConfiguration ClockFloorLog.machine (ClockFloorLog.input (ClockBinary.word raw.length)))=
      initialConfiguration logPhase (output raw x bound carry reset degree cap scratch) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick logSlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing logSlots _ _ (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hrs.trans hs⟩
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,log_pick,fullOutput,h0,h1,h2]
    rfl
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,log_pick,hh,logHeads]

noncomputable def fullMachine := Composition.machine machine logPhase
def fullBudget (raw x : List Bool) := budget raw x+1+(4*PCPResourceLedger.ell raw.length+8)

theorem full_run (raw x bound : List Bool) (hn : 0 < raw.length) :
    ∃ carry reset degree cap scratch r,
      run fullMachine (fullBudget raw x) (input raw x bound)=some r ∧
      r.final.tapes=fullOutput raw x bound carry reset degree cap scratch ∧
      r.final.heads=logHeads ∧ r.steps ≤ fullBudget raw x := by
  obtain ⟨carry,reset,degree,cap,scratch,first,hfirst,ht,hh,hs⟩ := prepare_ready raw x bound hn
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := log_run raw x bound carry reset degree cap scratch
  have he : Composition.restart first.final logPhase.start=
      initialConfiguration logPhase (output raw x bound carry reset degree cap scratch) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  unfold run at hlast
  rw [←he] at hlast
  have h := Composition.run_join machine logPhase (budget raw x) (4*PCPResourceLedger.ell raw.length+8)
    _ first last hfirst hlast
  refine ⟨carry,reset,degree,cap,scratch,Composition.joinedReceipt first last,h,hlt,hlh,?_⟩
  dsimp only [Composition.joinedReceipt,fullBudget]
  omega

theorem budget_bound (raw x : List Bool) (hx : x.length ≤ raw.length) :
    fullBudget raw x ≤ 300*(raw.length+1)*PCPResourceLedger.q raw.length^2 := by
  have hc := ClockPreparation.budget_bound raw
  have hxcount := HierarchyReduction.count_budget x
  have hwidth := (width_bounds raw.length).2
  have hell : PCPResourceLedger.ell x.length ≤ PCPResourceLedger.ell raw.length :=
    Nat.clog_mono_right 2 (by omega)
  have hq : 1 ≤ PCPResourceLedger.q raw.length := by simp [PCPResourceLedger.q]
  have hq2 : 1 ≤ PCPResourceLedger.q raw.length^2 := Nat.one_le_pow _ _ hq
  have hcount : HierarchyInputLength.budget x ≤
      42*(raw.length+1)*PCPResourceLedger.q raw.length^2 := by
    have hl : PCPResourceLedger.ell x.length+1 ≤ PCPResourceLedger.q raw.length^2 := by
      dsimp [PCPResourceLedger.q] at *
      nlinarith
    exact hxcount.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 42 (by omega)) hl)
  have he : PCPResourceLedger.ell raw.length ≤ PCPResourceLedger.q raw.length^2 := by
    dsimp [PCPResourceLedger.q]
    nlinarith
  have hp : PCPResourceLedger.q raw.length^2 ≤ (raw.length+1)*PCPResourceLedger.q raw.length^2 := by
    nlinarith
  dsimp only [fullBudget,budget]
  nlinarith

theorem output_fields (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) :
    let out := fullOutput raw x bound carry reset degree cap scratch
    out 0=frame raw ∧ out 1=frame x ∧ out 2=frame bound ∧
    out 3=frame (ClockBinary.word raw.length) ∧
    out 10=List.replicate (width raw.length) true ∧
    out 11=List.replicate (2*width raw.length) true ∧
    out 12=List.replicate (2*width raw.length+2) true ∧
    out 16=frame (normalized raw bound) ∧
    out 19=frame (SignedSortKey.binary (width raw.length) (limit raw.length)) ∧
    out 37=[flag raw x bound] ∧
    out 38=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 raw.length) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl⟩
  change frame (ClockBoundGuard.normalized _ _)=_
  simp [ClockBoundGuard.normalized,ClockScalarFields.resize_binary _ _ (limitWord_fits raw.length)]

end NearCubicWires.RepairOrdinary.UInputScalars
