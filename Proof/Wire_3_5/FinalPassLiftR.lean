import Proof.Wire_3_5.FinalPassLift

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

variable {ns ns' nr nr' : ℕ}

/-! ## Register programs -/

/-- Run a register program on renamed streams (`fs`) and renamed registers (`fr`). -/
def RM.liftR (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') : RM ns nr → WM ns' nr'
  | .skip => .skip
  | .inc r => .inc (fr r)
  | .dec r => .dec (fr r)
  | .fwd i => .fwd (fs i)
  | .bwd i => .bwd (fs i)
  | .setc v => .setc v
  | .seq P Q => .seq (P.liftR fs fr) (Q.liftR fs fr)
  | .ifr r P Q => .ifr (fr r) (P.liftR fs fr) (Q.liftR fs fr)
  | .ifs i P Q => .ifs (fs i) (P.liftR fs fr) (Q.liftR fs fr)
  | .whr r P => .whr (fr r) (P.liftR fs fr)
  | .whs i P => .whs (fs i) (P.liftR fs fr)

/-- `ω` carries `σ`: the renamed streams read like `inp` at the same heads; renamed registers and the cell agree. -/
structure LiftRelR (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (inp : Fin (ns + 1) → List Bool)
    (ω : WState ns' nr') (σ : RState ns nr) : Prop where
  sh : ∀ i, ω.sh (fs i) = σ.sh i
  rd : ∀ i p, readTapeBit (ω.st (fs i)) p = readTapeBit (inp i) p
  val : ∀ r, ω.val (fr r) = σ.val r
  cell : ω.cell = σ.cell

/-- Nothing outside the images changes, and no stream is written. -/
def OutsideR (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω ω' : WState ns' nr') : Prop :=
  ω'.st = ω.st ∧ (∀ j, (∀ i, fs i ≠ j) → ω'.sh j = ω.sh j) ∧ (∀ q, (∀ r, fr r ≠ q) → ω'.val q = ω.val q)

theorem OutsideR.refl (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr') :
    OutsideR fs fr ω ω := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem OutsideR.trans {fs : Fin (ns + 1) → Fin (ns' + 1)} {fr : Fin nr → Fin nr'} {ω ω' ω'' : WState ns' nr'}
    (h1 : OutsideR fs fr ω ω') (h2 : OutsideR fs fr ω' ω'') : OutsideR fs fr ω ω'' :=
  ⟨h2.1.trans h1.1, fun j hj => (h2.2.1 j hj).trans (h1.2.1 j hj), fun q hq => (h2.2.2 q hq).trans (h1.2.2 q hq)⟩

theorem wbit_liftR {fs : Fin (ns + 1) → Fin (ns' + 1)} {fr : Fin nr → Fin nr'} {inp : Fin (ns + 1) → List Bool}
    {ω : WState ns' nr'} {σ : RState ns nr} (h : LiftRelR fs fr inp ω σ) (i : Fin (ns + 1)) :
    wbit ω (fs i) = sbit inp σ i := by
  unfold wbit sbit
  rw [h.rd, h.sh]

theorem LiftRelR.seth {fs : Fin (ns + 1) → Fin (ns' + 1)} {fr : Fin nr → Fin nr'} (hfs : Function.Injective fs)
    {inp : Fin (ns + 1) → List Bool} {ω : WState ns' nr'} {σ : RState ns nr} (h : LiftRelR fs fr inp ω σ)
    (i : Fin (ns + 1)) (x : ℕ) : LiftRelR fs fr inp (ω.seth (fs i) x) (σ.seth i x) := by
  refine ⟨fun i' => ?_, fun i' p => h.rd i' p, fun r => h.val r, h.cell⟩
  simp only [WState.seth_sh, RState.seth_sh, Function.update_apply]
  by_cases hi : i' = i
  · subst hi; simp
  · have hne : fs i' ≠ fs i := fun e => hi (hfs e)
    simp only [hne, hi, if_false]
    exact h.sh i'

theorem LiftRelR.setv {fs : Fin (ns + 1) → Fin (ns' + 1)} {fr : Fin nr → Fin nr'} (hfr : Function.Injective fr)
    {inp : Fin (ns + 1) → List Bool} {ω : WState ns' nr'} {σ : RState ns nr} (h : LiftRelR fs fr inp ω σ)
    (r : Fin nr) (x : ℕ) : LiftRelR fs fr inp (ω.setv (fr r) x) (σ.setv r x) := by
  refine ⟨fun i => h.sh i, fun i p => h.rd i p, fun r' => ?_, h.cell⟩
  simp only [WState.setv_val, RState.setv_val, Function.update_apply]
  by_cases hr : r' = r
  · subst hr; simp
  · have hne : fr r' ≠ fr r := fun e => hr (hfr e)
    simp only [hne, hr, if_false]
    exact h.val r'

theorem OutsideR.seth (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr')
    (i : Fin (ns + 1)) (x : ℕ) : OutsideR fs fr ω (ω.seth (fs i) x) :=
  ⟨rfl, fun j hj => by simp [Function.update_of_ne (Ne.symm (hj i))], fun _ _ => rfl⟩

theorem OutsideR.setv (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr')
    (r : Fin nr) (x : ℕ) : OutsideR fs fr ω (ω.setv (fr r) x) :=
  ⟨rfl, fun _ _ => rfl, fun q hq => by simp [Function.update_of_ne (Ne.symm (hq r))]⟩

/-- **Lifting with renamed registers**: a register derivation runs inside the word program, at every capacity
`cap' ≥ cap`. -/
theorem RExec.liftR (inp : Fin (ns + 1) → List Bool) (cap cap' : ℕ) (hcap : cap ≤ cap')
    (fs : Fin (ns + 1) → Fin (ns' + 1)) (hfs : Function.Injective fs) (fr : Fin nr → Fin nr')
    (hfr : Function.Injective fr) {P : RM ns nr} {σ τ : RState ns nr} {n : ℕ} (h : RExec inp cap P σ τ n) :
    ∀ ω : WState ns' nr', LiftRelR fs fr inp ω σ →
      ∃ ω', WExec cap' (P.liftR fs fr) ω ω' n ∧ LiftRelR fs fr inp ω' τ ∧ OutsideR fs fr ω ω' := by
  induction h with
  | skip σ => exact fun ω hω => ⟨ω, WExec.skip ω, hω, OutsideR.refl fs fr ω⟩
  | inc r σ hv =>
    intro ω hω
    have e : ω.val (fr r) = σ.val r := hω.val r
    refine ⟨ω.setv (fr r) (ω.val (fr r) + 1), WExec.inc (fr r) ω (by omega), ?_, OutsideR.setv fs fr ω r _⟩
    rw [e]; exact hω.setv hfr r _
  | dec r σ hv =>
    intro ω hω
    have e : ω.val (fr r) = σ.val r := hω.val r
    refine ⟨ω.setv (fr r) (ω.val (fr r) - 1), WExec.dec (fr r) ω (by omega), ?_, OutsideR.setv fs fr ω r _⟩
    rw [e]; exact hω.setv hfr r _
  | fwd i σ =>
    intro ω hω
    refine ⟨ω.seth (fs i) (ω.sh (fs i) + 1), WExec.fwd (fs i) ω, ?_, OutsideR.seth fs fr ω i _⟩
    rw [hω.sh i]; exact hω.seth hfs i _
  | bwd i σ =>
    intro ω hω
    refine ⟨ω.seth (fs i) (ω.sh (fs i) - 1), WExec.bwd (fs i) ω, ?_, OutsideR.seth fs fr ω i _⟩
    rw [hω.sh i]; exact hω.seth hfs i _
  | setc v σ =>
    intro ω hω
    exact ⟨ω.setc v, WExec.setc v ω, ⟨fun i => hω.sh i, fun i p => hω.rd i p, fun r => hω.val r, rfl⟩,
      ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  | seq _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.seq e1 e2, r2, o1.trans o2⟩
  | ifrT hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifrT (by rw [hω.val]; exact hv) e1, r1, o1⟩
  | ifrF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifrF (by rw [hω.val]; exact hv) e1, r1, o1⟩
  | ifsT hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifsT (by rw [wbit_liftR hω]; exact hv) e1, r1, o1⟩
  | ifsF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifsF (by rw [wbit_liftR hω]; exact hv) e1, r1, o1⟩
  | whrF hv =>
    intro ω hω
    exact ⟨ω, WExec.whrF (by rw [hω.val]; exact hv), hω, OutsideR.refl fs fr ω⟩
  | whrT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.whrT (by rw [hω.val]; exact hv) e1 e2, r2, o1.trans o2⟩
  | whsF hv =>
    intro ω hω
    exact ⟨ω, WExec.whsF (by rw [wbit_liftR hω]; exact hv), hω, OutsideR.refl fs fr ω⟩
  | whsT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.whsT (by rw [wbit_liftR hω]; exact hv) e1 e2, r2, o1.trans o2⟩
  | mono _ hnm ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.mono e1 hnm, r1, o1⟩

/-! ## Word programs -/

/-- Run a word program on renamed streams (`fs`) and renamed registers (`fr`). -/
def WM.liftW (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') : WM ns nr → WM ns' nr'
  | .skip => .skip
  | .inc r => .inc (fr r)
  | .dec r => .dec (fr r)
  | .fwd i => .fwd (fs i)
  | .bwd i => .bwd (fs i)
  | .wr i b => .wr (fs i) b
  | .setc v => .setc v
  | .seq P Q => .seq (P.liftW fs fr) (Q.liftW fs fr)
  | .ifr r P Q => .ifr (fr r) (P.liftW fs fr) (Q.liftW fs fr)
  | .ifs i P Q => .ifs (fs i) (P.liftW fs fr) (Q.liftW fs fr)
  | .whr r P => .whr (fr r) (P.liftW fs fr)
  | .whs i P => .whs (fs i) (P.liftW fs fr)

/-- `ω` carries `σ`: the renamed streams hold `σ`'s streams at the same heads; renamed registers and the cell agree. -/
structure LiftW (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr') (σ : WState ns nr) :
    Prop where
  sh : ∀ i, ω.sh (fs i) = σ.sh i
  st : ∀ i, ω.st (fs i) = σ.st i
  val : ∀ r, ω.val (fr r) = σ.val r
  cell : ω.cell = σ.cell

/-- Nothing outside the images changes. -/
def OutsideW (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω ω' : WState ns' nr') : Prop :=
  (∀ j, (∀ i, fs i ≠ j) → ω'.sh j = ω.sh j ∧ ω'.st j = ω.st j) ∧ (∀ q, (∀ r, fr r ≠ q) → ω'.val q = ω.val q)

theorem OutsideW.refl (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr') :
    OutsideW fs fr ω ω := ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

theorem OutsideW.trans {fs : Fin (ns + 1) → Fin (ns' + 1)} {fr : Fin nr → Fin nr'} {ω ω' ω'' : WState ns' nr'}
    (h1 : OutsideW fs fr ω ω') (h2 : OutsideW fs fr ω' ω'') : OutsideW fs fr ω ω'' :=
  ⟨fun j hj => ⟨(h2.1 j hj).1.trans (h1.1 j hj).1, (h2.1 j hj).2.trans (h1.1 j hj).2⟩,
    fun q hq => (h2.2 q hq).trans (h1.2 q hq)⟩

theorem wbit_liftW {fs : Fin (ns + 1) → Fin (ns' + 1)} {fr : Fin nr → Fin nr'} {ω : WState ns' nr'}
    {σ : WState ns nr} (h : LiftW fs fr ω σ) (i : Fin (ns + 1)) : wbit ω (fs i) = wbit σ i := by
  unfold wbit
  rw [h.st, h.sh]

/-- **Lifting a word program**: every `WExec` derivation runs inside the larger word program, at every capacity
`cap' ≥ cap`. -/
theorem WExec.liftW (cap cap' : ℕ) (hcap : cap ≤ cap') (fs : Fin (ns + 1) → Fin (ns' + 1))
    (hfs : Function.Injective fs) (fr : Fin nr → Fin nr') (hfr : Function.Injective fr) {P : WM ns nr}
    {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    ∀ ω : WState ns' nr', LiftW fs fr ω σ →
      ∃ ω', WExec cap' (P.liftW fs fr) ω ω' n ∧ LiftW fs fr ω' τ ∧ OutsideW fs fr ω ω' := by
  induction h with
  | skip σ => exact fun ω hω => ⟨ω, WExec.skip ω, hω, OutsideW.refl fs fr ω⟩
  | inc r σ hv =>
    intro ω hω
    have e : ω.val (fr r) = σ.val r := hω.val r
    refine ⟨ω.setv (fr r) (ω.val (fr r) + 1), WExec.inc (fr r) ω (by omega), ⟨fun i => hω.sh i, fun i => hω.st i,
      fun r' => ?_, hω.cell⟩, ⟨fun _ _ => ⟨rfl, rfl⟩, fun q hq => by simp [Function.update_of_ne (Ne.symm (hq r))]⟩⟩
    simp only [WState.setv_val, Function.update_apply]
    by_cases hr : r' = r
    · subst hr; simp [e]
    · have hne : fr r' ≠ fr r := fun e' => hr (hfr e')
      simp only [hne, hr, if_false]
      exact hω.val r'
  | dec r σ hv =>
    intro ω hω
    have e : ω.val (fr r) = σ.val r := hω.val r
    refine ⟨ω.setv (fr r) (ω.val (fr r) - 1), WExec.dec (fr r) ω (by omega), ⟨fun i => hω.sh i, fun i => hω.st i,
      fun r' => ?_, hω.cell⟩, ⟨fun _ _ => ⟨rfl, rfl⟩, fun q hq => by simp [Function.update_of_ne (Ne.symm (hq r))]⟩⟩
    simp only [WState.setv_val, Function.update_apply]
    by_cases hr : r' = r
    · subst hr; simp [e]
    · have hne : fr r' ≠ fr r := fun e' => hr (hfr e')
      simp only [hne, hr, if_false]
      exact hω.val r'
  | fwd i σ =>
    intro ω hω
    refine ⟨ω.seth (fs i) (ω.sh (fs i) + 1), WExec.fwd (fs i) ω, ⟨fun i' => ?_, fun i' => hω.st i',
      fun r => hω.val r, hω.cell⟩, ⟨fun j hj => ⟨by simp [Function.update_of_ne (Ne.symm (hj i))], rfl⟩,
      fun _ _ => rfl⟩⟩
    simp only [WState.seth_sh, Function.update_apply]
    by_cases hi : i' = i
    · subst hi; simp [hω.sh]
    · have hne : fs i' ≠ fs i := fun e => hi (hfs e)
      simp only [hne, hi, if_false]
      exact hω.sh i'
  | bwd i σ =>
    intro ω hω
    refine ⟨ω.seth (fs i) (ω.sh (fs i) - 1), WExec.bwd (fs i) ω, ⟨fun i' => ?_, fun i' => hω.st i',
      fun r => hω.val r, hω.cell⟩, ⟨fun j hj => ⟨by simp [Function.update_of_ne (Ne.symm (hj i))], rfl⟩,
      fun _ _ => rfl⟩⟩
    simp only [WState.seth_sh, Function.update_apply]
    by_cases hi : i' = i
    · subst hi; simp [hω.sh]
    · have hne : fs i' ≠ fs i := fun e => hi (hfs e)
      simp only [hne, hi, if_false]
      exact hω.sh i'
  | wr i b σ =>
    intro ω hω
    refine ⟨ω.sets (fs i) (writeTapeBit (ω.st (fs i)) (ω.sh (fs i)) b), WExec.wr (fs i) b ω,
      ⟨fun i' => hω.sh i', fun i' => ?_, fun r => hω.val r, hω.cell⟩,
      ⟨fun j hj => ⟨rfl, by simp [Function.update_of_ne (Ne.symm (hj i))]⟩, fun _ _ => rfl⟩⟩
    simp only [WState.sets_st, Function.update_apply]
    by_cases hi : i' = i
    · subst hi; simp [hω.st, hω.sh]
    · have hne : fs i' ≠ fs i := fun e => hi (hfs e)
      simp only [hne, hi, if_false]
      exact hω.st i'
  | setc v σ =>
    intro ω hω
    exact ⟨ω.setc v, WExec.setc v ω, ⟨fun i => hω.sh i, fun i => hω.st i, fun r => hω.val r, rfl⟩,
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩⟩
  | seq _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.seq e1 e2, r2, o1.trans o2⟩
  | ifrT hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifrT (by rw [hω.val]; exact hv) e1, r1, o1⟩
  | ifrF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifrF (by rw [hω.val]; exact hv) e1, r1, o1⟩
  | ifsT hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifsT (by rw [wbit_liftW hω]; exact hv) e1, r1, o1⟩
  | ifsF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifsF (by rw [wbit_liftW hω]; exact hv) e1, r1, o1⟩
  | whrF hv =>
    intro ω hω
    exact ⟨ω, WExec.whrF (by rw [hω.val]; exact hv), hω, OutsideW.refl fs fr ω⟩
  | whrT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.whrT (by rw [hω.val]; exact hv) e1 e2, r2, o1.trans o2⟩
  | whsF hv =>
    intro ω hω
    exact ⟨ω, WExec.whsF (by rw [wbit_liftW hω]; exact hv), hω, OutsideW.refl fs fr ω⟩
  | whsT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.whsT (by rw [wbit_liftW hω]; exact hv) e1 e2, r2, o1.trans o2⟩
  | mono _ hnm ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.mono e1 hnm, r1, o1⟩

end NearCubicWires.WireExponent3_5.FinalPass.Tm
