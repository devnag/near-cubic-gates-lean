import Proof.Wire_3_5.FinalPassWords

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

variable {ns ns' nr : ℕ}

/-- Run a register program on renamed streams (`fs`) and shared registers. -/
def RM.lift (fs : Fin (ns + 1) → Fin (ns' + 1)) : RM ns nr → WM ns' nr
  | .skip => .skip
  | .inc r => .inc r
  | .dec r => .dec r
  | .fwd i => .fwd (fs i)
  | .bwd i => .bwd (fs i)
  | .setc v => .setc v
  | .seq P Q => .seq (P.lift fs) (Q.lift fs)
  | .ifr r P Q => .ifr r (P.lift fs) (Q.lift fs)
  | .ifs i P Q => .ifs (fs i) (P.lift fs) (Q.lift fs)
  | .whr r P => .whr r (P.lift fs)
  | .whs i P => .whs (fs i) (P.lift fs)

/-- `ω` carries `σ` through `fs`: the renamed streams read like `inp` at the same heads; registers and cell agree. -/
structure LiftRel (fs : Fin (ns + 1) → Fin (ns' + 1)) (inp : Fin (ns + 1) → List Bool) (ω : WState ns' nr)
    (σ : RState ns nr) : Prop where
  sh : ∀ i, ω.sh (fs i) = σ.sh i
  rd : ∀ i p, readTapeBit (ω.st (fs i)) p = readTapeBit (inp i) p
  val : ω.val = σ.val
  cell : ω.cell = σ.cell

/-- The stream contents are unchanged and the heads outside the image of `fs` do not move. -/
def Outside (fs : Fin (ns + 1) → Fin (ns' + 1)) (ω ω' : WState ns' nr) : Prop :=
  ω'.st = ω.st ∧ ∀ j, (∀ i, fs i ≠ j) → ω'.sh j = ω.sh j

theorem Outside.refl (fs : Fin (ns + 1) → Fin (ns' + 1)) (ω : WState ns' nr) : Outside fs ω ω :=
  ⟨rfl, fun _ _ => rfl⟩

theorem Outside.trans {fs : Fin (ns + 1) → Fin (ns' + 1)} {ω ω' ω'' : WState ns' nr} (h1 : Outside fs ω ω')
    (h2 : Outside fs ω' ω'') : Outside fs ω ω'' :=
  ⟨h2.1.trans h1.1, fun j hj => (h2.2 j hj).trans (h1.2 j hj)⟩

theorem wbit_lift {fs : Fin (ns + 1) → Fin (ns' + 1)} {inp : Fin (ns + 1) → List Bool} {ω : WState ns' nr}
    {σ : RState ns nr} (h : LiftRel fs inp ω σ) (i : Fin (ns + 1)) : wbit ω (fs i) = sbit inp σ i := by
  unfold wbit sbit
  rw [h.rd, h.sh]

theorem LiftRel.seth {fs : Fin (ns + 1) → Fin (ns' + 1)} (hfs : Function.Injective fs)
    {inp : Fin (ns + 1) → List Bool} {ω : WState ns' nr} {σ : RState ns nr} (h : LiftRel fs inp ω σ)
    (i : Fin (ns + 1)) (x : ℕ) : LiftRel fs inp (ω.seth (fs i) x) (σ.seth i x) := by
  refine ⟨fun i' => ?_, fun i' p => h.rd i' p, h.val, h.cell⟩
  simp only [WState.seth_sh, RState.seth_sh, Function.update_apply]
  by_cases hi : i' = i
  · subst hi; simp
  · have hne : fs i' ≠ fs i := fun e => hi (hfs e)
    simp only [hne, hi, if_false]
    exact h.sh i'

theorem Outside.seth (fs : Fin (ns + 1) → Fin (ns' + 1)) (ω : WState ns' nr) (i : Fin (ns + 1)) (x : ℕ) :
    Outside fs ω (ω.seth (fs i) x) :=
  ⟨rfl, fun j hj => by simp [Function.update_of_ne (Ne.symm (hj i))]⟩

theorem Outside.setv (fs : Fin (ns + 1) → Fin (ns' + 1)) (ω : WState ns' nr) (r : Fin nr) (x : ℕ) :
    Outside fs ω (ω.setv r x) :=
  ⟨rfl, fun _ _ => rfl⟩

theorem LiftRel.setv {fs : Fin (ns + 1) → Fin (ns' + 1)} {inp : Fin (ns + 1) → List Bool} {ω : WState ns' nr}
    {σ : RState ns nr} (h : LiftRel fs inp ω σ) (r : Fin nr) (x : ℕ) :
    LiftRel fs inp (ω.setv r x) (σ.setv r x) :=
  ⟨fun i => h.sh i, fun i p => h.rd i p, by simp [h.val], h.cell⟩

/-- **Lifting**: a register derivation runs inside the word program, at every capacity `cap' ≥ cap`. -/
theorem RExec.lift (inp : Fin (ns + 1) → List Bool) (cap cap' : ℕ) (hcap : cap ≤ cap')
    (fs : Fin (ns + 1) → Fin (ns' + 1)) (hfs : Function.Injective fs)
    {P : RM ns nr} {σ τ : RState ns nr} {n : ℕ} (h : RExec inp cap P σ τ n) :
    ∀ ω : WState ns' nr, LiftRel fs inp ω σ →
      ∃ ω', WExec cap' (P.lift fs) ω ω' n ∧ LiftRel fs inp ω' τ ∧ Outside fs ω ω' := by
  induction h with
  | skip σ => exact fun ω hω => ⟨ω, WExec.skip ω, hω, Outside.refl fs ω⟩
  | inc r σ hv =>
    intro ω hω
    have e : ω.val r = σ.val r := by rw [hω.val]
    refine ⟨ω.setv r (ω.val r + 1), WExec.inc r ω (by omega), ?_, Outside.setv fs ω r _⟩
    rw [e]; exact hω.setv r _
  | dec r σ hv =>
    intro ω hω
    have e : ω.val r = σ.val r := by rw [hω.val]
    refine ⟨ω.setv r (ω.val r - 1), WExec.dec r ω (by omega), ?_, Outside.setv fs ω r _⟩
    rw [e]; exact hω.setv r _
  | fwd i σ =>
    intro ω hω
    refine ⟨ω.seth (fs i) (ω.sh (fs i) + 1), WExec.fwd (fs i) ω, ?_, Outside.seth fs ω i _⟩
    rw [hω.sh i]; exact hω.seth hfs i _
  | bwd i σ =>
    intro ω hω
    refine ⟨ω.seth (fs i) (ω.sh (fs i) - 1), WExec.bwd (fs i) ω, ?_, Outside.seth fs ω i _⟩
    rw [hω.sh i]; exact hω.seth hfs i _
  | setc v σ =>
    intro ω hω
    exact ⟨ω.setc v, WExec.setc v ω, ⟨fun i => hω.sh i, fun i p => hω.rd i p, hω.val, rfl⟩, ⟨rfl, fun _ _ => rfl⟩⟩
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
    exact ⟨ω1, WExec.ifsT (by rw [wbit_lift hω]; exact hv) e1, r1, o1⟩
  | ifsF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.ifsF (by rw [wbit_lift hω]; exact hv) e1, r1, o1⟩
  | whrF hv =>
    intro ω hω
    exact ⟨ω, WExec.whrF (by rw [hω.val]; exact hv), hω, Outside.refl fs ω⟩
  | whrT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.whrT (by rw [hω.val]; exact hv) e1 e2, r2, o1.trans o2⟩
  | whsF hv =>
    intro ω hω
    exact ⟨ω, WExec.whsF (by rw [wbit_lift hω]; exact hv), hω, Outside.refl fs ω⟩
  | whsT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, r2, o2⟩ := ih2 ω1 r1
    exact ⟨ω2, WExec.whsT (by rw [wbit_lift hω]; exact hv) e1 e2, r2, o1.trans o2⟩
  | mono _ hnm ih =>
    intro ω hω
    obtain ⟨ω1, e1, r1, o1⟩ := ih ω hω
    exact ⟨ω1, WExec.mono e1 hnm, r1, o1⟩

/-- Blank padding does not change what a stream reads. -/
theorem readTapeBit_pad (l : List Bool) (k p : ℕ) :
    readTapeBit (l ++ List.replicate k false) p = readTapeBit l p := by
  unfold readTapeBit
  by_cases hp : p < l.length
  · rw [List.getD_append _ _ _ _ hp]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have h1 : l.getD p false = false := List.getD_eq_default _ _ (by omega)
    rw [h1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

end NearCubicWires.WireExponent3_5.FinalPass.Tm
