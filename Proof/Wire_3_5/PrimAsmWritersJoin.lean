import Proof.Wire_3_5.PrimAsmPreLink
import Proof.Wire_3_5.PrimAsmComposeEnv

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ NearCubicWires.WireExponent3_5.PrimAsm.PreLink
open NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv

/-! ## Monotonicity -/

/-- A writer's run within `B` steps is a run within any larger bound. -/
theorem writerRun_mono {t s : ℕ} {M : Machine t s} {B B' : ℕ} {i o : Fin t} {w v : List Bool}
    (h : WriterRun M B i o w v) (hB : B ≤ B') : WriterRun M B' i o w v := by
  obtain ⟨J, hJ, hR⟩ := h
  exact ⟨J, fun j => (hJ j).trans hB, ClockJoin.enlarge M B B' _ _ hR hB⟩

/-- Every call length with the star hypotheses is at least `1`. -/
theorem one_le_of_starAt {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {n : ℕ}
    (hs : I.StarAt n) : 1 ≤ n := by
  have h1 := hs.2.1
  have h2 := hs.2.2.1
  omega

/-- The writers' budget is monotone in the floor envelope and the coefficient. -/
theorem budget_mono {EW EW' : Envelope} {cW cW' : ℕ} (h : ClassLE EW EW') (hc : cW ≤ cW') {n : ℕ} (hn : 1 ≤ n)
    (k psi : ℕ) :
    cW * classBound EW .preprocessing n k psi ≤ cW' * classBound EW' .preprocessing n k psi :=
  Nat.mul_le_mul hc (classBound_mono h .preprocessing n k psi hn (fun h => by cases h))

section Mono
variable {l : Literals} {F : GateFree l} {EW EW' : Envelope} {cW cW' kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

/-- The SYM writer within a larger budget. -/
def symMono (W : SymWriterAtJ l F EW cW kclk coef A a ha) (h : ClassLE EW EW') (hc : cW ≤ cW') :
    SymWriterAtJ l F EW' cW' kclk coef A a ha :=
  { W.toWriterStage with
    ready := fun n a' ha' Cs c tr hcall hs =>
      writerRun_mono (W.ready n a' ha' Cs c tr hcall hs) (budget_mono h hc (one_le_of_starAt hs) _ _) }

/-- The THR writer within a larger budget. -/
def thrMono (W : ThrWriterAtJ l F EW cW kclk coef A a ha) (h : ClassLE EW EW') (hc : cW ≤ cW') :
    ThrWriterAtJ l F EW' cW' kclk coef A a ha :=
  { W.toWriterStage with
    ready := fun n a' ha' Cs c tr hcall hs =>
      writerRun_mono (W.ready n a' ha' Cs c tr hcall hs) (budget_mono h hc (one_le_of_starAt hs) _ _) }

/-- The HASH writer within a larger budget. -/
def hashMono (W : HashWriterAtJ l F EW cW kclk coef A a ha) (h : ClassLE EW EW') (hc : cW ≤ cW') :
    HashWriterAtJ l F EW' cW' kclk coef A a ha :=
  { W.toWriterStage with
    ready := fun n a' ha' Cs c tr hcall hs =>
      writerRun_mono (W.ready n a' ha' Cs c tr hcall hs) (budget_mono h hc (one_le_of_starAt hs) _ _) }

end Mono

/-- **The SYM writer's deliverable**, in `WriterLeafJ2`'s order of choice. -/
def SymLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SymWriterAtJ l F EW cW kclk coef A a ha

/-- **The THR writer's deliverable**, in `WriterLeafJ2`'s order of choice. -/
def ThrLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), ThrWriterAtJ l F EW cW kclk coef A a ha

/-- **The HASH writer's deliverable**, in `WriterLeafJ2`'s order of choice. -/
def HashLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), HashWriterAtJ l F EW cW kclk coef A a ha

/-! ## The join -/

theorem classLE_max3_1 (E₁ E₂ E₃ : Envelope) : ClassLE E₁ (envMax (envMax E₁ E₂) E₃) :=
  classLE_trans (classLE_envMax_left E₁ E₂) (classLE_envMax_left _ E₃)

theorem classLE_max3_2 (E₁ E₂ E₃ : Envelope) : ClassLE E₂ (envMax (envMax E₁ E₂) E₃) :=
  classLE_trans (classLE_envMax_right E₁ E₂) (classLE_envMax_left _ E₃)

theorem classLE_max3_3 (E₁ E₂ E₃ : Envelope) : ClassLE E₃ (envMax (envMax E₁ E₂) E₃) :=
  classLE_envMax_right _ E₃

theorem le_max3_1 (a b c : ℕ) : a ≤ max (max a b) c := by omega

theorem le_max3_2 (a b c : ℕ) : b ≤ max (max a b) c := by omega

theorem le_max3_3 (a b c : ℕ) : c ≤ max (max a b) c := by omega

/-- **The writers' join**: three separately built writers give the writer node's target. -/
noncomputable def writerLeafJ2_of (l : Literals) (S : SymLeafJ2 l) (T : ThrLeafJ2 l) (H : HashLeafJ2 l) :
    WriterLeafJ2 l :=
  fun fe => ⟨envMax (envMax (S fe).1 (T fe).1) (H fe).1, max (max (S fe).2.1 (T fe).2.1) (H fe).2.1,
    fun F hF hE hCD =>
      let s := (S fe).2.2 F hF (classLE_trans (classLE_max3_1 _ _ _) hE) ((le_max3_1 _ _ _).trans hCD)
      let t := (T fe).2.2 F hF (classLE_trans (classLE_max3_2 _ _ _) hE) ((le_max3_2 _ _ _).trans hCD)
      let h := (H fe).2.2 F hF (classLE_trans (classLE_max3_3 _ _ _) hE) ((le_max3_3 _ _ _).trans hCD)
      ⟨max (max s.1 t.1) h.1, fun kclk coef A a ha =>
        { sym := symMono (s.2 kclk coef A a ha) (classLE_max3_1 _ _ _) (le_max3_1 _ _ _)
          thr := thrMono (t.2 kclk coef A a ha) (classLE_max3_2 _ _ _) (le_max3_2 _ _ _)
          hash := hashMono (h.2 kclk coef A a ha) (classLE_max3_3 _ _ _) (le_max3_3 _ _ _) }⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin
