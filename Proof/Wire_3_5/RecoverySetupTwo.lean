import Proof.Wire_3_5.RecoveryLeaf
import Proof.Wire_3_5.PadCast
import Proof.CaseAnalysis.NativeWidthStep

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

section S2
variable (l : Literals) (G : Split.Gate)

/-- The refuter's hierarchy at the clock `N^{kclk+2}`. -/
noncomputable def refH (kclk : ℕ) : OrdinaryHierarchy (fun n => n ^ (kclk + 2)) := (recRefuter l kclk).hierarchy

theorem refH_spec (kclk : ℕ) :
    ∀ n (x : BitInput n), recL l kclk n x = true ↔ (refH l kclk).verifier.language (refH l kclk).time n x :=
  fun n x => hierarchy_language_exact _ n x

/-- The refuter hierarchy's native outer PCP (width `R(N)`). -/
noncomputable def recPCP (kclk : ℕ) := (hierarchyPCP l (refH l kclk)).data

/-- **The setup at the recovered language**: the refuter hierarchy's own PCP padded to `q(N)`. -/
noncomputable def recSetup2 (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : UnionSetup (G.inputs kclk coef A a ha) :=
  setupOfResult (G.inputs kclk coef A a ha) (recL l kclk) (refH l kclk) (refH_spec l kclk) (recPCP l kclk)
    (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l) (recOracleDeg l) (gateParams1 l)
    (gridMassOf (gateCδ1 l) G.row.sp) (fun _ => by unfold gridMassOf; positivity) G.row.sp

/-- **The re-pinned union setup `S₂`**: the refuter hierarchy's own PCP at `recL`, `S₁` elsewhere. -/
noncomputable def unionSetupS2 : G.Setup := fun kclk coef A a ha L hL => by
  classical
  exact if h : L = recL l kclk then
    setupOfResult (G.inputs kclk coef A a ha) L (refH l kclk) (by subst h; exact refH_spec l kclk) (recPCP l kclk)
      (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l) (recOracleDeg l) (gateParams1 l)
      (gridMassOf (gateCδ1 l) G.row.sp) (fun _ => by unfold gridMassOf; positivity) G.row.sp
  else unionSetupS1 l G kclk coef A a ha L hL

theorem unionSetupS2_recL (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (hL : InNTIME (fun n => n ^ (kclk + 2)) (recL l kclk)) :
    unionSetupS2 l G kclk coef A a ha (recL l kclk) hL = recSetup2 l G kclk coef A a ha := by
  unfold unionSetupS2
  rw [dif_pos rfl]
  rfl

theorem recSetup2_G (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : (recSetup2 l G kclk coef A a ha).G = recOracleDeg l := rfl

theorem recSetup2_params (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    (recSetup2 l G kclk coef A a ha).params = gateParams1 l := rfl

/-- The padded width is the ledger's `q(N)` eventually. -/
theorem recSetup2_width (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∃ N₀, ∀ N, N₀ ≤ N →
      (recSetup2 l G kclk coef A a ha).pcp.nativeWidth N = Ledger.nativeWidth kclk G.Apad N := by
  obtain ⟨N₀, hN₀⟩ := width_le_nativeWidth kclk (5 + (gateSource l).degrees.proofLog)
    (recPCP l kclk).coefficient (refH l kclk).coefficient
    (fun N => (recPCP l kclk).pcp.nativeWidth N)
    (fun n hn => (recPCP l kclk).proofBound n hn)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := hN₀ N hN
  have hmono : Ledger.nativeWidth kclk (5 + (gateSource l).degrees.proofLog + 1) N ≤
      Ledger.nativeWidth kclk G.Apad N := by
    unfold Ledger.nativeWidth
    have : 5 + (gateSource l).degrees.proofLog + 1 ≤ G.Apad := by omega
    have := Nat.mul_le_mul_right (Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2)) this
    omega
  show max _ _ = _
  exact max_eq_right (h1.trans hmono)

/-- The native width at dyadic lengths is at least the index plus one (base's `native_dyadic_lower`). -/
theorem native_lower (kclk s : ℕ) : s + 1 ≤ (recPCP l kclk).pcp.nativeWidth (2 ^ s) :=
  CloseoutNativeWidth.native_dyadic_lower (gateSource l) (refH l kclk) _ s

theorem recSetup2_hind (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {N : ℕ} (z : BitInput N) :
    ∀ u v, (recSetup2 l G kclk coef A a ha).pcp.decision z u = (recSetup2 l G kclk coef A a ha).pcp.decision z v :=
  fun _ _ => (recPCP l kclk).decisionIndependent _ z _ _

/-- Perfect completeness of the native PCP at a hierarchy yes-instance. -/
theorem recPCP_complete (kclk : ℕ) {N : ℕ} (z : BitInput N) (hyes : recL l kclk N z = true) :
    ∃ proof, ∀ randomness, (recPCP l kclk).pcp.accepts z proof randomness = true := by
  have hacc : (refH l kclk).timedView.accepts N z = true :=
    (hierarchy_language_exact _ N z).2 ((refH_spec l kclk N z).1 hyes)
  exact (recPCP l kclk).complete N z hacc

end S2

end NearCubicWires.WireExponent3_5.Transfer
