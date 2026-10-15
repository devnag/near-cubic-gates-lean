import Proof.Wire_3_5.RecoveryLanguage

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.ProjectionPCPPadding (padProjectionPCP padProjectionPCP_complete)
open Filter

section Facts
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem recSetup_hind {N : ℕ} (z : BitInput N) :
    ∀ u v, (recSetup l G kclk coef A a ha).pcp.decision z u = (recSetup l G kclk coef A a ha).pcp.decision z v :=
  fun _ _ => (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.decisionIndependent _ z _ _

/-- **Perfect completeness** at a hierarchy yes-instance, through the padding. -/
theorem recSetup_complete {N : ℕ} (z : BitInput N) (hyes : recL l kclk N z = true) :
    ∃ proof, ∀ randomness, (recSetup l G kclk coef A a ha).pcp.accepts z proof randomness = true := by
  have hH := Classical.choose_spec (recL_inNTIME l kclk)
  have hacc : (hierarchyOf (recL_inNTIME l kclk)).timedView.accepts N z = true :=
    (hierarchy_language_exact _ N z).2 ((hH N z).1 hyes)
  obtain ⟨proof, hproof⟩ := (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.complete N z hacc
  exact padProjectionPCP_complete _ _ _ z ⟨proof, hproof⟩

/-- The padded width is the ledger's `q(N)` eventually. -/
theorem recSetup_width (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∀ᶠ N in atTop, (recSetup l G kclk coef A a ha).pcp.nativeWidth N = nativeWidth kclk G.Apad N := by
  obtain ⟨N₀, h⟩ := unionSetupS1_width l G kclk coef A a ha (recL l kclk) (recL_inNTIME l kclk) hApad
  exact eventually_atTop.2 ⟨N₀, h⟩

theorem request_arity {N : ℕ} (z : BitInput N)
    (oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N)) :
    ((recSetup l G kclk coef A a ha).request z oracle).arity =
      max ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) (gatePCPP l).minimumArity := rfl

theorem clogN_le_nativeWidth (A' N : ℕ) : Nat.clog 2 N ≤ nativeWidth kclk A' N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  · have h1 : N ≤ N ^ (kclk + 2) := Nat.le_self_pow (by omega) N
    exact (Nat.clog_mono_right 2 h1).trans (Ledger.clog_le_nativeWidth kclk A' N)

theorem tendsto_nativeWidth (A' : ℕ) : Tendsto (nativeWidth kclk A') atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun N hN => ?_⟩
  calc b = Nat.clog 2 (2 ^ b) := (Nat.clog_pow 2 b (by norm_num)).symm
    _ ≤ Nat.clog 2 N := Nat.clog_mono_right 2 hN
    _ ≤ nativeWidth kclk A' N := clogN_le_nativeWidth kclk A' N

/-- **The request's arity is `q(N)`** eventually. -/
theorem eventually_request_arity (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∀ᶠ N in atTop, (recSetup l G kclk coef A a ha).pcp.nativeWidth N = nativeWidth kclk G.Apad N ∧
      ∀ (z : BitInput N) (oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N)),
        ((recSetup l G kclk coef A a ha).request z oracle).arity = nativeWidth kclk G.Apad N := by
  filter_upwards [recSetup_width l G kclk coef A a ha hApad,
    (tendsto_nativeWidth kclk G.Apad).eventually (eventually_ge_atTop (gatePCPP l).minimumArity)] with N hw hm
  refine ⟨hw, fun z oracle => ?_⟩
  rw [request_arity, hw]
  exact max_eq_left hm

end Facts

end NearCubicWires.WireExponent3_5.Transfer
