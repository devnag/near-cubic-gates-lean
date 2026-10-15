import StatementSupport

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5
open NearCubicWires NearCubicWires.RepairSource

noncomputable def WireExponent3_5Hard (c KT KS : ℝ) (language : Language) : Prop :=
  ∀ AT AS : ℝ, 0 < AT → 0 < AS →
    ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
      (∀ circuit : ThresholdThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            if circuit.topWeight i = 0 then 0
            else (circuit.bottom i).support.card + 1 : ℕ) : ℝ) ≤
          AT * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KT →
        ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) <
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)) ∧
      (∀ circuit : SymmetricThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            ((circuit.bottom i).support.card + 1) : ℕ) : ℝ) ≤
          AS * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KS →
        ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) <
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c))

noncomputable def _root_.NearCubicWires.WireExponent3_5 (c KT KS : ℝ) : Prop :=
  ∃ language : Language,
    (∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
        Nonempty (OrdinaryENPCertificate oracle language)) ∧
    WireExponent3_5Hard c KT KS language

noncomputable def rowB : Prop := WireExponent3_5 (1 / 8) (11 / 2) (9 / 2)

/-- The nine literal hypotheses of the Theorem 2.5 artifact (`Check.lean`, `MainTheorem.lean`), in order. Each
field is one literal Prop of `Statement`, transcribing a printed statement of the cited paper. -/
structure Literals : Prop where
  ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2
  cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2
  williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4
  hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2
  rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314
  clw310 : NearCubicWires.Bindings.CLW20Lemma310TM2.CLW20_Lemma3_10_TM2
  clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2
  clw113 : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13
  clw39 : NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2

end NearCubicWires.WireExponent3_5
