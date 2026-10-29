import NineInputs

/-! # An `E^NP` certificate is a deterministic computation that pins its language

A check of `InENP` in the trusted statement, the `E^NP` membership required of the hard language in the
main theorem (`thm:main`); `SourceMapping/main-theorem.md` (item 6) describes
the model.

The execution semantics of an oracle program (`OrdinaryOracleStep`, `OrdinaryOracleTrace`,
`OrdinaryOracleRuns`) are inductive relations, not functions. If they allowed two different runs on one
input, a single certificate could "compute" both answers and `InENP` would hold for every language, making the
hardness conclusion meaningless. Likewise, the oracle in `InENP` is an arbitrary function `ℕ → Bool`
constrained only by its NP verifier. This module proves that neither freedom exists:

* `frame_append_inj`: framed words are a prefix code, so a query tape determines its query word.
* `oracleStep_det`, `oracleTrace_det`: one step, and a run to a halted state, are deterministic.
* `oracleRuns_output_unique`: a program and an oracle produce at most one output on each input.
* `certificate_determines_language`: two languages certified by the same program against the same oracle
  are equal, so a certificate pins its language.
* `oracle_determined`: an NP verifier with its polynomial bound pins its oracle.
-/

namespace NearCubicGates.StatementChecks.ENPDeterminism

open NearCubicGates.Target NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource

set_option autoImplicit false

/-- Framing is a prefix code: `frame a ++ p = frame b ++ q` forces `a = b` and `p = q`. -/
theorem frame_append_inj : ∀ (a b p q : List Bool),
    RepairSource.frame a ++ p = RepairSource.frame b ++ q → a = b ∧ p = q
  | [], [], p, q, h => by simpa [RepairSource.frame, RepairOrdinary.frame] using h
  | [], _ :: _, _, _, h => by simp [RepairSource.frame, RepairOrdinary.frame] at h
  | _ :: _, [], _, _, h => by simp [RepairSource.frame, RepairOrdinary.frame] at h
  | x :: xs, y :: ys, p, q, h => by
      simp only [RepairSource.frame, RepairOrdinary.frame, List.cons_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hxy, h'⟩ := h
      obtain ⟨h1, h2⟩ := frame_append_inj xs ys p q h'
      exact ⟨by rw [hxy, h1], h2⟩

/-- One step of an oracle program is deterministic, in its cost and in its successor. -/
theorem oracleStep_det {oracle : ℕ → Bool} {p : OrdinaryOracleProgram} {c1 c2 : ℕ}
    {a m1 m2 : p.Config}
    (h1 : OrdinaryOracleStep oracle p c1 a m1) (h2 : OrdinaryOracleStep oracle p c2 a m2) :
    c1 = c2 ∧ m1 = m2 := by
  rcases h1 with ⟨_, _, _, nq1, tr1⟩ | ⟨_, bits1, pad1, rule1, _, aq1, _, wq1⟩
  · rcases h2 with ⟨_, _, _, _, tr2⟩ | ⟨_, _, _, _, _, aq2, _, _⟩
    · rw [tr1] at tr2
      exact ⟨rfl, Option.some.inj tr2⟩
    · rw [nq1] at aq2
      cases aq2
  · rcases h2 with ⟨_, _, _, nq2, _⟩ | ⟨_, bits2, pad2, rule2, _, aq2, _, wq2⟩
    · rw [aq1] at nq2
      cases nq2
    · rw [aq1] at aq2
      cases aq2
      rw [wq1] at wq2
      obtain ⟨hb, _⟩ := frame_append_inj _ _ _ _ wq2
      subst hb
      exact ⟨rfl, rfl⟩

/-- No step leaves a halted configuration. -/
theorem oracleStep_notHalted {oracle : ℕ → Bool} {p : OrdinaryOracleProgram} {c : ℕ}
    {a m : p.Config} (h : OrdinaryOracleStep oracle p c a m) :
    p.base.machine.halted a.control = false := by
  rcases h with ⟨_, _, nh, _, _⟩ | ⟨_, _, _, _, nh, _, _, _⟩ <;> exact nh

/-- Two runs from one configuration that both end in halted configurations end in the same one. -/
theorem oracleTrace_det {oracle : ℕ → Bool} {p : OrdinaryOracleProgram} {c1 : ℕ}
    {a f1 : p.Config} (h1 : OrdinaryOracleTrace oracle p c1 a f1) :
    p.base.machine.halted f1.control = true →
    ∀ {c2 : ℕ} {f2 : p.Config}, OrdinaryOracleTrace oracle p c2 a f2 →
      p.base.machine.halted f2.control = true → f1 = f2 := by
  induction h1 with
  | refl x =>
    intro hf1 c2 f2 h2 hf2
    cases h2 with
    | refl _ => rfl
    | cons s _ =>
      have hs := oracleStep_notHalted s
      simp_all
  | cons s1 _ ih =>
    intro hf1 c2 f2 h2 hf2
    cases h2 with
    | refl _ =>
      have hs := oracleStep_notHalted s1
      simp_all
    | cons s2 t2 =>
      obtain ⟨_, hm⟩ := oracleStep_det s1 s2
      subst hm
      exact ih hf1 t2 hf2

/-- A program and an oracle produce at most one output on each input, whatever the step budgets. -/
theorem oracleRuns_output_unique {oracle : ℕ → Bool} {p : OrdinaryOracleProgram}
    {input o1 o2 : List Bool} {b1 b2 : ℕ}
    (h1 : OrdinaryOracleRuns oracle p input o1 b1) (h2 : OrdinaryOracleRuns oracle p input o2 b2) :
    o1 = o2 := by
  obtain ⟨_, f1, -, t1, hf1, out1⟩ := h1
  obtain ⟨_, f2, -, t2, hf2, out2⟩ := h2
  have hf := oracleTrace_det t1 hf1 t2 hf2
  subst hf
  rw [out1] at out2
  exact (frame_append_inj o1 o2 [] [] (by simpa using out2)).1

/-- Two languages certified by the same program against the same oracle are equal. -/
theorem certificate_determines_language {oracle : ℕ → Bool} {F G : Language}
    (cF : OrdinaryENPCertificate oracle F) (cG : OrdinaryENPCertificate oracle G)
    (h : cF.program = cG.program) : F = G := by
  funext n x
  have hF := cF.computes n x
  have hG := cG.computes n x
  rw [h] at hF
  have hout := oracleRuns_output_unique hF hG
  cases hFx : F n x <;> cases hGx : G n x <;> simp_all

/-- Two oracles with the same NP verifier and the same polynomial bound are equal. -/
theorem oracle_determined {o1 o2 : ℕ → Bool} (v1 : EncodedNPVerifier o1) (v2 : EncodedNPVerifier o2)
    (hv : v1.verifier = v2.verifier) (hc : v1.coefficient = v2.coefficient)
    (hd : v1.degree = v2.degree) : o1 = o2 := by
  funext code
  have a := v1.correct code
  have b := v2.correct code
  rw [hv, hc, hd, ← b] at a
  exact Bool.eq_iff_iff.mpr (by simpa using a)

end NearCubicGates.StatementChecks.ENPDeterminism
