import Proof.Gates.Outer.CircuitEval
import Proof.Gates.Outer.Count
import Proof.Gates.Outer.Width
import Proof.Foundations.BooleanCircuitSizePadding

/-!
# The short PCP applied once per clock: the width, `D_B`, its soundness and the honest oracle

Paper §11.4 ("We apply imp:short-pcp once, to 𝒱_G with the time bound T_G"): on the instance `⟨B_src⟩_ν` the import
returns `C`, with `ℓ_out ≤ q(N)` ("A_pad … so that ℓ_out ≤ q(N)"); the guessed `B_pf` is substituted for the oracle,
giving "the outer verifier D_B(x) = ¬C^{O_{B_pf}}_{⟨B_src⟩_ν}(x_1, …, x_{ℓ_out}), x ∈ {0,1}^q". If CHECK passes and the source input is a
hierarchy no-instance, `D_B` accepts at most a `1/L_ν` fraction of its inputs (MW's soundness `1 − 1/n` at
`n = L_ν`); if it is a yes-instance, some oracle makes `C` unsatisfiable (MW's completeness).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.Bindings.MW20
open NearCubicWires.Bindings.CLW20Lemma311

section
variable (mw : MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : SuccinctVerifier H G)

/-- The import applied to `𝒱_G` (paper §11.4: "We apply imp:short-pcp once, to 𝒱_G with the time bound T_G"). -/
noncomputable def alg : MWSourceAlgorithm SV.V SV.T :=
  Classical.choice (mw SV.V SV.T SV.atLeast SV.runs)

/-- `A_pad`, fixed after the import's constants for `𝒱_G` (paper App. C, the constant order, items 5–6). -/
noncomputable def apad : ℕ :=
  padConst (alg mw SV).coefficient SV.timeCoefficient (alg mw SV).ellExp + 1

/-- The native width `q(N)` (paper §11.4, unchanged formula). -/
noncomputable def width (N : ℕ) : ℕ := widthOf k (apad mw SV) N

/-- `C^O` for the instance `⟨B_src⟩_ν`. -/
noncomputable def outC (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : OracleOutput :=
  (alg mw SV).output (srcInput G ν B)

/-- `D_B` at source index `ν` for a pair guessed on the width at any length `N` (the weak machine's form; `N = 2^ν`
in every use): `¬C^{B_pf(·,0)}` on `q` inputs, size-padded to its arity (as the old `substitutedCircuit`). -/
noncomputable def Dat (ν : ℕ) {N : ℕ} (B : OuterGuess (width mw SV N)) : Circuit :=
  ⟨width mw SV N, (substCircuit (outC mw SV ν B.src).circuit B.pf).padToArity,
    BooleanCircuit.arity_le_padToArity_size _⟩

/-- `D_B` at `N = 2^ν`. -/
noncomputable def D (ν : ℕ) (B : OuterGuess (width mw SV (2 ^ ν))) : Circuit := Dat mw SV ν B

theorem Dat_eval (ν : ℕ) {N : ℕ} (B : OuterGuess (width mw SV N)) (r : BitInput (width mw SV N)) :
    (Dat mw SV ν B).D.eval r =
      !((outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) (truncInput r)) := by
  simp only [Dat, BooleanCircuit.padToArity_eval]
  exact subst_eval _ _ r

theorem D_n (ν : ℕ) (B : OuterGuess (width mw SV (2 ^ ν))) : (D mw SV ν B).n = width mw SV (2 ^ ν) := rfl

theorem Dat_n (ν : ℕ) {N : ℕ} (B : OuterGuess (width mw SV N)) : (Dat mw SV ν B).n = width mw SV N := rfl

theorem D_eval (ν : ℕ) (B : OuterGuess (width mw SV (2 ^ ν))) (r : BitInput (width mw SV (2 ^ ν))) :
    (D mw SV ν B).D.eval r =
      !((outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) (truncInput r)) := by
  exact Dat_eval mw SV ν B r

/-- `D_B` is a tautology when `B_pf` answers as an honest oracle (Case 2, paper v2 §11.5). -/
theorem D_eval_true (ν : ℕ) (B : OuterGuess (width mw SV (2 ^ ν)))
    (O : BitInput (outC mw SV ν B.src).ell → Bool) (hO : ∀ a, B.pf.eval (padQuery a) = O a)
    (hhon : ∀ w, (outC mw SV ν B.src).circuit.eval O w = false) (x : BitInput (width mw SV (2 ^ ν))) :
    (D mw SV ν B).D.eval x = true := by
  rw [D_eval]
  have hf : (fun a => B.pf.eval (padQuery a)) = O := funext hO
  rw [hf, hhon]
  rfl

theorem instLength_pos (ν : ℕ) (hν : 1 ≤ ν) : 1 ≤ instLength G ν := by
  unfold instLength
  exact Nat.one_le_pow _ _ hν

/-- `ℓ_out ≤ q` from the onset of `𝒱_G` on (paper §11.4: "so that ℓ_out ≤ q(N)"). -/
theorem ell_le_width (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) (hon : SV.onset ≤ ν) (hν : 1 ≤ ν) :
    (outC mw SV ν B).ell ≤ width mw SV (2 ^ ν) := by
  have hl := (alg mw SV).ellBound (srcInput G ν B) (instLength_pos ν hν)
  have hT := SV.timeBound ν hon
  set K := (alg mw SV).coefficient
  set e := (alg mw SV).ellExp
  set c := SV.timeCoefficient
  have hN : 1 ≤ 2 ^ ν := Nat.one_le_two_pow
  have henv := envelope_le K c e k (2 ^ ν) hN
  have hmono : K * SV.T (instLength G ν) * logScale (SV.T (instLength G ν)) ^ e ≤
      K * (c * (2 ^ ν) ^ (k + 2)) * logScale (c * (2 ^ ν) ^ (k + 2)) ^ e := by
    gcongr
    unfold logScale
    exact Nat.clog_mono_right _ (by omega)
  have hpow : 2 ^ (outC mw SV ν B).ell ≤ 2 ^ widthOf k (padConst K c e) (2 ^ ν) :=
    (hl.trans hmono).trans henv
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  refine hle.trans ?_
  unfold width apad widthOf
  have : Nat.clog 2 (clkLog k (2 ^ ν) + 2) * padConst K c e ≤ Nat.clog 2 (clkLog k (2 ^ ν) + 2) * (padConst K c e + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Completeness** (paper §11.5, Case 1 (iii) and Case 2): if CHECK passes on a hierarchy yes-instance, some oracle makes
`C^O_{⟨B_src⟩_ν}` unsatisfiable. -/
theorem honest (ν : ℕ) (z : BitInput (2 ^ ν)) {m : ℕ} (B : BooleanCircuit m) (hon : SV.onset ≤ ν) (hν : 1 ≤ ν)
    (hm : ν ≤ m) (hfit : SrcFits G ν B) (hcheck : Check ν z B) (hyes : H.verifier.language H.time (2 ^ ν) z) :
    ∃ O : BitInput (outC mw SV ν B).ell → Bool, ∀ w, (outC mw SV ν B).circuit.eval O w = false := by
  have hL := (SV.language ν m B hon hν hm hfit).mpr (by rw [hcheck]; exact hyes)
  exact (alg mw SV).complete (srcInput G ν B) (instLength_pos ν hν) hL

/-- **Soundness** (paper §11.4: "On a hierarchy no-instance z, consider a branch whose source circuit passes the
check … Hence D_B(x) = 1 on at most a 1/L_ν fraction of inputs"), for every `B_pf`. -/
theorem sound (ν : ℕ) (z : BitInput (2 ^ ν)) (B : OuterGuess (width mw SV (2 ^ ν))) (hon : SV.onset ≤ ν)
    (hν : 1 ≤ ν) (hfit : SrcFits G ν B.src) (hcheck : Check ν z B.src)
    (hno : ¬ H.verifier.language H.time (2 ^ ν) z) :
    ((Finset.univ.filter fun r => (D mw SV ν B).D.eval r = true).card : ℝ) ≤
      (2 : ℝ) ^ width mw SV (2 ^ ν) / (instLength G ν : ℝ) := by
  have hL : ¬ SV.V.language SV.T (instLength G ν) (srcBits G ν B.src) := by
    intro hyes
    have hm : ν ≤ width mw SV (2 ^ ν) := by
      have := succ_le_widthOf k (apad mw SV) ν (by unfold apad; omega)
      unfold width
      omega
    exact hno (by rw [← hcheck]; exact (SV.language ν _ B.src hon hν hm hfit).mp hyes)
  have hsat := (alg mw SV).sound (srcInput G ν B.src) (instLength_pos ν hν) hL
    (fun a => B.pf.eval (padQuery a))
  have hle : (outC mw SV ν B.src).ell ≤ width mw SV (2 ^ ν) := ell_le_width mw SV ν B.src hon hν
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BitInput (outC mw SV ν B.src).ell)))
    (fun w => (outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) w = true)
  simp only [Finset.card_univ, Bool.not_eq_true] at hsplit
  have hunsat : (((Finset.univ.filter fun w =>
      (outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) w = false).card : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (outC mw SV ν B.src).ell / (instLength G ν : ℝ) := by
    have hpos : (0 : ℝ) < (instLength G ν : ℝ) := by exact_mod_cast instLength_pos ν hν
    rw [le_div_iff₀ hpos]
    have hs : (2 : ℝ) ^ (outC mw SV ν B.src).ell * (1 - 1 / (instLength G ν : ℝ)) ≤
        ((outC mw SV ν B.src).satCount (fun a => B.pf.eval (padQuery a)) : ℝ) := hsat
    have hcard : (((outC mw SV ν B.src).satCount (fun a => B.pf.eval (padQuery a)) : ℕ) : ℝ) +
        (((Finset.univ.filter fun w =>
          (outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) w = false).card : ℕ) : ℝ) =
        (2 : ℝ) ^ (outC mw SV ν B.src).ell := by
      unfold OracleOutput.satCount
      rw [← Nat.cast_add, hsplit]
      simp [BitInput]
    have hexp : (2 : ℝ) ^ (outC mw SV ν B.src).ell * (1 - 1 / (instLength G ν : ℝ)) =
        (2 : ℝ) ^ (outC mw SV ν B.src).ell - (2 : ℝ) ^ (outC mw SV ν B.src).ell / (instLength G ν : ℝ) := by ring
    rw [hexp] at hs
    have hdiv : (2 : ℝ) ^ (outC mw SV ν B.src).ell / (instLength G ν : ℝ) * (instLength G ν : ℝ) =
        (2 : ℝ) ^ (outC mw SV ν B.src).ell := by
      field_simp
    nlinarith
  have hD : (Finset.univ.filter fun r => (D mw SV ν B).D.eval r = true) =
      (Finset.univ.filter fun r : BitInput (width mw SV (2 ^ ν)) =>
        (outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) (truncInput r) = false) := by
    apply Finset.filter_congr
    intro r _
    rw [D_eval]
    simp
  have hc := card_trunc hle (fun w => (outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) w = false)
  beta_reduce at hc
  rw [hD]
  erw [hc]
  push_cast
  calc (2 : ℝ) ^ (width mw SV (2 ^ ν) - (outC mw SV ν B.src).ell) *
        (((Finset.univ.filter fun w =>
          (outC mw SV ν B.src).circuit.eval (fun a => B.pf.eval (padQuery a)) w = false).card : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (width mw SV (2 ^ ν) - (outC mw SV ν B.src).ell) *
        ((2 : ℝ) ^ (outC mw SV ν B.src).ell / (instLength G ν : ℝ)) := by gcongr
    _ = (2 : ℝ) ^ width mw SV (2 ^ ν) / (instLength G ν : ℝ) := by
      rw [mul_div_assoc', ← pow_add, Nat.sub_add_cancel hle]

/-- **Soundness at a source length `N = 2^ν`** (the weak machine's form of `sound`). -/
theorem sound_at (ν N : ℕ) (hN : N = 2 ^ ν) (z : BitInput N) (B : OuterGuess (width mw SV N))
    (hon : SV.onset ≤ ν) (hν : 1 ≤ ν) (hfit : SrcFits G ν B.src) (hcheck : CheckAt ν z B.src)
    (hno : ¬ H.verifier.language H.time N z) :
    ((Finset.univ.filter fun r => (Dat mw SV ν B).D.eval r = true).card : ℝ) ≤
      (2 : ℝ) ^ width mw SV N / (instLength G ν : ℝ) := by
  subst hN
  exact sound mw SV ν z B hon hν hfit ((check_iff_checkAt ν z B.src).mpr hcheck) hno

end

end NearCubicGates.Close.Outer
