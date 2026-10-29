import Proof.Gates.Closure.Obligations
import Proof.CaseAnalysis.WeakSelectedRuntime
import Proof.Circuits.PolynomialOrdinaryClock
import Proof.Gates.Transfer.Schedule
import Proof.Gates.Transfer.LenFit
import Proof.Gates.Worker.NativeLower

set_option autoImplicit false

namespace NearCubicGates.Close.Closure

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.RepairSource.CloseoutWeakRuntime
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer NearCubicGates.Close.Worker
open NearCubicGates.PublishedSources.PCPP

theorem gate_littleO (s : GateSources) (g : GateParams)
    (M : OrdinaryWeakMachine) (A B a sigma : ℕ) (hot : ℕ → ℕ)
    (ha : a ≤ g.k + 1) (hs : Outer.apad s.mw (g.sv s) + 1 ≤ sigma)
    (bound : ∃ onset, ∀ N, onset ≤ N →
      M.runtime N ≤ A * (N + 1) ^ a + hot N ∧ hot N * (width s g N) ^ sigma ≤ B * 2 ^ (width s g N)) :
    OrdinaryLittleO M (fun n => n ^ (g.k + 2)) := by
  have hA : 1 ≤ Outer.apad s.mw (g.sv s) := by unfold Outer.apad; omega
  apply littleO_of_split M g.k A B (3 * 12 ^ Outer.apad s.mw (g.sv s)) a (Outer.apad s.mw (g.sv s)) sigma
    (width s g) hot ha hs
  · intro m
    exact ⟨2 ^ m, fun N hN => gate_nativeWidth_ge s g m N hN⟩
  · obtain ⟨onset, hbound⟩ := bound
    refine ⟨max onset 1, ?_⟩
    intro N hn
    obtain ⟨hr, hh⟩ := hbound N ((Nat.le_max_left _ _).trans hn)
    exact ⟨hr, hh, Outer.widthOf_table g.k _ N ((Nat.le_max_right _ _).trans hn) hA⟩

/-- `𝒜₃ → ∞`, and eventually `0 ≤ 𝒜₃(q) ≤ q³` and `𝒜₃(q) ≤ 𝒜₁(q)`. -/
def AsymptoticsFacts : Prop :=
  (∀ M : ℝ, ∃ q0 : ℕ, ∀ q, q0 ≤ q → M ≤ A3 q) ∧
    ∃ q0 : ℕ, ∀ q, q0 ≤ q → 0 ≤ A3 q ∧ A3 q ≤ (q : ℝ) ^ 3 ∧ A3 q ≤ A1 q

def ClauseRoom (s : GateSources) (P : ThreeQueryPCPP) : Prop :=
  ∀ g : GateParams, ∃ d onset : ℕ, 1 ≤ d ∧ ∀ (N : ℕ) (x : BitInput N) (B : Outer.OuterGuess (width s g N)),
    B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N) → onset ≤ width s g N → 2 ≤ N →
    (P.output (checkedCircuit P.code (substituted s g x B))).randomBits ≤ clauseWidth d (width s g N)

theorem list_ofFn_getD (bits : List Bool) {m : ℕ} (h : bits.length = m) :
    List.ofFn (fun i : Fin m => bits.getD i.val false) = bits := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-! The outer PCP and the refuter are used, never unfolded, in the assembly below. -/
attribute [local irreducible] GateSources.hierarchy

/-- Transport of the Case 2 data along an equality of outer verifiers. -/
theorem hardTable_transport (P : ThreeQueryPCPP) {D1 D2 : NearCubicWires.Bindings.CLW20Lemma311.Circuit} (h : D1 = D2)
    (hD2 : ∀ x, D2.D.eval x = true) (cl pl : ℕ) (C2 : NearCubicGates.Target.WeightedSymmetricCircuit (D2.n + cl + pl)) :
    ∃ (hD1 : ∀ x, D1.D.eval x = true) (C1 : NearCubicGates.Target.WeightedSymmetricCircuit (D1.n + cl + pl)),
      C1.topWeight = C2.topWeight ∧
      NearCubicGates.FiniteAverages.agreement C1.eval (hardTable P D1 hD1 cl pl) =
        NearCubicGates.FiniteAverages.agreement C2.eval (hardTable P D2 hD2 cl pl) := by
  subst h
  exact ⟨hD2, C2, rfl, rfl⟩

/-- At `N = 2^ν` the worker's outer verifier is the transfer side's `D_B`. -/
theorem substituted_pow (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν))
    (B : Outer.OuterGuess (width s g (2 ^ ν))) : substituted s g z B = g.D s ν B := by
  show Outer.Dat s.mw (g.sv s) (Nat.log 2 (2 ^ ν)) B = Outer.Dat s.mw (g.sv s) ν B
  rw [Nat.log_pow (by norm_num)]

/-- **ClosureSupply** from the machine obligations and the two pure facts. -/
theorem closureSupply_of (hC : CounterSupply) (hW : WorkerSupply) (hA : AsymptoticsFacts)
    (hR : ∀ s P, ClauseRoom s P) : ClosureSupply := by
  classical
  intro s P ε hε hεγ
  obtain ⟨B1, B2, hB1, hB2, ctr, hden, hout⟩ := hC s
  obtain ⟨aC, haC, onsetC, hcomp⟩ := ctr.complete
  obtain ⟨hgrow, qA, hAq⟩ := hA
  have hγ1 : (P.gamma : ℝ) < 1 := by exact_mod_cast P.gamma_lt_one
  have hε1 : ε < 1 := by linarith
  -- the radius `ω ≤ min(ε/128, 1/16)`
  obtain ⟨ω, hω0, hωlt⟩ := exists_rat_btwn (show (0 : ℝ) < min (ε / 128) (1 / 16) by positivity)
  have hω0' : (0 : ℚ) < ω := by exact_mod_cast hω0
  have hωε : (ω : ℝ) ≤ ε / 128 := le_of_lt (lt_of_lt_of_le hωlt (min_le_left _ _))
  have hω16 : ω ≤ 1 / 16 := by
    have h := le_of_lt (lt_of_lt_of_le hωlt (min_le_right _ _))
    have h' : ((ω : ℚ) : ℝ) ≤ ((1 / 16 : ℚ) : ℝ) := by push_cast; exact h
    exact_mod_cast h'
  -- the machine threshold `ε < ε_T < 2ε`
  obtain ⟨εT, hεT1, hεT2⟩ := exists_rat_btwn (show ε < 2 * ε by linarith)
  have hεT0 : (0 : ℝ) < εT := by linarith
  -- the weight budget `b = budgetOf η` with rational `0 < η ≤ min(aω/2, 1/2)` (Closure/Budget.lean)
  obtain ⟨η, hη0r, hηlt⟩ := exists_rat_btwn (show (0 : ℝ) < min (aC * ω / 2) (1 / 2) by positivity)
  have hη0 : (0 : ℚ) < η := by exact_mod_cast hη0r
  have hηa : (η : ℝ) ≤ aC * ω / 2 := (lt_of_lt_of_le hηlt (min_le_left _ _)).le
  have hη1 : (η : ℝ) ≤ 1 / 2 := (lt_of_lt_of_le hηlt (min_le_right _ _)).le
  set budget : ℕ → ℕ := budgetOf η with hbudget
  obtain ⟨d0, hWs⟩ := hW s P B1 B2 ctr η εT ω hden hout hη0 hω0'
  have hqA4 : ∀ q, max qA 4 ≤ q → 4 ≤ q ∧ qA ≤ q := fun q hq => ⟨(le_max_right _ _).trans hq,
    (le_max_left _ _).trans hq⟩
  have hbud_le : ∀ q, max qA 4 ≤ q → (budget q : ℝ) ≤ η * A3 q := fun q hq =>
    (budgetOf_bounds η hη0 q (hqA4 q hq).1).1
  have hcubic : ∀ q, max qA 4 ≤ q → budget q ≤ q ^ 3 := by
    intro q hq
    obtain ⟨h0, h3, -⟩ := hAq q (hqA4 q hq).2
    have h := hbud_le q hq
    have : (budget q : ℝ) ≤ (q : ℝ) ^ 3 := by nlinarith
    exact_mod_cast this
  -- the position count `P = 2^{pl} > max(128/ε, 8)`
  obtain ⟨pl, hpl⟩ := pow_unbounded_of_one_lt (max (128 / ε) 8) (by norm_num : (1 : ℝ) < 2)
  have hpl8 : (8 : ℝ) < 2 ^ pl := lt_of_le_of_lt (le_max_right _ _) hpl
  have hpl128 : 128 / ε < 2 ^ pl := lt_of_le_of_lt (le_max_left _ _) hpl
  have hP : 128 ≤ ε * ((2 ^ pl : ℕ) : ℝ) := by
    push_cast
    have := (div_lt_iff₀ hε).1 hpl128
    linarith
  have hP5 : 5 ≤ 2 ^ pl := by
    have : (5 : ℝ) < 2 ^ pl := by linarith
    exact_mod_cast this.le
  have hpl1 : 1 ≤ pl := by
    rcases Nat.eq_zero_or_pos pl with h | h
    · subst h; norm_num at hpl8
    · exact h
  -- the degrees and the parameters (constant order of `app:multitape`: G, then G′, then the clock, then d_G)
  set degree := 17 * s.amplification.stvExponent with hdeg
  obtain ⟨lenRoot, hlenFit⟩ := Transfer.lenFit s degree
  set g0 : GateParams := ⟨d0 + 1, PolynomialClock.ordinaryClock (d0 + 1), degree, lenRoot, 0, pl,
    max 1 (selectedAmplifier s.amplification degree).arityCoefficient, 0⟩ with hg0
  obtain ⟨d, onsetR, hd1, hRoom⟩ := hR s P g0
  set g : GateParams := { g0 with clauseDegree := d } with hg
  obtain ⟨W⟩ := hWs g (show d0 ≤ d0 + 1 + 1 by omega)
  obtain ⟨onsetF, hfits⟩ := W.complete
  obtain ⟨fitOnset, hfitν⟩ := hlenFit g rfl rfl
  -- eventual thresholds on the native width
  obtain ⟨qG, hqG⟩ := hgrow (4 / (η : ℝ))
  set Q : ℕ := max (max (max 4 onsetC) (max (max qA 4) qG)) (max (max (Nat.ceil (1 / (ω : ℝ))) (ratWord ω).length) onsetR)
    with hQ
  refine ⟨{ g := g, budget := budget,
            ready := ⟨le_max_left _ _, ⟨(η : ℝ) / 4, by positivity, max (max qA 4) qG, ?_⟩, ⟨max qA 4, hcubic⟩, le_refl _,
              le_max_right _ _, hpl1, hd1, ⟨fitOnset, hfitν⟩⟩,
            M := Weak.machine W.worker W.htapes W.result W.fuel _
              (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total),
            littleO := ?_, oneSided := ?_, complete := ?_ }⟩
  · -- budgetLower: `b ≥ η𝒜₃/2 − 1 ≥ η𝒜₃/4` once `η𝒜₃ ≥ 4`
    intro q hq
    have hqa : max qA 4 ≤ q := (le_max_left _ _).trans hq
    have hqg : qG ≤ q := (le_max_right _ _).trans hq
    have hbig : 4 / (η : ℝ) ≤ A3 q := hqG q hqg
    have hηr : (0 : ℝ) < η := by exact_mod_cast hη0
    have hηA : 4 ≤ (η : ℝ) * A3 q := by
      have := mul_le_mul_of_nonneg_left hbig hηr.le
      rwa [mul_div_cancel₀ _ hηr.ne'] at this
    have hlo := (budgetOf_bounds η hη0 q (hqA4 q hqa).1).2
    show (η : ℝ) / 4 * A3 q ≤ (budgetOf η q : ℝ)
    nlinarith
  · -- littleO
    obtain ⟨on, hsplit⟩ := W.split
    exact gate_littleO s g _ W.A W.B W.a W.sigma W.hot W.ha W.hsigma
      ⟨on, fun N hN => by
        obtain ⟨h1, h2⟩ := hsplit N hN
        exact ⟨by rw [Weak.runtime_eq]; exact h1, h2⟩⟩
  · -- one-sided
    exact Weak.one_sided W.worker W.htapes W.result W.fuel _
      (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total)
      (fun n x => (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.timedView.accepts n x = true)
      (fun n x bits h => by
        obtain ⟨G, hG⟩ := W.sound n x bits h
        exact meaning_sound ctr budget (εT : ℝ) ω n x G hG)
  · -- completeness (`sec:gadget-extract`, case (Tautology))
    refine ⟨max (max (max Q onsetF) (Nat.ceil (1 / (εT : ℝ)))) (max fitOnset ((g.sv s).onset + 1)), ?_⟩
    intro ν hν z B hsrc hpf hcheck hD C0 hCw0 hagree0
    have hν' : max (max Q onsetF) (Nat.ceil (1 / (εT : ℝ))) ≤ ν := (le_max_left _ _).trans hν
    have hνfit : fitOnset ≤ ν := (le_max_left _ _).trans ((le_max_right _ _).trans hν)
    have hνsv : (g.sv s).onset + 1 ≤ ν := (le_max_right _ _).trans ((le_max_right _ _).trans hν)
    apply (Weak.accepts_exact W.worker W.htapes W.result W.fuel _
      (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total) (2 ^ ν) z).mpr
    have hνQ : Q ≤ ν := (le_max_left _ _).trans ((le_max_left _ _).trans hν')
    have hνF : onsetF ≤ ν := (le_max_right _ _).trans ((le_max_left _ _).trans hν')
    have hνε : Nat.ceil (1 / (εT : ℝ)) ≤ ν := (le_max_right _ _).trans hν'
    have hwid : ν + 1 ≤ width s g (2 ^ ν) := GateParams.width_lower s g ν
    have hqQ : Q ≤ width s g (2 ^ ν) := by omega
    have hq4 : 4 ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_left 4 onsetC).trans ((le_max_left _ _).trans (le_max_left _ _))) hqQ
    have hqC : onsetC ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_right 4 onsetC).trans ((le_max_left _ _).trans (le_max_left _ _))) hqQ
    have hqA' : max qA 4 ≤ width s g (2 ^ ν) :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hqQ
    have hqA : qA ≤ width s g (2 ^ ν) := (le_max_left _ _).trans hqA'
    have hqω : Nat.ceil (1 / (ω : ℝ)) ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))) hqQ
    have hqr : (ratWord ω).length ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))) hqQ
    have hqR : onsetR ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_right _ _).trans (le_max_right _ _)) hqQ
    have hn : 1 ≤ width s g (2 ^ ν) := by omega
    have hr1 : 1 ≤ ω * (width s g (2 ^ ν) : ℚ) ^ B1 := by
      have hq1 : (1 / (ω : ℝ)) ≤ width s g (2 ^ ν) := (Nat.le_ceil _).trans (by exact_mod_cast hqω)
      have hωq : (1 : ℝ) ≤ ω * width s g (2 ^ ν) := by
        rw [div_le_iff₀ hω0] at hq1; linarith
      have hpow : (width s g (2 ^ ν) : ℝ) ≤ (width s g (2 ^ ν) : ℝ) ^ B1 :=
        le_self_pow₀ (by exact_mod_cast hn) (by omega)
      have : (1 : ℝ) ≤ ω * (width s g (2 ^ ν) : ℝ) ^ B1 := by nlinarith
      exact_mod_cast this
    have hr3 : (ratWord ω).length ≤ width s g (2 ^ ν) ^ B2 :=
      hqr.trans (Nat.le_self_pow (by omega) _)
    have hb : (budget (width s g (2 ^ ν)) : ℝ) ≤ η * A3 (width s g (2 ^ ν)) := hbud_le _ hqA'
    obtain ⟨hA0, -, hA31⟩ := hAq _ hqA
    have hηA : 2 * (η : ℝ) * A3 (width s g (2 ^ ν)) ≤ aC * (ω : ℝ) * A3 (width s g (2 ^ ν)) :=
      mul_le_mul_of_nonneg_right (by linarith [hηa]) hA0
    have hA3c : (2 * budget (width s g (2 ^ ν)) : ℝ) ≤ aC * (ω : ℝ) * A3 (width s g (2 ^ ν)) := by
      linarith [hb, hηA]
    have hA1c : (budget (width s g (2 ^ ν)) : ℝ) ≤ aC * (ω : ℝ) * A1 (width s g (2 ^ ν)) := by
      have h1 : aC * (ω : ℝ) * A3 (width s g (2 ^ ν)) ≤ aC * (ω : ℝ) * A1 (width s g (2 ^ ν)) :=
        mul_le_mul_of_nonneg_left hA31 (by positivity)
      have hb0 : (0 : ℝ) ≤ (budget (width s g (2 ^ ν)) : ℝ) := by positivity
      linarith [hA3c, h1]
    have hb4 : budget (width s g (2 ^ ν)) ≤ width s g (2 ^ ν) ^ 4 :=
      (hcubic _ hqA').trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    -- `ν = log₂ 2^ν`, and the set-up's guards on the pair
    have hnu : nu (2 ^ ν) = ν := Nat.log_pow (by norm_num) ν
    have hν1 : 1 ≤ nu (2 ^ ν) := by rw [hnu]; omega
    have hprec : (P.gamma : ℝ) / (Outer.instLength g.lenExp (nu (2 ^ ν)) : ℝ) < (εT : ℝ) := by
      rw [hnu]
      have hνr : (1 / (εT : ℝ)) ≤ ν := (Nat.le_ceil _).trans (by exact_mod_cast hνε)
      have hL : (ν : ℝ) ≤ (Outer.instLength g.lenExp ν : ℝ) := by
        have : ν ≤ Outer.instLength g.lenExp ν := by
          unfold Outer.instLength
          calc ν = ν ^ 1 := (pow_one ν).symm
            _ ≤ ν ^ (g.lenExp + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        exact_mod_cast this
      have hLpos : (0 : ℝ) < (Outer.instLength g.lenExp ν : ℝ) := by
        exact_mod_cast Outer.instLength_pos (G := g.lenExp) ν (by omega)
      rw [div_lt_iff₀ hLpos]
      have h1 : 1 ≤ (εT : ℝ) * ν := by rw [div_le_iff₀ hεT0] at hνr; linarith
      calc (P.gamma : ℝ) < 1 := hγ1
        _ ≤ (εT : ℝ) * ν := h1
        _ ≤ (εT : ℝ) * (Outer.instLength g.lenExp ν : ℝ) := mul_le_mul_of_nonneg_left hL hεT0.le
    have hpair : PairOK s g z B := by
      refine ⟨by rw [hnu], by rw [hnu]; omega, by rw [hnu]; exact hfitν ν hνfit B.src hsrc, ?_⟩
      rw [hnu]
      exact (Outer.check_iff_checkAt ν z B.src).mp hcheck

    obtain ⟨hD1, C, hCt, hag⟩ := hardTable_transport P (substituted_pow s g ν z B) hD
      (clauseWidth g.clauseDegree (width s g (2 ^ ν))) g.positionLog C0
    have hCw : C.topWeight ≤ budget (width s g (2 ^ ν)) := hCt ▸ hCw0
    have hagree : 1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicGates.FiniteAverages.agreement C.eval
        (hardTable P (substituted s g z B) hD1 (clauseWidth g.clauseDegree (width s g (2 ^ ν))) g.positionLog) :=
      hag ▸ hagree0
    have hrb := hRoom (2 ^ ν) z B hpf hqR (by have := Nat.one_lt_two_pow (n := ν) (by omega); omega)
    obtain ⟨hguards, hsizeok, hU⟩ := approx_complete s P g z B hD1 C s.normalization hn ctr ω
      aC onsetC hcomp budget ε (εT : ℝ) hCw hagree hε hε1 hεγ (by linarith) hω0'.le hωε hP5 hP hq4 hqC hb4 hr1
      hω16 hr3 hA3c hA1c hsrc hpf hrb hν1 hprec hpair
    exact hfits (2 ^ ν) (hνF.trans (Nat.lt_two_pow_self).le) z _ hsizeok ⟨hguards, hU⟩

end NearCubicGates.Close.Closure
