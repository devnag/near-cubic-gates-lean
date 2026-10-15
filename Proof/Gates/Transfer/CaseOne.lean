import Proof.Gates.Transfer.Budget
import Proof.Gates.Transfer.CaseTwo
import Proof.Gates.Transfer.Symmetric
import Proof.CaseAnalysis.CaseOneHardness
import Proof.CaseAnalysis.CaseOneBounds

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.CloseoutCaseOne NearCubicGates.Close.Gadget NearCubicGates.Target
open NearCubicWires.OuterPCPRecovery NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.PhysicalRecovery

/-- The two agreement notions coincide on the cube. -/
theorem finiteAgreement_eq {n : ℕ} (f g : BitInput n → Bool) :
    NearCubicGates.FiniteAverages.agreement f g = NearCubicWires.agreement f g := by
  classical
  unfold NearCubicGates.FiniteAverages.agreement NearCubicGates.FiniteAverages.mean NearCubicWires.agreement
  rw [Finset.sum_boole]

noncomputable def ampCore {c d : ℕ} (amplifier : ScheduleAmplifier c d) (q : ℕ) (f : BoolFunction q) (hq : 1 ≤ q)
    (hard : WorstCaseHardAt f (oracleSizeBound d q)) : HardCore booleanCircuitFamily where
  arity := (amplifier.output q f).arity
  function := (amplifier.output q f).function
  size := integerFloorRoot c (oracleSizeBound d q)
  advantage := Real.rpow (oracleSizeBound d q : ℝ) (-(1 : ℝ) / c)
  hard := by
    intro candidate hcandidate
    obtain ⟨circuit, hsize, rfl⟩ := hcandidate
    exact amplifier.sound _ f hq hard circuit hsize

/-- The Case 1 branch of `gateCore` is the padded amplified function. -/
theorem amplified_eq {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (q : ℕ) (f : BoolFunction q)
    (target : ℕ) (hfit : (amplifier.output q f).arity ≤ target) :
    GateParams.amplified amplifier q f target = padCore (amplifier.output q f).function hfit := by
  unfold GateParams.amplified
  simp only []
  rw [dif_pos hfit]

theorem truncInput_padQuery {q ℓ : ℕ} (h : ℓ ≤ q) (a : BitInput ℓ) :
    Outer.truncInput (q := q) (Outer.padQuery a) = a := by
  funext i
  simp [Outer.truncInput, Outer.padQuery, show i.val < q by omega]

/-- Case 1 (i): with no CHECK-passing source circuit of `q^G` gates, `X_z` is worst-case hard. -/
theorem srcFn_hard (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν))
    (hno : ¬ g.SrcExists s ν z) : WorstCaseHardAt (g.srcFn s ν z) (g.bound s ν) := by
  intro B hB
  by_contra hall
  push Not at hall
  apply hno
  refine ⟨B, hB, fun r => ?_⟩
  apply (ENP.unitOuter_check ν _ _ z z B r).mpr
  funext i
  unfold Outer.ttN
  rw [hall]
  unfold GateParams.srcFn
  congr 1
  have hlt : i.val < 2 ^ ν := i.isLt
  have : (fun j : Fin ν => Outer.pointOf ν (g.width s ν) i.val (Fin.castLE (g.nu_lt_width s ν).le j)) =
      fun j : Fin ν => i.val.testBit j.val := by
    funext j
    simp [Outer.pointOf, j.isLt]
  rw [this, binaryAddress_testBit hlt]

/-- Case 1 (iii): if no `q^G`-gate circuit answers as the table `t`, then `O_t` on `q` bits is worst-case hard. -/
theorem pfFn_hard (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν)) {ℓ : ℕ}
    (hℓ : ℓ ≤ g.width s ν) (t : BitInput (2 ^ ℓ))
    (hno : ¬ RecoveryChoice.SmallOracle (g.matchPCP s ν hℓ t) g.degree z) :
    WorstCaseHardAt (GateParams.pfFn (q := g.width s ν) t) (g.bound s ν) := by
  intro B hB
  by_contra hall
  push Not at hall
  apply hno
  refine ⟨B, hB, fun r => ?_⟩
  apply (ENP.unitOuter_match ℓ _ hℓ (tableOracle t) z B r).mpr
  intro a
  rw [hall]
  unfold GateParams.pfFn
  rw [truncInput_padQuery hℓ]

/-- The simulation size inequality: `40 (m + b(q)(m+1) + 2)⁴ ≤ q¹⁷` when `m ≤ C q`, `b(q) ≤ q³`,
`q ≥ 40 (2C+3)⁴`. -/
theorem simulation_room (C q m b : ℕ) (hq1 : 1 ≤ q) (hm : m ≤ C * q) (hb : b ≤ q ^ 3)
    (hQ : 40 * (2 * C + 3) ^ 4 ≤ q) : 40 * (m + b * (m + 1) + 2) ^ 4 ≤ q ^ 17 := by
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq1
  have h3 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
  have h1 : q ≤ q ^ 4 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
  have hsum : m + b * (m + 1) + 2 ≤ (2 * C + 3) * q ^ 4 := by
    have hbm : b * (m + 1) ≤ q ^ 3 * (C * q + 1) := Nat.mul_le_mul hb (by omega)
    have : q ^ 3 * (C * q + 1) = C * q ^ 4 + q ^ 3 := by ring
    have hCq : C * q ≤ C * q ^ 4 := Nat.mul_le_mul_left _ h1
    nlinarith
  calc 40 * (m + b * (m + 1) + 2) ^ 4 ≤ 40 * ((2 * C + 3) * q ^ 4) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 4)
    _ = (40 * (2 * C + 3) ^ 4) * q ^ 16 := by ring
    _ ≤ q * q ^ 16 := Nat.mul_le_mul_right _ hQ
    _ = q ^ 17 := by ring

theorem caseOnePart {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ} (c : GateClosure s P ε) (hε : 0 < ε) :
    CaseOnePart c := by
  classical
  intro hsel
  set H := s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock with hH
  set cst := s.amplification.stvExponent with hcst
  have hc : 0 < cst := s.amplification.stvExponentPositive
  have hd : 17 * cst ≤ c.g.degree := c.ready.degreeLarge
  set amp := selectedAmplifier s.amplification c.g.degree with hamp
  obtain ⟨refOnset, refReady⟩ := refuterYes H.joint c.M c.littleO c.oneSided
  set gap : ℝ := 1 / 2 - (P.gamma : ℝ) / 5 + ε with hgapdef
  have hγ1 : (P.gamma : ℝ) < 1 := by exact_mod_cast P.gamma_lt_one
  have hgap : 0 < gap := by rw [hgapdef]; linarith
  obtain ⟨advOnset, -, advReady⟩ := advantage_onset cst c.g.degree hc (by omega) gap hgap
  obtain ⟨q1, hq1⟩ := c.ready.budgetUpper
  obtain ⟨fitOnset, hfitν⟩ := c.ready.lenFit
  set svOnset := (c.g.sv s).onset with hsvOnset
  set Cc := c.g.ampFactor * (1 + 2 * c.g.clauseDegree + c.g.positionLog) with hCc
  obtain ⟨o, hfacts⟩ := hsel.2
  obtain ⟨n0, hn0⟩ := hsel.1 (max (max refOnset advOnset)
    (max q1 (max (40 * (2 * Cc + 3) ^ 4) (max fitOnset svOnset))))
  refine ⟨max o n0, fun n hn hnot C hC => ?_⟩
  obtain ⟨hν1, hνsrc, hlen⟩ := hfacts n (le_trans (le_max_left _ _) hn)
  have hνbig := hn0 n (le_trans (le_max_right _ _) hn)
  set ν := c.g.selected s n with hν
  set q := c.g.width s ν with hqdef
  have hqν : ν + 1 ≤ q := c.g.width_lower s ν
  have hq1' : 1 ≤ q := by omega
  have hrefν : refOnset ≤ 2 ^ ν := by
    have : refOnset ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hνbig
    exact le_trans this (Nat.lt_two_pow_self).le
  have hadvq : advOnset ≤ q := by
    have : advOnset ≤ ν := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hνbig
    omega
  have hq1q : q1 ≤ q := by
    have : q1 ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hνbig
    omega
  have hQq : 40 * (2 * Cc + 3) ^ 4 ≤ q := by
    have : 40 * (2 * Cc + 3) ^ 4 ≤ ν :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hνbig
    omega
  have hfitOn : fitOnset ≤ ν :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _)))) hνbig
  have hsvOn : svOnset ≤ ν :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _)))) hνbig
  set z := c.input n with hz
  have hyes : H.hierarchy.verifier.language H.hierarchy.time (2 ^ ν) z :=
    (hierarchy_language_exact H.hierarchy (2 ^ ν) z).mp (refReady (2 ^ ν) hrefν).2

  have finish : ∀ f : BoolFunction q, WorstCaseHardAt f (oracleSizeBound c.g.degree q) →
      c.nativeFn n = GateParams.amplified amp q f (c.g.nativeLength s n) →
      NearCubicGates.FiniteAverages.agreement C.eval (c.nativeFn n) < 1 - (P.gamma : ℝ) / 5 + ε := by
    intro f hardf hnat
    let hard := ampCore amp.toScheduleAmplifier q f hq1' hardf
    have hpl := c.ready.positionPos
    have hfit : (amp.output q f).arity ≤ c.g.nativeLength s n := by
      have he := NearCubicWires.RepairSource.CloseoutParameters.arity_envelope amp c.g.ampFactor q
        (clauseWidth c.g.clauseDegree q + c.g.positionLog - 1) c.ready.ampLarge hq1' f
      rw [hlen]
      unfold GateParams.coreArity GateParams.tableArity
      have heq : c.g.ampFactor * (q + (clauseWidth c.g.clauseDegree q + c.g.positionLog - 1) + 1) =
          c.g.ampFactor * (q + clauseWidth c.g.clauseDegree q + c.g.positionLog) := by
        congr 1; omega
      exact he.trans (le_of_eq heq)
    have hhard : hard.arity ≤ c.g.nativeLength s n := hfit
    have hnative : c.nativeFn n = (padAmplifierCore hard (c.g.nativeLength s n) hhard).function := by
      rw [hnat, amplified_eq amp q f _ hfit]
      rfl
    have hbud : c.budget q ≤ q ^ 3 := hq1 q hq1q
    have hm : (c.g.nativeLength s n) ≤ Cc * q := by rw [hlen]; exact coreArity_le_linear s c.g ν
    set symCap := c.budget q * ((c.g.nativeLength s n) + 1) with hsymCap
    have hroom : 40 * ((c.g.nativeLength s n) + symCap + 2) ^ 4 ≤ q ^ 17 :=
      simulation_room Cc q (c.g.nativeLength s n) (c.budget q) hq1' hm hbud hQq
    have hsize : 40 * ((padAmplifierCore hard (c.g.nativeLength s n) hhard).arity + symCap + 2) ^ 4 ≤
        (padAmplifierCore hard (c.g.nativeLength s n) hhard).size := by
      change 40 * ((c.g.nativeLength s n) + symCap + 2) ^ 4 ≤ integerFloorRoot cst (oracleSizeBound c.g.degree q)
      exact hroom.trans (amplifier_size_ge_power cst c.g.degree 17 q hc (by omega) hd)
    have hs := symmetricAverageHard_of_boolean s.normalization (padAmplifierCore hard (c.g.nativeLength s n) hhard)
      symCap hsize
    have hwire : (toSymmetric C).wireCount ≤ symCap := by
      refine (toSymmetric_wireCount C).trans ?_
      exact Nat.mul_le_mul_right _ hC
    have hagree := hs (toSymmetric C).eval ⟨toSymmetric C, hwire, rfl⟩
    have hadv : (padAmplifierCore hard (c.g.nativeLength s n) hhard).advantage < gap := by
      change Real.rpow (oracleSizeBound c.g.degree q : ℝ) (-(1 : ℝ) / cst) < gap
      exact advReady q hadvq
    rw [finiteAgreement_eq, hnative]
    have hev : (toSymmetric C).eval = C.eval := funext (toSymmetric_eval C)
    rw [hev] at hagree
    rw [hgapdef] at hadv
    have hagree' : NearCubicWires.agreement (n := c.g.nativeLength s n) C.eval
        (padAmplifierCore hard (c.g.nativeLength s n) hhard).function ≤
        1 / 2 + (padAmplifierCore hard (c.g.nativeLength s n) hhard).advantage := hagree
    linarith
  -- the gate core at the selected source index
  have hnat0 : c.nativeFn n = c.g.gateCore s P amp ν z (clauseWidth c.g.clauseDegree q) c.g.positionLog
      (c.g.nativeLength s n) := by
    simp only [GateClosure.nativeFn, GateParams.native]
    rw [if_pos ⟨hν1, hνsrc⟩]
    rfl
  by_cases h1 : c.g.SrcExists s ν z
  · -- Case 1 (iii): the first honest oracle `O*` has no `q^G`-gate circuit
    set b := c.g.firstSrc s ν z h1 with hb
    have hbsize : b.size ≤ c.g.bound s ν :=
      (RecoveryChoice.oracleSelector (c.g.checkPCP s ν z) c.g.degree z h1).sizeBounded
    have hcheck : Outer.Check ν z b :=
      (ENP.unitOuter_check ν _ _ z z _ (fun _ => false)).mp
        ((RecoveryChoice.oracleSelector (c.g.checkPCP s ν z) c.g.degree z h1).accepts (fun _ => false))
    have hfits : Outer.SrcFits c.g.lenExp ν b := hfitν ν hfitOn b hbsize
    obtain ⟨O, hO⟩ := Outer.honest s.mw (c.g.sv s) ν z b hsvOn hν1 (c.g.nu_lt_width s ν).le hfits hcheck hyes
    have h2 : ∃ t, HonestTable (c.g.outC s ν b).circuit t := honestTable_of_oracle _ O hO
    have hℓ : (c.g.outC s ν b).ell ≤ c.g.width s ν := Outer.ell_le_width s.mw (c.g.sv s) ν b hsvOn hν1
    set T := Classical.choice (existsFirstTable _ h2) with hT
    have h3 : ¬ RecoveryChoice.SmallOracle (c.g.matchPCP s ν hℓ T.table) c.g.degree z :=
      fun h3 => hnot ⟨h1, h2, hℓ, h3⟩
    apply finish (GateParams.pfFn T.table) (pfFn_hard s c.g ν z hℓ T.table h3)
    rw [hnat0]
    unfold GateParams.gateCore
    rw [dif_pos h1, dif_pos h2]
    simp only []
    rw [dif_neg (show ¬ GateParams.IsCaseTwo s c.g ν z from hnot)]
  · -- Case 1 (i): no CHECK-passing source circuit; the source input itself is hard
    apply finish (c.g.srcFn s ν z) (srcFn_hard s c.g ν z h1)
    rw [hnat0]
    unfold GateParams.gateCore
    rw [dif_neg h1]

end NearCubicGates.Close.Transfer
