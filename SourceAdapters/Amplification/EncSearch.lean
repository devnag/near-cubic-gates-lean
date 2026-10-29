import SourceAdapters.Amplification.EncMain
import SourceAdapters.Field.BinaryField

/-!
# The X3 modulus by exhaustive search, in the cell language (proof of `lem:small-bias`, join X3)

`GF.firstPrimitive t = 2^t + j₀` for the least `j₀ < 2^t` such that `2^t + j₀` passes the primitivity certificate
`GF.PrimitiveCert` (period of the LFSR orbit of `1` equal to `2^t − 1`). The machine tests the candidates in order:

* `certP`: `CF := [PrimitiveCert P t]`, by running the LFSR `2^t − 1` steps and recording an early return to `1`
  (`cert_iff`);
* `searchP`: `P := firstPrimitive t` (`firstPrimitive_least`: the least certified candidate exists, by the fixed X3
  join's `firstPrimitive` certificate).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

/-! ## The certificate as a recursion -/

theorem cert_iff (p t : ℕ) (ht : 1 ≤ t) (hp : GF.ModulusOk p t) :
    GF.PrimitiveCert p t ↔ GF2.lfsrPow p t (2 ^ t - 1) = 1 ∧
      ∀ i, 0 < i → i < 2 ^ t - 1 → GF2.lfsrPow p t i ≠ 1 := by
  have h2 : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  unfold GF.PrimitiveCert GF2.period
  constructor
  · rintro ⟨-, -, hper⟩
    cases hf : (List.range (2 ^ t)).find? (fun j => j ≠ 0 && GF2.lfsrPow p t j == 1) with
    | none => rw [hf] at hper; simp at hper; omega
    | some j =>
      rw [hf] at hper
      simp only [Option.getD_some] at hper
      subst hper
      rw [List.find?_range_eq_some] at hf
      obtain ⟨h1, -, h3⟩ := hf
      refine ⟨(by simpa using h1 : _ ∧ _).2, fun i hi hi2 he => ?_⟩
      have := h3 i hi2
      simp [he] at this; omega
  · rintro ⟨h1, h2'⟩
    refine ⟨ht, hp, ?_⟩
    have : (List.range (2 ^ t)).find? (fun j => j ≠ 0 && GF2.lfsrPow p t j == 1) = some (2 ^ t - 1) := by
      rw [List.find?_range_eq_some]
      refine ⟨by simp [h1]; omega, by simp, fun i hi => ?_⟩
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp [hi0, h2' i (by omega) hi]
    rw [this]; rfl

theorem firstPrimitive_least (t : ℕ) (ht : 1 ≤ t) :
    ∃ j0 < 2 ^ t, GF.firstPrimitive t = 2 ^ t + j0 ∧ GF.PrimitiveCert (2 ^ t + j0) t ∧
      ∀ j < j0, ¬ GF.PrimitiveCert (2 ^ t + j) t := by
  have hc := (Field.binaryFieldArithmetic.2.1 t ht).1
  unfold GF.firstPrimitive at hc ⊢
  cases hf : (List.range (2 ^ t)).find? (fun j => decide (GF.PrimitiveCert (2 ^ t + j) t)) with
  | none =>
    rw [hf] at hc
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using hc) (hf 0 (by simp))
  | some j0 =>
    rw [List.find?_range_eq_some] at hf
    obtain ⟨h1, h2, h3⟩ := hf
    refine ⟨j0, by simpa using h2, rfl, by simpa using h1, fun j hj => ?_⟩
    have := h3 j hj
    simpa using this

/-! ## The certificate test -/

abbrev vCA : Var := 72
abbrev vCI : Var := 73
abbrev vCR : Var := 74
abbrev vCL : Var := 75
abbrev vCF : Var := 76

def certS : List Var := [vCA, vCI, vCR, vCL, vCF, vFA] ++ lfsrS

def certBody : Sc :=
  .seq (.op (.copy vFA vCA)) <| .seq lfsrP <| .seq (.op (.copy vCA vFR)) <| .seq (.op (.inc vCI)) <|
  .ite (.eq vCA vONE) (.ite (.lt vCI vCL) (.op (.copy vCR vONE)) (.op (.zero vXQ))) (.op (.zero vXQ))

def certP : Sc :=
  .seq (.op (.copy vCA vONE)) <| .seq (.op (.zero vCI)) <| .seq (.op (.zero vCR)) <|
  .seq (.op (.copy vCL vPOWT)) <| .seq (.op (.sub vCL vONE)) <| .seq (.loop (.lt vCI vCL) certBody) <|
  .seq (.op (.zero vCF)) <| .ite (.eq vCA vONE) (.ite (.eq vCR vZ) (.op (.inc vCF)) (.op (.zero vXQ))) (.op (.zero vXQ))

def certCost (t : ℕ) : ℕ := (2 ^ t - 1) * (lfsrCost t + 10 + 2) + 30

/-- No early return to `1` among the first `j` steps. -/
def NoEarly (p t j : ℕ) : Prop := ∀ i, 0 < i → i ≤ j → i < 2 ^ t - 1 → GF2.lfsrPow p t i ≠ 1

/-- The state of `certP` before round `j`. -/
def CertInv (g : Prm) (a0 : Ds) (j : ℕ) (b : Ds) : Prop :=
  Fr certS [] a0 b ∧ b.env vCA = GF2.lfsrPow g.p g.t j ∧ b.env vCI = j ∧ b.env vCL = 2 ^ g.t - 1 ∧
    (b.env vCR = 0 ↔ NoEarly g.p g.t j)

theorem certP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a) :
    Runs C certP a (certCost g.t) certS [] (fun b => b.env vCF = if GF.PrimitiveCert g.p g.t then 1 else 0) := by
  have ht := hw.2.2.2.2.2
  have hone : 1 < 2 ^ g.t := Nat.one_lt_two_pow (by omega)
  have hTW : 2 ^ g.t < 2 ^ C.Wd := pow_lt_W hw (by have := hw.2.1; omega)
  refine Runs.op1 (run_copy C certS a vCA vONE (by decide) (by decide)) ?_ (by unfold certCost; omega)
  refine Runs.op1 (run_zero C certS _ vCI (by decide)) ?_ (by unfold certCost; omega)
  refine Runs.op1 (run_zero C certS _ vCR (by decide)) ?_ (by unfold certCost; omega)
  refine Runs.op1 (run_copy C certS _ vCL vPOWT (by decide) (by decide)) ?_ (by unfold certCost; omega)
  refine Runs.op1 (run_sub C certS _ vCL vONE (by decide) (by decide) (by norm_env; rw [hg.c.2.1, hg.powt]; omega))
    ?_ (by unfold certCost; omega)
  norm_env
  rw [hg.c.2.1, hg.powt]
  refine Runs.call (Runs.loopN0 (C := C) (c := .lt vCI vCL) (body := certBody) (S := certS)
    (by unfold Cnd.wf; decide) (2 ^ g.t - 1) (lfsrCost g.t + 10) (CertInv g a) ?step ?stop _ ?init) ?cont
    (by unfold certCost; omega)
  case init =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | exact Fr.refl certS a | refine Fr.set_right ?_ _ _ (by decide))
    all_goals norm_env
    · rfl
    · simp only [true_iff]; intro i hi hi0; omega
  case stop =>
    rintro b ⟨-, -, hI, hL, -⟩
    simp [Cnd.eval, hI, hL]
  case step =>
    rintro j hj b ⟨hf, hA, hI, hL, hR⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    refine ⟨by simp [Cnd.eval, hI, hL, hj], ?_⟩
    refine Runs.op1 (run_copy C certS b vFA vCA (by decide) (by decide)) ?_ (by unfold lfsrCost; omega)
    have hAlt : GF2.lfsrPow g.p g.t j < 2 ^ g.t := (GF.lfsrPow_spec g.p g.t hp ht j).1
    refine Runs.callS (lfsrP_spec C g hw hp _ (hgb.of_fr (Fr.set certS b vFA _ (by decide)) (by decide))
      _ (by norm_env; exact hA) hAlt) (by decide) ?_ (by unfold lfsrCost; omega)
    intro d hd hdv
    have hdI : d.env vCI = j := by rw [hd.env vCI (by decide)]; norm_env; exact hI
    have hdL : d.env vCL = 2 ^ g.t - 1 := by rw [hd.env vCL (by decide)]; norm_env; exact hL
    have hdR : d.env vCR = b.env vCR := by rw [hd.env vCR (by decide)]; norm_env
    have hgd : Glob g d := (hgb.of_fr (Fr.set certS b vFA _ (by decide)) (by decide)).of_fr hd (by decide)
    have hjW : j + 1 < 2 ^ C.Wd := by omega
    refine Runs.op1 (run_copy C certS _ vCA vFR (by decide) (by decide)) ?_ (by unfold lfsrCost; omega)
    refine Runs.op1 (run_inc C certS _ vCI (by decide) (by norm_env; rw [hdI]; exact hjW)) ?_
      (by unfold lfsrCost; omega)
    norm_env
    rw [hdv, hdI]
    have hpow : GF2.lfsr g.p g.t (GF2.lfsrPow g.p g.t j) = GF2.lfsrPow g.p g.t (j + 1) := rfl
    rw [hpow]
    have hfr : ∀ (x : Var) (v : ℕ), x ∈ certS → Fr certS [] a
        ((((d.set vCA (GF2.lfsrPow g.p g.t (j + 1))).set vCI (j + 1)).set x v)) := by
      intro x v hx
      have e1 := (hf.trans0 (Fr.set certS b vFA _ (by decide))).trans0 (hd.mono (by decide))
      exact ((e1.set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _ hx
    by_cases hret : GF2.lfsrPow g.p g.t (j + 1) = 1 ∧ j + 1 < 2 ^ g.t - 1
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hret.1, hgd.c.2.1]) ?_ (by omega)
      refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hdL, hret.2]) ?_ (by omega)
      refine Runs.last (run_copy C certS _ vCR vONE (by decide) (by decide)) ?_ (by omega)
      intro _
      refine ⟨hfr _ _ (by decide), ?_, ?_, ?_, ?_⟩ <;> norm_env
      · exact hdL
      · rw [hgd.c.2.1]
        simp only [one_ne_zero, false_iff]
        intro hne
        exact hne (j + 1) (by omega) le_rfl hret.2 hret.1
    · have hR' : (b.env vCR = 0 ↔ NoEarly g.p g.t (j + 1)) := by
        rw [hR]
        constructor
        · intro h i hi0 hij hit
          rcases Nat.lt_or_ge i (j + 1) with hlt | hge
          · exact h i hi0 (by omega) hit
          · have : i = j + 1 := by omega
            subst this
            intro he; exact hret ⟨he, hit⟩
        · intro h i hi0 hij hit; exact h i hi0 (by omega) hit
      by_cases h1 : GF2.lfsrPow g.p g.t (j + 1) = 1
      · have h2 : ¬ j + 1 < 2 ^ g.t - 1 := fun h2 => hret ⟨h1, h2⟩
        refine Runs.iteT' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, h1, hgd.c.2.1]) ?_ (by omega)
        refine Runs.iteF' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hdL, h2]) ?_ (by omega)
        refine Runs.last (run_zero C certS _ vXQ (by decide)) ?_ (by omega)
        intro _
        refine ⟨hfr _ _ (by decide), ?_, ?_, ?_, ?_⟩ <;> norm_env
        · exact hdL
        · rw [hdR]; exact hR'
      · refine Runs.iteF' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, h1, hgd.c.2.1]) ?_ (by omega)
        refine Runs.last (run_zero C certS _ vXQ (by decide)) ?_ (by omega)
        intro _
        refine ⟨hfr _ _ (by decide), ?_, ?_, ?_, ?_⟩ <;> norm_env
        · exact hdL
        · rw [hdR]; exact hR'
  case cont =>
    rintro b hfb ⟨hf, hA, -, -, hR⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    refine Runs.op1 (run_zero C certS b vCF (by decide)) ?_ (by unfold certCost; omega)
    have hcert := cert_iff g.p g.t ht hp
    have hNE : NoEarly g.p g.t (2 ^ g.t - 1) ↔ ∀ i, 0 < i → i < 2 ^ g.t - 1 → GF2.lfsrPow g.p g.t i ≠ 1 :=
      ⟨fun h i h0 h1 => h i h0 (by omega) h1, fun h i h0 _ h1 => h i h0 h1⟩
    by_cases hA1 : GF2.lfsrPow g.p g.t (2 ^ g.t - 1) = 1
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hA, hA1, hgb.c.2.1]) ?_ (by unfold certCost; omega)
      by_cases hR0 : b.env vCR = 0
      · refine Runs.iteT' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hR0, hgb.c.1]) ?_ (by unfold certCost; omega)
        refine Runs.last (run_inc C certS _ vCF (by decide) (by norm_env; omega)) ?_ (by unfold certCost; omega)
        intro _
        norm_env
        rw [if_pos (hcert.mpr ⟨hA1, hNE.mp (hR.mp hR0)⟩)]
      · refine Runs.iteF' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hR0, hgb.c.1]) ?_ (by unfold certCost; omega)
        refine Runs.last (run_zero C certS _ vXQ (by decide)) ?_ (by unfold certCost; omega)
        intro _
        norm_env
        rw [if_neg (fun h => hR0 (hR.mpr (hNE.mpr (hcert.mp h).2)))]
    · refine Runs.iteF' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hA, hA1, hgb.c.2.1]) ?_ (by unfold certCost; omega)
      refine Runs.last (run_zero C certS _ vXQ (by decide)) ?_ (by unfold certCost; omega)
      intro _
      norm_env
      rw [if_neg (fun h => hA1 (hcert.mp h).1)]

/-! ## The search -/

/-- The parameters with another modulus. -/
def Prm.withP (g : Prm) (p : ℕ) : Prm := { g with p := p }

@[simp] theorem Prm.withP_t (g : Prm) (p : ℕ) : (g.withP p).t = g.t := rfl

@[simp] theorem Prm.withP_p (g : Prm) (p : ℕ) : (g.withP p).p = p := rfl

theorem Glob.of_fr_p {g : Prm} {S : List Var} {w : List Bool} {a b : Ds} (h : Glob g a) (hf : Fr S w a b)
    (hS : ∀ x ∈ globs.erase vP, x ∉ S) (p' : ℕ) (hp : b.env vP = p') : Glob (g.withP p') b := by
  have e : ∀ x ∈ globs.erase vP, b.env x = a.env x := fun x hx => hf.env x (hS x hx)
  obtain ⟨⟨h0, h1, h2⟩, ht, htb, hpt, hh, hph, hn, hpn, hm, hL, hpl, -, he⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp, ?_⟩ <;>
    (rw [e _ (by decide)]; assumption)

theorem modulusOk_cand (t j : ℕ) (hj : j < 2 ^ t) : GF.ModulusOk (2 ^ t + j) t :=
  ⟨Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (by rw [pow_succ]; omega), by rw [pow_succ]; omega⟩

abbrev vSJ : Var := 78

def searchS : List Var := [vSJ, vP] ++ certS

def searchBody : Sc :=
  .seq (.op (.inc vSJ)) <| .seq (.op (.copy vP vPOWT)) <| .seq (.op (.add vP vSJ)) certP

def searchP : Sc :=
  .seq (.op (.zero vSJ)) <| .seq (.op (.copy vP vPOWT)) <| .seq certP (.loop (.lt vCF vONE) searchBody)

def searchCost (t : ℕ) : ℕ := 2 ^ t * (certCost t + 10 + 2) + certCost t + 10

/-- The state of the search before testing candidate `j + 1`. -/
def SearchInv (g : Prm) (a0 : Ds) (j : ℕ) (b : Ds) : Prop :=
  Fr searchS [] a0 b ∧ b.env vSJ = j ∧ Glob (g.withP (2 ^ g.t + j)) b ∧
    b.env vCF = (if GF.PrimitiveCert (2 ^ g.t + j) g.t then 1 else 0) ∧
    ∀ j' < j, ¬ GF.PrimitiveCert (2 ^ g.t + j') g.t

theorem searchP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (a : Ds) (hg : Glob g a) :
    Runs C searchP a (searchCost g.t) searchS []
      (fun b => b.env vP = GF.firstPrimitive g.t ∧ Glob (g.withP (GF.firstPrimitive g.t)) b) := by
  have ht := hw.2.2.2.2.2
  obtain ⟨j0, hj0, hfp, hc0, hmin⟩ := firstPrimitive_least g.t ht
  have hTW : 2 ^ g.t + 2 ^ g.t < 2 ^ C.Wd := by
    have := pow_lt_W hw (x := g.t + 1) (by have := hw.2.1; omega); rw [pow_succ] at this; omega
  have hw' : ∀ p', WOk (g.withP p') C := fun _ => hw
  refine Runs.op1 (run_zero C searchS a vSJ (by decide)) ?_ (by (try simp only [Prm.withP_t] at *); unfold searchCost; omega)
  refine Runs.op1 (run_copy C searchS _ vP vPOWT (by decide) (by decide)) ?_ (by (try simp only [Prm.withP_t] at *); unfold searchCost; omega)
  have hg0 : Glob (g.withP (2 ^ g.t + 0)) ((a.set vSJ 0).set vP ((a.set vSJ 0).env vPOWT)) :=
    hg.of_fr_p (((Fr.refl searchS a).set_right _ _ (by decide)).set_right _ _ (by decide)) (by decide) _
      (by norm_env; rw [hg.powt]; rfl)
  refine Runs.callS (certP_spec C _ (hw' _) (modulusOk_cand g.t 0 (by omega)) _ hg0) (by decide) ?_
    (by (try simp only [Prm.withP_t] at *); unfold searchCost; omega)
  intro b hb hbv
  have hinit : SearchInv g a 0 b := by
    refine ⟨?_, ?_, hg0.of_fr hb (by decide), by rw [hbv]; exact if_congr Iff.rfl rfl rfl,
      fun j' hj' => absurd hj' (by omega)⟩
    · exact (((Fr.refl searchS a).set_right _ _ (by decide)).set_right _ _ (by decide)).trans0 (hb.mono (by decide))
    · rw [hb.env vSJ (by decide)]; norm_env
  refine (Runs.loopN0 (C := C) (c := .lt vCF vONE) (body := searchBody) (S := searchS) (by unfold Cnd.wf; decide)
    j0 (certCost g.t + 10) (SearchInv g a) ?step ?stop b hinit).mono ?cost ?sub ?post
  case cost =>
    have := Nat.mul_le_mul_right (certCost g.t + 10 + 2) hj0.le
    (try simp only [Prm.withP_t] at *); unfold searchCost; omega
  case sub => exact List.Subset.refl _
  case post =>
    rintro d - ⟨-, hJ, hgd, -, -⟩
    refine ⟨?_, by rw [hfp]; exact hgd⟩
    rw [hgd.p]; exact hfp.symm
  case stop =>
    rintro d ⟨-, -, hgd, hF, -⟩
    simp [Cnd.eval, hF, hc0, hgd.c.2.1]
  case step =>
    rintro j hj d ⟨hf, hJ, hgd, hF, hlt⟩
    have hnc : ¬ GF.PrimitiveCert (2 ^ g.t + j) g.t := hmin j hj
    refine ⟨by simp [Cnd.eval, hF, hnc, hgd.c.2.1], ?_⟩
    have hjW : j + 1 < 2 ^ C.Wd := by omega
    refine Runs.op1 (run_inc C searchS d vSJ (by decide) (by rw [hJ]; exact hjW)) ?_ (by (try simp only [Prm.withP_t] at *); unfold certCost; omega)
    refine Runs.op1 (run_copy C searchS _ vP vPOWT (by decide) (by decide)) ?_ (by (try simp only [Prm.withP_t] at *); unfold certCost; omega)
    refine Runs.op1 (run_add C searchS _ vP vSJ (by decide) (by decide)
      (by norm_env; rw [hgd.powt, hJ]; simp only [Prm.withP_t]; omega)) ?_ (by (try simp only [Prm.withP_t] at *); unfold certCost; omega)
    norm_env
    rw [hgd.powt, hJ]
    simp only [Prm.withP_t]
    have hg1 : Glob (g.withP (2 ^ g.t + (j + 1))) (((d.set vSJ (j + 1)).set vP (2 ^ g.t)).set vP (2 ^ g.t + (j + 1))) :=
      hgd.of_fr_p ((((Fr.refl searchS d).set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _
        (by decide)) (by decide) _ (by norm_env)
    refine Runs.lastS (certP_spec C _ (hw' _) (modulusOk_cand g.t (j + 1) (by omega)) _ hg1) (by decide) ?_
      (by (try simp only [Prm.withP_t] at *); unfold certCost; omega)
    intro e he hev
    refine ⟨?_, ?_, hg1.of_fr he (by decide), by rw [hev]; exact if_congr Iff.rfl rfl rfl, fun j' hj' => ?_⟩
    · exact (hf.trans0 ((((Fr.refl searchS d).set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _
        (by decide))).trans0 (he.mono (by decide))
    · rw [he.env vSJ (by decide)]; norm_env
    · rcases Nat.lt_or_ge j' j with h | h
      · exact hlt j' h
      · have : j' = j := by omega
        subst this; exact hnc

end NearCubicGates.Adapters.Amplification.Enc
