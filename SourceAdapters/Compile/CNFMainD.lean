import SourceAdapters.Compile.CNFMainC

/-!
# The printer, part D: the whole program and its cost polynomial

proof of `lem:multitape-refuter` (the framed query is written) and proof of `cor:framed-refuter` (within a polynomial whose degree is fixed before
the machine): `mainP` = parse ; dimensions ; generate ; scan ; tautologies ; interpret ; output unit ;
balanced code ; framed bits. `mainCost r` sums the phase budgets; `mainCost_le` bounds it by `10^20·measure^36`.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.RepairSource.VerifierEncoding
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- **The printing program.** -/
def mainP : St VV MM :=
  .seq parseP (.seq dimsP (.seq genP (.seq scanP (.seq tautP (.seq runsP (.seq finP (.seq balP
    (emitBitsF bY))))))))

/-! ## Untouched state across phases -/

/-- `b` agrees with `a` on everything the program `s` never names. -/
def Kp (s : St VV MM) (a b : DS VV MM) : Prop :=
  (∀ x, sAny (opWr x) s = false → b.env x = a.env x) ∧
    (∀ m, sAny (opMs m) s = false → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ (sAny opEm s = false → b.out = a.out)

theorem Kp.trans {s u : St VV MM} {a b d : DS VV MM} (h1 : Kp s a b) (h2 : Kp u b d) : Kp (.seq s u) a d := by
  refine ⟨fun x hx => ?_, fun m hm => ?_, fun h => ?_⟩ <;> simp only [sAny, Bool.or_eq_false_iff] at *
  · rw [h2.1 x hx.2, h1.1 x hx.1]
  · exact ⟨(h2.2.1 m hm.2).1.trans (h1.2.1 m hm.1).1, (h2.2.1 m hm.2).2.trans (h1.2.1 m hm.1).2⟩
  · rw [h2.2.2 h.2, h1.2.2 h.1]

theorem Hs.kp {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop} (h : Hs C s a t R) :
    Hs C s a t (fun b => R b ∧ Kp s a b) := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  obtain ⟨k1, k2, _, k4⟩ := ex_keep he
  exact ⟨b, n, he, hn, hb, k1, k2, k4⟩

/-! ## Payloads -/

theorem tcode_le (t : RTok) : tcode t ≤ 8 * tpay t + 7 := by
  cases t with
  | cst b => cases b <;> simp [tcode, tpay]
  | inp j => simp [tcode, tpay]
  | wir k => simp [tcode, tpay]
  | _ => simp [tcode, tpay]

theorem genT_pay (r : CNFCompilationRequest) : ∀ t ∈ genT (reqGD r),
    tpay t ≤ windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1) + r.witnessLength + 1 := by
  intro t ht
  have hR : (reqGD r).td.Rep r.verifier.machine r.verifier.accepting := by
    rw [reqGD_td]; exact ofBits_rep r.verifier
  change t ∈ tmplT (reqGD r).td r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1) at ht
  rw [tmplT_eq _ _ _ hR, roundToks, List.mem_append] at ht
  rcases ht with h | h
  · have := vecW_pay _ _ t h; omega
  · simp at h; subst h; simp [tpay]

/-- The stream the interpreter runs is the request's token stream. -/
theorem requestToks_run (r : CNFCompilationRequest) :
    requestToks r = runToks (genI (reqGD r) r.input) (genT (reqGD r)) (genA (reqGD r) r.high) r.fuel := by
  have hR : (reqGD r).td.Rep r.verifier.machine r.verifier.accepting := by
    rw [reqGD_td]; exact ofBits_rep r.verifier
  rw [requestToks_eq r _ hR, runToks, genI, genT, genA]
  simp [reqGD, List.append_assoc]

/-! ## The cost polynomial -/

def lam (r : CNFCompilationRequest) : ℕ := 4 * r.measure ^ 2
def Ib (r : CNFCompilationRequest) : ℕ := initCost (lam r)
def Tb (r : CNFCompilationRequest) : ℕ := tmplCost (reqGD r) (lam r)
def Ab (r : CNFCompilationRequest) : ℕ := accCost (lam r) + rankCost r.witnessLength + 1
def Nb (r : CNFCompilationRequest) : ℕ := Ib r + r.fuel * Tb r + Ab r
def k0 (r : CNFCompilationRequest) : ℕ := (reqGD r).W + r.witnessLength + 1

def costScan (r : CNFCompilationRequest) : ℕ := 6 * (Ib r + Tb r + Ab r) + 60
def costRuns (r : CNFCompilationRequest) : ℕ :=
  (r.fuel + 1) * (7 * (Ib r + Tb r + Ab r + 3) + 30) + Nb r * (stepCost (k0 r + Nb r) + 8)
def costFin (r : CNFCompilationRequest) : ℕ := 7 * (k0 r + Nb r) + 85
def costBal (r : CNFCompilationRequest) : ℕ := balCost (requestFormula r).length 0
def costEmit (r : CNFCompilationRequest) : ℕ :=
  10 * Nat.size (RecoveryOracle.sourceSATCode (requestFormula r)) + 6

def mainCost (r : CNFCompilationRequest) : ℕ :=
  parseCost r + dimsCost r + genCost (reqGD r) (lam r) + costScan r + (r.witnessLength * (70 + 4) + 4) +
    costRuns r + costFin r + costBal r + costEmit r + 8

theorem runsCost_le (r : CNFCompilationRequest) (I T A : List RTok) (hI : I.length ≤ Ib r)
    (hT : T.length ≤ Tb r) (hA : A.length ≤ Ab r) : runsCost I T A r.fuel (k0 r) ≤ costRuns r := by
  have hN : (runToks I T A r.fuel).length ≤ Nb r := by
    simp only [runToks, List.length_append, len_rep, Nb]
    have := Nat.mul_le_mul_left r.fuel hT
    omega
  unfold runsCost costRuns stepCost
  gcongr

/-- Sizes in the measure. -/
theorem sizes (r : CNFCompilationRequest) :
    Ib r ≤ 1000 * r.measure ^ 4 ∧ Tb r ≤ 5000000 * r.measure ^ 12 ∧ Ab r ≤ 2000 * r.measure ^ 4 ∧
      k0 r ≤ 6 * r.measure ^ 2 ∧ Nb r ≤ 6000000 * r.measure ^ 13 := by
  set m := r.measure with hm
  have hm1 : 1 ≤ m := request_measure_positive r
  have pw : ∀ a b, a ≤ b → m ^ a ≤ m ^ b := fun a b h => Nat.pow_le_pow_right hm1 h
  have hok := reqGD_ok r
  have hn : r.witnessLength ≤ m := by rw [hm]; unfold CNFCompilationRequest.measure; omega
  have hf : r.fuel ≤ m := by rw [hm]; unfold CNFCompilationRequest.measure; omega
  have hL : lam r = 4 * m ^ 2 := rfl
  have e4 : (m ^ 2) ^ 2 = m ^ 4 := by ring
  have e12 : (m ^ 2) ^ 6 = m ^ 12 := by ring
  have hI : Ib r ≤ 1000 * m ^ 4 := by
    unfold Ib initCost; rw [hL]
    have := pw 2 4 (by norm_num); have := pw 0 2 (by norm_num); simp at *; nlinarith
  have hT : Tb r ≤ 5000000 * m ^ 12 := by
    unfold Tb lam
    calc tmplCost (reqGD r) (4 * m ^ 2) ≤ 1000 * (4 * m ^ 2) ^ 6 := tmplCost_le _ _ hok
      _ = 4096000 * m ^ 12 := by ring
      _ ≤ 5000000 * m ^ 12 := by omega
  have hA : Ab r ≤ 2000 * m ^ 4 := by
    unfold Ab accCost rankCost; rw [hL]
    have := pw 2 4 (by norm_num); have := pw 1 4 (by norm_num); have := pw 0 4 (by norm_num); simp at *
    nlinarith
  have hk : k0 r ≤ 6 * m ^ 2 := by
    unfold k0; have hW : (reqGD r).W ≤ 4 * m ^ 2 := hok.WΛ
    have := pw 1 2 (by norm_num); have := pw 0 2 (by norm_num); simp only [pow_one, pow_zero] at *; omega
  refine ⟨hI, hT, hA, hk, ?_⟩
  unfold Nb
  have h1 : r.fuel * Tb r ≤ m * (5000000 * m ^ 12) := Nat.mul_le_mul hf hT
  have h2 : m * (5000000 * m ^ 12) = 5000000 * m ^ 13 := by ring
  have := pw 4 13 (by norm_num)
  omega

theorem mainCost_le (r : CNFCompilationRequest) : mainCost r ≤ 10 ^ 20 * r.measure ^ 36 := by
  obtain ⟨hI, hT, hA, hk, hN⟩ := sizes r
  have hw := requestWord_length r
  have hl := requestFormula_length r
  have hb := requestFormula_bits r
  have hm1 : 1 ≤ r.measure := request_measure_positive r
  set m := r.measure with hm
  have pw : ∀ a b, a ≤ b → m ^ a ≤ m ^ b := fun a b h => Nat.pow_le_pow_right hm1 h
  have hcode : (code r.verifier).length + r.input.length + r.witnessLength + r.fuel + 1 ≤ m := by
    rw [hm]; unfold CNFCompilationRequest.measure; omega
  have p1 := pw 0 1 (by norm_num); have p4 := pw 1 4 (by norm_num); have p12 := pw 4 12 (by norm_num)
  have p13 := pw 12 13 (by norm_num); have p26 := pw 13 26 (by norm_num); have p36 := pw 26 36 (by norm_num)
  have p2 := pw 1 2 (by norm_num); have p2' := pw 2 13 (by norm_num)
  simp only [pow_zero, pow_one] at p1 p4 p2
  -- phases
  have cP : parseCost r ≤ 400 * m := by unfold parseCost; omega
  have cD : dimsCost r ≤ 400 * m := by unfold dimsCost; omega
  have cG : genCost (reqGD r) (lam r) ≤ 6000000 * m ^ 12 := by
    have e : genCost (reqGD r) (lam r) = Ib r + Tb r + Ab r + 30 := by
      unfold genCost Ib Tb Ab; simp only [reqGD]; omega
    omega
  have cS : costScan r ≤ 40000000 * m ^ 12 := by unfold costScan; omega
  have cR : costRuns r ≤ 2 * 10 ^ 15 * m ^ 26 := by
    unfold costRuns stepCost
    have hst : 30 * (k0 r + Nb r) + 300 + 8 ≤ 200000000 * m ^ 13 := by omega
    have hp : Nb r * (30 * (k0 r + Nb r) + 300 + 8) ≤ (6000000 * m ^ 13) * (200000000 * m ^ 13) :=
      Nat.mul_le_mul hN hst
    have hf : r.fuel + 1 ≤ m := by omega
    have hq : (r.fuel + 1) * (7 * (Ib r + Tb r + Ab r + 3) + 30) ≤ m * (40000000 * m ^ 12) :=
      Nat.mul_le_mul hf (by omega)
    have e1 : (6000000 * m ^ 13) * (200000000 * m ^ 13) = 1200000000000000 * m ^ 26 := by ring
    have e2 : m * (40000000 * m ^ 12) = 40000000 * m ^ 13 := by ring
    omega
  have cF : costFin r ≤ 100000000 * m ^ 13 := by unfold costFin; omega
  have cB : costBal r ≤ 100000000 * m ^ 12 := by
    unfold costBal balCost
    have p6 := pw 6 12 (by norm_num); have p0 := pw 0 6 (by norm_num); simp at p0
    have hx : (3 * (requestFormula r).length + 1) * (90 * (requestFormula r).length + 132) ≤
        (1537 * m ^ 6) * (46212 * m ^ 6) := Nat.mul_le_mul (by omega) (by omega)
    have e : (1537 * m ^ 6) * (46212 * m ^ 6) = 71027844 * m ^ 12 := by ring
    omega
  have cE : costEmit r ≤ 10 * (16000 * 130 ^ 6) * m ^ 36 + 6 := by
    unfold costEmit
    have hs : Nat.size (RecoveryOracle.sourceSATCode (requestFormula r)) ≤
        natBitLength (RecoveryOracle.sourceSATCode (requestFormula r)) := by
      unfold natBitLength
      rcases Nat.eq_zero_or_pos (RecoveryOracle.sourceSATCode (requestFormula r)) with h | h
      · rw [h]; simp
      · have := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
          (RecoveryOracle.sourceSATCode (requestFormula r)))
        omega
    nlinarith
  unfold mainCost
  have hm36 : 1 ≤ m ^ 36 := Nat.one_le_pow _ _ hm1
  have pt : m ≤ m ^ 36 := by omega
  have pt12 : m ^ 12 ≤ m ^ 36 := by omega
  have pt13 : m ^ 13 ≤ m ^ 36 := by omega
  have pt26 : m ^ 26 ≤ m ^ 36 := p36
  norm_num at cE ⊢
  omega

end NearCubicGates.Adapters.Compile
