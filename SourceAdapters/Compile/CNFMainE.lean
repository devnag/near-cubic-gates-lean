import SourceAdapters.Compile.CNFMainD

/-!
# The printer, part E: the whole run and X5(b)

 (`lem:multitape-refuter`, Steps 3–4) and proof of `cor:framed-refuter` (`cor:framed-refuter`): from the empty cell
state on the entry word, `mainP` prints exactly the framed native balanced SAT query `requestQueryWord r` of
`requestFormula r` within `mainCost r ≤ 10^20·measure^36` steps, once the register width is at least
`10^40·measure^37` (`mainP_spec`). With the cell size constants `a = 10^40`, `c = 37` this is
`CNFProgramRuns`, and `computationToCNF_of_program` gives the join `ComputationToCNF`.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.RepairSource.VerifierEncoding NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
  NearCubicWires.CanonicalBinary
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem taut_mem : ∀ n i, i < n → circuitInputTautology i ∈ circuitInputTautologies n := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      show circuitInputTautology i ∈ circuitInputTautologies n ++ [circuitInputTautology n]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact List.mem_append_left _ (ih i h)
      · subst h; simp

/-- Every clause code of the formula is below the width once the whole query code is. -/
theorem code_lt (C : Ctx) (r : CNFCompilationRequest)
    (hcode : RecoveryOracle.sourceSATCode (requestFormula r) < 2 ^ C.Wd) (c : List (Bool × ℕ))
    (hc : c ∈ requestFormula r) : Encodable.encode c < 2 ^ C.Wd :=
  lt_of_le_of_lt (le_encodeBalancedList _ _ (List.mem_map_of_mem hc)) hcode

theorem mainP_spec (r : CNFCompilationRequest) (C : Ctx) (hC : C.inp = requestEntryWord r)
    (hW : 10 ^ 40 * r.measure ^ 37 ≤ C.Wd) :
    Hs C mainP a0 (mainCost r) (fun b => b.out = requestQueryWord r) := by
  obtain ⟨sI, sT, sA, sk, sN⟩ := sizes r
  have hw := requestWord_length r
  have hl := requestFormula_length r
  have hbits := requestFormula_bits r
  have hm1 : 1 ≤ r.measure := request_measure_positive r
  have hok := reqGD_ok r
  have hmeas : (code r.verifier).length + r.input.length + r.witnessLength + r.fuel + 1 ≤ r.measure := by
    unfold CNFCompilationRequest.measure; omega
  set m := r.measure with hm
  have pw : ∀ a b, a ≤ b → m ^ a ≤ m ^ b := fun a b h => Nat.pow_le_pow_right hm1 h
  have p1 := pw 0 1 (by norm_num); have p2 := pw 1 2 (by norm_num); have p4 := pw 2 4 (by norm_num)
  have p6 := pw 4 6 (by norm_num); have p12 := pw 6 12 (by norm_num); have p13 := pw 12 13 (by norm_num)
  have p36 := pw 13 36 (by norm_num); have p37 := pw 36 37 (by norm_num)
  simp only [pow_zero, pow_one] at p1 p2
  have hWd : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have big : ∀ x, x ≤ 10 ^ 39 * m ^ 36 → x ≤ C.Wd := fun x hx => by omega
  have bigl : ∀ x, x ≤ 10 ^ 39 * m ^ 36 → x < 2 ^ C.Wd := fun x hx => by have := big x hx; omega
  -- the query code is in range
  have hcode : RecoveryOracle.sourceSATCode (requestFormula r) < 2 ^ C.Wd := by
    set q := RecoveryOracle.sourceSATCode (requestFormula r)
    have h1 : q < 2 ^ natBitLength q := by unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) q
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (big _ (by norm_num at hbits ⊢; omega)))
  -- names
  set D := reqGD r with hD
  set n := r.witnessLength with hn
  set F := r.fuel with hF
  set I := genI D r.input with hI
  set T := genT D with hT
  set A := genA D r.high with hA
  set K := sentK D with hK
  have hDW : D.W ≤ 4 * m ^ 2 := hok.WΛ
  have hDn : D.n = n := rfl
  have eIb : Ib r = initCost (lam r) := rfl
  have eTb : Tb r = tmplCost D (lam r) := rfl
  have eAb : Ab r = accCost (lam r) + rankCost n + 1 := rfl
  have eNb : Nb r = Ib r + F * Tb r + Ab r := rfl
  have ek0 : k0 r = D.W + n + 1 := rfl
  have eK : K = D.W + n + 2 := rfl
  have eScan : costScan r = 6 * (Ib r + Tb r + Ab r) + 60 := rfl
  have eFin : costFin r = 7 * (k0 r + Nb r) + 85 := rfl
  have eMain : mainCost r = parseCost r + dimsCost r + genCost D (lam r) + costScan r + (n * (70 + 4) + 4) +
      costRuns r + costFin r + costBal r + costEmit r + 8 := rfl
  have hnm : n ≤ m := by omega
  have hFm : F + 1 ≤ m := by omega
  -- phase 1: parse
  refine Hs.seqc (t1 := parseCost r) (t2 := dimsCost r + genCost D (lam r) + costScan r + (n * (70 + 4) + 4) +
      costRuns r + costFin r + costBal r + costEmit r + 7)
    (Hs.kp (parseP_spec r C hC (big _ (by omega)))) (fun b1 ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, _, _, _⟩, K1⟩ => ?_)
    (by rw [eMain]; omega)
  have tt1 : TTend b1 := by
    unfold TTend; rw [(K1.2.1 sTT (by decide)).1, (K1.2.1 sTT (by decide)).2]; rfl
  -- phase 2: dimensions
  have hsq : ((code r.verifier).length + r.fuel + 2) ^ 2 + 10 ≤ C.Wd := big _ (by
    have : ((code r.verifier).length + r.fuel + 2) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    omega)
  refine Hs.seqc (t1 := dimsCost r) (t2 := genCost D (lam r) + costScan r + (n * (70 + 4) + 4) +
      costRuns r + costFin r + costBal r + costEmit r + 6)
    (Hs.kp (dimsP_spec r b1 q1 q2 q3 q4 q5 q6 q7 q8 tt1 hsq)) (fun b2 ⟨G2, K2⟩ => ?_) (by omega)
  -- phase 3: generation
  have h2 : b2.env dH = r.high := by rw [K2.1 dH (by decide), q9]
  refine Hs.seqc (t1 := genCost D (lam r)) (t2 := costScan r + (n * (70 + 4) + 4) +
      costRuns r + costFin r + costBal r + costEmit r + 5)
    (Hs.kp (genP_spec D (lam r) hok (le_of_lt (bigl (64 * lam r + 64) (by unfold lam; rw [← hm]; omega))) r.input rfl r.high b2 G2 h2
      (Nat.pow_le_pow_right (by norm_num) (big (D.n + 1) (by omega)))
      (bigl (8 * (D.W + D.n + 2) + 10) (by omega))))
    (fun b3 ⟨⟨E3, M3, G3, l3I, l3T, l3A⟩, K3⟩ => ?_) (by omega)
  change I.length ≤ Ib r at l3I
  change T.length ≤ Tb r at l3T
  change A.length ≤ Ab r at l3A
  have K03 := (K1.trans K2).trans K3
  have htt3 : b3.ram sTT = (I ++ [RTok.inp K] ++ T ++ [RTok.inp K] ++ A ++ [RTok.inp K]).map tcode := by
    rw [E3.tt, ((K1.trans K2).2.1 sTT (by decide)).1]; simp [ttToks, a0, hI, hT, hA, hK]
  have hlen3 : (b3.ram sTT).length = I.length + T.length + A.length + 3 := by rw [htt3]; simp; omega
  have hItoks := requestToks_run r
  have hpay : ∀ t ∈ I ++ T ++ A, tcode t < 8 * K + 1 := by
    intro t ht
    have hp : tpay t ≤ D.W + n + 1 := by
      simp only [List.mem_append] at ht
      rcases ht with (h | h) | h
      · exact requestToks_pay r t (by rw [hItoks]; simp only [runToks, List.mem_append]; exact Or.inl (Or.inl h))
      · exact genT_pay r t h
      · exact requestToks_pay r t (by rw [hItoks]; simp only [runToks, List.mem_append]; exact Or.inr h)
    have := tcode_le t
    show tcode t < 8 * (D.W + D.n + 2) + 1
    omega
  have hNle : (runToks I T A F).length ≤ Nb r := by
    simp only [runToks, List.length_append, len_rep]
    rw [eNb]
    have := Nat.mul_le_mul_left F l3T
    omega
  -- phase 4: scan
  refine Hs.seqc (t1 := costScan r) (t2 := (n * (70 + 4) + 4) + costRuns r + costFin r + costBal r + costEmit r + 4)
    (Hs.kp (Hs.mono (scanP_spec I T A K b3 G3.kc M3 htt3 (by rw [G3.tt, hlen3]) hpay
      (bigl _ (by omega))) (by rw [eScan]; omega)
      (fun b h => h)))
    (fun b4 ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, K4⟩ => ?_) (by omega)
  have K04 := K03.trans K4
  have k4 : KC b4 := KC.of_keep (s := scanP) G3.kc (by decide) K4.1
  have n4 : b4.env dN = n := by rw [K4.1 dN (by decide)]; exact G3.n
  -- phase 5: tautologies
  have hcT : ∀ i < n, ccode 1 i 0 i 1 i < 2 ^ C.Wd := fun i hi => by
    have := code_lt C r hcode (circuitInputTautology i) (by
      rw [requestFormula_rcl]; exact List.mem_append_left _ (taut_mem n i hi))
    rwa [circuitInputTautology, positive, negative, encode_triple] at this
  refine Hs.seqc (t1 := n * (70 + 4) + 4) (t2 := costRuns r + costFin r + costBal r + costEmit r + 3)
    (Hs.kp (tautP_spec n b4 k4 n4 (K04.2.1 sCL (by decide)).1 (K04.2.1 sCL (by decide)).2 hcT (bigl _ (by omega))))
    (fun b5 ⟨⟨t1, t2⟩, K5⟩ => ?_) (by omega)
  have K05 := K04.trans K5
  have z5 : ∀ x ∈ [iIdx, iSp, iWl, iNc], b5.env x = 0 := fun x hx => by
    rw [K05.1 x (by revert hx; decide +revert)]; rfl
  have e5 : ∀ s ∈ [sSK, sWM, sNW], b5.ram s = [] ∧ b5.rc s = 0 := fun s hs => K05.2.1 s (by revert hs; decide +revert)
  have hIR5 : IR n (k0 r) RS.init b5 := by
    refine ⟨KC.of_keep (s := tautP) k4 (by decide) K5.1, by rw [K5.1 dN (by decide), n4], z5 iIdx (by simp), rfl,
      ⟨z5 iSp (by simp), by simp [RS.init], by simp [RS.init]⟩, z5 iWl (by simp), by simp [RS.init],
      by simp [RS.init], z5 iNc (by simp), by simp [RS.init], by simp [RS.init],
      (e5 sNW (by simp)).2, by rw [t1]; simp [RS.init, rclFrom_nil], by rw [t2, t1]; simp,
      by rw [(e5 sSK (by simp)).1]; simp, by rw [(e5 sSK (by simp)).2]; simp,
      by rw [(e5 sWM (by simp)).1]; simp, by rw [(e5 sWM (by simp)).2]; simp,
      by rw [(e5 sNW (by simp)).1]; simp, by simp [RS.init], by simp [RS.init], by simp [RS.init],
      by simp [RS.init]⟩
  have hok5 : RunOK C n (k0 r) RS.init (runToks I T A F) := by
    have := runOK_piece C r [] (runToks I T A F) [] (by rw [hItoks]; simp only [List.nil_append, List.append_nil]; rfl) (k0 r) le_rfl hcode
    simpa using this
  have K45 : ∀ y ∈ [mLI, mLT, mLA, mP2, mP3], b5.env y = b4.env y := fun y hy =>
    K5.1 y (by revert hy; decide +revert)
  have hF5 : b5.env dF = F := by
    rw [(((K2.trans K3).trans K4).trans K5).1 dF (by decide), q8]
  -- phase 6: the interpreter
  refine Hs.seqc (t1 := costRuns r) (t2 := costFin r + costBal r + costEmit r + 2)
    (Hs.kp (Hs.mono (runsP_spec n (k0 r) F K I T A b5 hIR5
      (by rw [(K5.2.1 sTT (by decide)).1, s6]; exact htt3)
      (by rw [(K5.2.1 sTT (by decide)).2, s8])
      (by rw [K45 mLI (by simp), s1]) (by rw [K45 mLT (by simp), s2]) (by rw [K45 mLA (by simp), s3])
      (by rw [K45 mP2 (by simp), s4]) (by rw [K45 mP3 (by simp), s5]) hF5 hok5
      (le_of_lt (bigl _ (by omega))))
      (runsCost_le r I T A l3I l3T l3A) (fun b h => h)))
    (fun b6 ⟨R6, K6⟩ => ?_) (by omega)
  -- phase 7: the output unit
  set S := RS.init.run (runToks I T A F) with hS
  set kF := k0 r + (runToks I T A F).length with hkF
  have hstk : S.stk.length ≤ kF := le_trans R6.stk.len (R6.bsk)
  have htop : (popS S.stk).1 ≤ kF := by
    have := R6.vstk
    cases h : S.stk with
    | nil => simp [popS]
    | cons x l => simp only [popS]; exact this x (by rw [h]; simp)
  have hrcl := requestFormula_rcl r
  rw [hItoks] at hrcl
  have hcU : ccode 1 (n + (popS S.stk).1) 1 (n + (popS S.stk).1) 1 (n + (popS S.stk).1) < 2 ^ C.Wd := by
    have := code_lt C r hcode (positiveUnit (n + (popS S.stk).1)) (by
      rw [hrcl]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
    rwa [positiveUnit, positive, encode_triple] at this
  have hkb : kF ≤ k0 r + Nb r := by omega
  refine Hs.seqc (t1 := costFin r) (t2 := costBal r + costEmit r + 1)
    (Hs.kp (Hs.mono (finP_spec n kF S b6 R6 (bigl _ (by omega)) (bigl _ (by omega)) hcU)
      (by have := R6.rsk; have := R6.bsk; rw [eFin]; omega) (fun b h => h)))
    (fun b7 ⟨⟨f1, f2, f3⟩, K7⟩ => ?_) (by omega)
  rw [← hrcl] at f1
  have K07 := (K05.trans K6).trans K7
  -- phase 8: the balanced code
  set cl := (requestFormula r).map Encodable.encode with hcl
  have hpos : ∀ x ∈ cl, 0 < x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have h3 := requestFormula_three r c hc
    cases c with
    | nil => simp at h3
    | cons a l => rw [Encodable.encode_list_cons]; omega
  have hB : encodeBalancedList cl < 2 ^ C.Wd := hcode
  refine Hs.seqc (t1 := costBal r) (t2 := costEmit r)
    (Hs.mono (balP_spec cl 0 hpos hB (bigl _ (by rw [hcl, List.length_map]; omega)) b7 f3 f1
      (by rw [f2, f1]) (by rw [(K07.2.1 sTK (by decide)).2, (K07.2.1 sVS (by decide)).2]; rfl))
      (by unfold costBal; rw [hcl, List.length_map]) (fun b h => h))
    (fun b8 ⟨y8, k8, o8, _⟩ => ?_) (by omega)
  -- phase 9: the framed bits
  refine Hs.mono (emitBitsF_spec bY (by decide) b8 ⟨k8.z, k8.one, k8.two⟩ (big _ (by omega)))
    (by unfold costEmit; rw [y8]; rfl) ?_
  rintro b9 ⟨e9, _⟩
  rw [e9, o8, K07.2.2 (by decide), y8]
  rfl

/-- **The printing program runs** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`). -/
theorem cnfProgramRuns : CNFProgramRuns mainP (10 ^ 40) 37 mainCost := by
  intro r
  obtain ⟨b, n, he, hn, hb⟩ := mainP_spec r (ctxOf noCallee (cnfSz (10 ^ 40) 37) (requestEntryWord r)) rfl
    (width_ge _ _ r)
  exact ⟨b, n, he, hb, hn⟩

/-- **X5(b): the join `ComputationToCNF`** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`). -/
theorem computationToCNF : ComputationToCNF :=
  computationToCNF_of_program mainP (10 ^ 40) 37 (10 ^ 20) 36 mainCost (by norm_num) cnfProgramRuns mainCost_le

end NearCubicGates.Adapters.Compile
