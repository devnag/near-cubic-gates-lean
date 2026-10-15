import Proof.Gates.Setup.Sizes

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu)
open NearCubicGates.Close.Worker.Format (readCount readField)

theorem pw (N e E : ℕ) (h : e ≤ E) : (N + 1) ^ e ≤ (N + 1) ^ E := Nat.pow_le_pow_right (by omega) h

theorem pw' (N e E : ℕ) (h : e ≤ E) (C : ℕ) : C * (N + 1) ^ e ≤ C * (N + 1) ^ E :=
  Nat.mul_le_mul_left _ (pw N e E h)

theorem two_pow_size (v : ℕ) : 2 ^ v.size ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · have h1 : 1 ≤ v.size := by
      rw [Nat.one_le_iff_ne_zero]; intro h; rw [Nat.size_eq_zero] at h; omega
    have h2 : ¬ v.size ≤ v.size - 1 := by omega
    rw [Nat.size_le] at h2
    have h3 : 2 ^ v.size = 2 * 2 ^ (v.size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-! ## The evaluator's cost -/

theorem evalCost_le (dl lb lp : ℕ) :
    Succinct.evalCost dl lb lp ≤ 100000 * (dl + 2 ^ (lb + lp) + lb + lp + 2) ^ 3 := by
  have hlb : 2 ^ lb ≤ 2 ^ (lb + lp) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold Succinct.evalCost Succinct.nodeCost Succinct.fieldCost
  generalize 2 ^ (lb + lp) = T at hlb ⊢
  generalize 2 ^ lb = U at hlb ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = dl + T + lb + lp + 2 := ⟨_, rfl⟩
  rw [← hX]
  have hX2 : 2 ≤ X := by omega
  have f1 : 400 * (dl + lb + 2) * (U + 1) ≤ 400 * (X * X) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have f2 : 400 * (dl + (lb + lp) + 2) * (T + 1) ≤ 400 * (X * X) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hXX : X ≤ X * X := Nat.le_mul_self X
  have h400 : 4 ≤ X * X := Nat.mul_le_mul hX2 hX2
  obtain ⟨P1, hP1⟩ : ∃ P, P = 400 * (dl + (lb + lp) + 2) * (T + 1) := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, P = 400 * (dl + lb + 2) * (U + 1) := ⟨_, rfl⟩
  rw [← hP1] at f2 ⊢
  rw [← hP2] at f1 ⊢
  have e3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have e4 : X ^ 3 = X * X * X := by ring
  have e2 : (X + 4) * (2000 * (X * X) + 100) ≤ 30000 * (X * X * X) := by nlinarith
  have e1 : (U + 4) * (4 * P1 + 100 * T + 40 * U + 40 * (lb + lp) + 400 + 100) ≤
      (X + 4) * (2000 * (X * X) + 100) := Nat.mul_le_mul (by omega) (by omega)
  rw [e4]
  obtain ⟨X3, hX3⟩ : ∃ Y, Y = X * X * X := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Y, Y = (U + 4) * (4 * P1 + 100 * T + 40 * U + 40 * (lb + lp) + 400 + 100) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Y, Y = (X + 4) * (2000 * (X * X) + 100) := ⟨_, rfl⟩
  rw [← hX3] at e2 e3 ⊢
  rw [← hQ] at e1 ⊢
  rw [← hQ'] at e1 e2
  omega

/-! ## Phase K -/

theorem costK_le (g : GateParams) : ∃ C : ℕ, ∀ N, costK g N (lenL g (nu N)) ≤ C * (N + 1) ^ 2 := by
  set G := g.lenExp + 2 with hG
  have hG2 : g.lenRoot + 1 ≤ G := by rw [hG]; unfold GateParams.lenExp; omega
  obtain ⟨C0, hC0⟩ := polylog_le (10000000000 + 400 * (G + 1) + 400 * (g.lenRoot + 2)) (6 * G)
  refine ⟨3 * C0 + 300, fun N => ?_⟩
  set ν := nu N with hν
  obtain ⟨A, hA⟩ : ∃ A, A = (ν + 1) ^ G := ⟨_, rfl⟩
  have hA1 : ν + 1 ≤ A := by rw [hA]; exact Nat.le_self_pow (by omega) _
  have hL : lenL g ν ≤ A := by rw [hA]; exact Nat.pow_le_pow_left (by omega) _
  have hb : baseOf g ν ≤ A := by
    rw [hA]; unfold baseOf
    exact (Nat.pow_le_pow_left (Nat.le_succ ν) _).trans (Nat.pow_le_pow_right (by omega) hG2)
  have hlb2 : 2 ^ lbOf g ν ≤ 11 * A := by have := two_pow_size (lenL g ν + 4); unfold lbOf; omega
  have hlp2 : 2 ^ lpOf ν ≤ 2 * A := by have := two_pow_size ν; unfold lpOf; omega
  have hlb : lbOf g ν ≤ 11 * A := (Nat.lt_two_pow_self).le.trans hlb2
  have hlp : lpOf ν ≤ 2 * A := (Nat.lt_two_pow_self).le.trans hlp2
  have hAA : A ≤ A * A := Nat.le_mul_self A
  have hX : lenL g ν + 2 ^ (lbOf g ν + lpOf ν) + lbOf g ν + lpOf ν + 2 ≤ 40 * (A * A) := by
    rw [pow_add]
    have : 2 ^ lbOf g ν * 2 ^ lpOf ν ≤ (11 * A) * (2 * A) := Nat.mul_le_mul hlb2 hlp2
    nlinarith
  have hev := evalCost_le (lenL g ν) (lbOf g ν) (lpOf ν)
  have hA6 : A ^ 6 = (ν + 1) ^ (6 * G) := by rw [hA, ← pow_mul, Nat.mul_comm]
  have hpoly := hC0 N
  rw [← hν, ← hA6] at hpoly
  obtain ⟨Y, hY⟩ : ∃ Y, Y = A ^ 6 := ⟨_, rfl⟩
  rw [← hY] at hpoly
  have hA2 : A * A ≤ Y := by rw [hY]; nlinarith [Nat.one_le_pow 4 A (by omega)]
  have hev' : Succinct.evalCost (lenL g ν) (lbOf g ν) (lpOf ν) ≤ 10000000000 * Y := by
    have h1 : (lenL g ν + 2 ^ (lbOf g ν + lpOf ν) + lbOf g ν + lpOf ν + 2) ^ 3 ≤ (40 * (A * A)) ^ 3 :=
      Nat.pow_le_pow_left hX 3
    have h2 : (40 * (A * A)) ^ 3 = 64000 * Y := by rw [hY]; ring
    omega
  have t1 : 60 * (ν + 1) ^ 2 ≤ 60 * Y := by
    have : (ν + 1) ^ 2 ≤ A * A := by rw [sq]; exact Nat.mul_le_mul hA1 hA1
    omega
  have t2 : 100 * (g.lenExp + 3) * (lenL g ν + ν + 1) ^ 2 ≤ 400 * (G + 1) * Y := by
    have : (lenL g ν + ν + 1) ^ 2 ≤ (2 * A) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * A) ^ 2 = 4 * (A * A) := by ring
    have h3 : g.lenExp + 3 = G + 1 := by rw [hG]
    rw [h3]
    calc 100 * (G + 1) * (lenL g ν + ν + 1) ^ 2 ≤ 100 * (G + 1) * (4 * (A * A)) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 100 * (G + 1) * (4 * Y) := Nat.mul_le_mul_left _ (by omega)
      _ = 400 * (G + 1) * Y := by ring
  have t3 : lbOf g ν * (12 * (lenL g ν + 4) + 30) + 1 ≤ 1000 * Y := by
    have : lbOf g ν * (12 * (lenL g ν + 4) + 30) ≤ (11 * A) * (90 * A) := Nat.mul_le_mul hlb (by omega)
    have e : (11 * A) * (90 * A) = 990 * (A * A) := by ring
    have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
    omega
  have t4 : 100 * (g.lenRoot + 2) * (baseOf g ν + ν + 1) ^ 2 ≤ 400 * (g.lenRoot + 2) * Y := by
    have : (baseOf g ν + ν + 1) ^ 2 ≤ (2 * A) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * A) ^ 2 = 4 * (A * A) := by ring
    calc 100 * (g.lenRoot + 2) * (baseOf g ν + ν + 1) ^ 2 ≤ 100 * (g.lenRoot + 2) * (4 * (A * A)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 100 * (g.lenRoot + 2) * (4 * Y) := Nat.mul_le_mul_left _ (by omega)
      _ = 400 * (g.lenRoot + 2) * Y := by ring
  have t5 : 3 * (lbOf g ν + lpOf ν + ν) ≤ 100 * Y := by omega
  have hck : Succinct.checkCost (lenL g ν) (lbOf g ν) (lpOf ν) N ≤
      (N + 1) * (10000000000 * Y + 14 * N + 50) + 80 * N + 40 := by
    unfold Succinct.checkCost Succinct.pointCost
    have : Succinct.evalCost (lenL g ν) (lbOf g ν) (lpOf ν) + 14 * N + 40 + 10 ≤ 10000000000 * Y + 14 * N + 50 := by
      omega
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _) _
  have hYC : (10000000000 + 400 * (G + 1) + 400 * (g.lenRoot + 2)) * Y ≤ C0 * (N + 1) := hpoly
  have hYs : 10000000000 * Y + 400 * (G + 1) * Y + 400 * (g.lenRoot + 2) * Y ≤ C0 * (N + 1) := by
    have e : (10000000000 + 400 * (G + 1) + 400 * (g.lenRoot + 2)) * Y =
        10000000000 * Y + 400 * (G + 1) * Y + 400 * (g.lenRoot + 2) * Y := by ring
    omega
  have hsum : costK g N (lenL g ν) ≤ 101 * N + 99 + 2 * (C0 * (N + 1)) +
      (N + 1) * (10000000000 * Y + 14 * N + 50) := by
    unfold costK
    simp only [← hν]
    have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
    omega
  have hm : (N + 1) * (10000000000 * Y + 14 * N + 50) ≤ (N + 1) * (C0 * (N + 1) + 14 * N + 50) :=
    Nat.mul_le_mul_left _ (by omega)
  have e5 : (N + 1) * (C0 * (N + 1) + 14 * N + 50) = C0 * (N + 1) ^ 2 + 14 * (N * (N + 1)) + 50 * (N + 1) := by
    ring
  have h7 : N * (N + 1) ≤ (N + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  have h8 : C0 * (N + 1) ≤ C0 * (N + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have h9 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e6 : (3 * C0 + 300) * (N + 1) ^ 2 = 3 * (C0 * (N + 1) ^ 2) + 300 * (N + 1) ^ 2 := by ring
  rw [e6]
  omega

/-! ## Phase R -/

theorem costR_le (g : GateParams) (s : GateSources) (R : OuterM.ARun s.mw (g.sv s)) :
    ∃ C : ℕ, ∀ N, costR R N ≤ C * (N + 1) := by
  obtain ⟨C0, hC0⟩ := polylog_le (2 * R.K) R.e
  refine ⟨C0 + 60, fun N => ?_⟩
  have h := hC0 N
  have hν : nu N ≤ N := Nat.log_le_self 2 N
  unfold costR
  have e : 2 * (R.K * (nu N + 1) ^ R.e) = 2 * R.K * (nu N + 1) ^ R.e := by ring
  rw [e]
  have e2 : (C0 + 60) * (N + 1) = C0 * (N + 1) + 60 * (N + 1) := by ring
  rw [e2]
  omega

/-! ## The guessed fields -/

theorem fields_le (N : ℕ) (bits : List Bool) (pad : ℕ) (hpad : N / 16 + 1 ≤ pad) :
    (readField (guessWord N bits pad)).1.length ≤ N / 16 ∧
      (readField (readField (guessWord N bits pad)).2).1.length ≤ N / 16 := by
  obtain ⟨-, h1, h2, -⟩ := guessWord_split N bits pad hpad
  obtain ⟨-, h3, -⟩ := field2_split N bits pad hpad
  obtain ⟨-, e2, -⟩ := fields_padB N bits pad
  refine ⟨by omega, ?_⟩
  rw [← e2]; exact h3

/-! ## Phase B -/

theorem fdCost_le (n b : ℕ) : fdCost n b ≤ 100 * (n + 1) + 2 * b := by unfold fdCost; omega

theorem oracleCost_le (x bits ab : List Bool) :
    Worker.oracleCost x bits ab ≤ 100 * (x.length + bits.length + 1) +
      2 * RepairOrdinary.CloseoutWitness.Oracle.budget x bits ab := by
  unfold Worker.oracleCost; omega

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

theorem costB_le (W : OuterM.WidthDonor s.mw (g.sv s)) : ∃ C : ℕ, ∀ (N : ℕ) (x : BitInput N) (bits : List Bool)
    (pad : ℕ), 2 ≤ N → width s g N ≤ N → N / 16 + 1 ≤ pad → costB W x bits pad ≤ C * (N + 1) ^ 25 := by
  refine ⟨1000 * (W.K + 1) + 200 + 2 * (2 * (40000000000000000000000 * 2 ^ 25)), fun N x bits pad hN hq hpad => ?_⟩
  obtain ⟨h1, h2⟩ := fields_le N bits pad hpad
  have c1 := cold_le x (readField (guessWord N bits pad)).1 (width s g N) hN (by omega) hq
  have c2 := cold_le x (readField (readField (guessWord N bits pad)).2).1 (width s g N) hN (by omega) hq
  have o1 := oracleCost_le (List.ofFn x) (readField (guessWord N bits pad)).1 (width s g N).bits
  have o2 := oracleCost_le (List.ofFn x) (readField (readField (guessWord N bits pad)).2).1 (width s g N).bits
  have fd := fdCost_le N (2 * (W.K * (N + 1) ^ 1) + 2)
  rw [List.length_ofFn] at o1 o2
  have hP : N + 1 ≤ (N + 1) ^ 25 := Nat.le_self_pow (by norm_num) _
  have hK : W.K * (N + 1) ^ 1 ≤ W.K * (N + 1) ^ 25 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  unfold costB
  have e : (1000 * (W.K + 1) + 200 + 2 * (2 * (40000000000000000000000 * 2 ^ 25))) * (N + 1) ^ 25 =
      1000 * (W.K * (N + 1) ^ 25) + 1200 * (N + 1) ^ 25 +
        4 * (40000000000000000000000 * 2 ^ 25 * (N + 1) ^ 25) := by ring
  rw [e]
  omega

/-! ## The pad-free sizes of an accepting run -/

/-- The size exponent fixed by the composite's uniform exponent `E` and the PCPP's output exponent `e_P`. -/
def EA (E eP : ℕ) : ℕ := 30 * (E + 1) * (eP + 1) + 30

theorem EA_ge (E eP : ℕ) : 25 * E + 27 ≤ EA E eP ∧ 27 * eP ≤ EA E eP ∧ 27 ≤ EA E eP := by
  unfold EA; refine ⟨?_, ?_, ?_⟩ <;> nlinarith

section Core
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (cf : CompFull s P g) (E : ℕ) (hcfe : cf.e ≤ E)
  (R : OuterM.ARun s.mw (g.sv s)) (KP eP : ℕ)
  (hP : ∀ C : Circuit, (P.output C).proofBits ≤ KP * (C.m + 1) ^ eP ∧ 2 ^ (P.output C).randomBits ≤ KP * (C.m + 1) ^ eP)
  (Kc : ℕ) (hcode : ∀ n, 2 ≤ n → P.code.length n ≤ Kc * (n + 1))
  (N0 : ℕ) (hq : ∀ N, N0 ≤ N → 4 ≤ N ∧ width s g N + 1 ≤ N ∧ 1 ≤ nu N)

include hcfe hP hcode hq R in
/-- **The pad-free sizes and budgets of an accepting run**, at the exponent `EA E e_P`. -/
theorem core_le : ∃ C : ℕ, ∀ (N : ℕ) (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)), N0 ≤ N → N / 16 + 1 ≤ pad →
    Worker.Decodes (width s g N) (guessWord N bits pad) B →
    N + width s g N + gadgets s g N + auxN s P g x B + (pcpp s P g x B).randomBits + (pcpp s P g x B).word.length +
      (supportsWord P.code (width s g N)).length + (mwWord s g N B.src).length + (PCPPNative.descriptor B.src).length +
      (PCPPNative.descriptor B.pf).length +
      cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e +
      nu N ^ (g.lenRoot + 1) ≤ C * (N + 1) ^ EA E eP := by
  obtain ⟨CM, hCM⟩ := gadgets_lin s g
  obtain ⟨CR, hCR⟩ := polylog_le R.K R.e
  obtain ⟨Cb, hCb⟩ := polylog_le 1 (g.lenRoot + 1)
  obtain ⟨CC, hCC⟩ := outC_lin (s := s) g
  let Kd := 40000000000000000000000 * 2 ^ 25 + 9
  let Cmw := 2 * Kd + CR + 1
  let Csh := Cmw + Kd + 2
  let Cfu := cf.C * Csh ^ E
  let Cm := CC * (Kd + 1) + Kc * 7 + 10
  let Cpb := KP * Cm ^ eP
  refine ⟨1 + 1 + CM + (Cpb + CM) + Cpb + 2 * (Cmw + Kd + Cfu) + Cmw + Kd + Kd + Cfu + Cb + 10, fun N x bits pad B hN
    hpad hdec => ?_⟩
  obtain ⟨hN4, hqN, hν1⟩ := hq N hN
  have hq2 : 2 ≤ width s g N := Worker.two_le_nativeWidth s g N hN4
  obtain ⟨hf1, hf2⟩ := fields_le N bits pad hpad
  have hqb : (width s g N).bits.length ≤ N + 1 := (LitDecode.bits_len_le _).trans (by omega)
  have hX1 : 1 ≤ (N + 1) ^ 25 := Nat.one_le_pow _ _ (by omega)
  have hNp : N + 1 ≤ (N + 1) ^ 25 := Nat.le_self_pow (by norm_num) _
  -- the descriptors
  have hd1 : (PCPPNative.descriptor B.src).length ≤ Kd * (N + 1) ^ 25 := by
    have h1 := desc_le x _ _ B.src (by omega) (by omega) hqb hdec.1
    have h2 := cold_le x (readField (guessWord N bits pad)).1 (width s g N) (by omega) (by omega) (by omega)
    have : 6 * N + 3 ≤ 9 * (N + 1) ^ 25 := by omega
    calc _ ≤ 6 * N + 3 + 40000000000000000000000 * 2 ^ 25 * (N + 1) ^ 25 := by omega
      _ ≤ 9 * (N + 1) ^ 25 + 40000000000000000000000 * 2 ^ 25 * (N + 1) ^ 25 := by omega
      _ = Kd * (N + 1) ^ 25 := by ring
  have hd2 : (PCPPNative.descriptor B.pf).length ≤ Kd * (N + 1) ^ 25 := by
    have h1 := desc_le x _ _ B.pf (by omega) (by omega) hqb hdec.2
    have h2 := cold_le x (readField (readField (guessWord N bits pad)).2).1 (width s g N) (by omega) (by omega)
      (by omega)
    have : 6 * N + 3 ≤ 9 * (N + 1) ^ 25 := by omega
    calc _ ≤ 6 * N + 3 + 40000000000000000000000 * 2 ^ 25 * (N + 1) ^ 25 := by omega
      _ ≤ 9 * (N + 1) ^ 25 + 40000000000000000000000 * 2 ^ 25 * (N + 1) ^ 25 := by omega
      _ = Kd * (N + 1) ^ 25 := by ring
  -- the word of `C^O_{⟨B_src⟩_ν}`
  have hmw : (mwWord s g N B.src).length ≤ Cmw * (N + 1) ^ 25 := by
    have h1 := mw_le R B.src
    have h2 := hCR N
    have hν : nu N ≤ N := Nat.log_le_self 2 N
    have : CR * (N + 1) ≤ CR * (N + 1) ^ 25 := Nat.mul_le_mul_left _ hNp
    calc _ ≤ Kd * (N + 1) ^ 25 + N + CR * (N + 1) ^ 25 := by omega
      _ ≤ Kd * (N + 1) ^ 25 + Kd * (N + 1) ^ 25 + CR * (N + 1) ^ 25 + (N + 1) ^ 25 := by
          have : N ≤ Kd * (N + 1) ^ 25 := le_trans (by omega) (Nat.mul_le_mul_right _ (by omega : 1 ≤ Kd))
          omega
      _ = Cmw * (N + 1) ^ 25 := by ring
  -- the composite's fuel
  obtain ⟨Sh, hSh⟩ : ∃ n, n = (mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1 :=
    ⟨_, rfl⟩
  have hSh1 : 1 ≤ Sh := by omega
  have hShb : Sh ≤ Csh * (N + 1) ^ 25 := by
    have : Sh ≤ Cmw * (N + 1) ^ 25 + Kd * (N + 1) ^ 25 + 2 * (N + 1) ^ 25 := by omega
    calc Sh ≤ Cmw * (N + 1) ^ 25 + Kd * (N + 1) ^ 25 + 2 * (N + 1) ^ 25 := this
      _ = Csh * (N + 1) ^ 25 := by ring
  have hfuel : cf.C * Sh ^ cf.e ≤ Cfu * (N + 1) ^ (25 * E) := by
    calc cf.C * Sh ^ cf.e ≤ cf.C * Sh ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hSh1 hcfe)
      _ ≤ cf.C * (Csh * (N + 1) ^ 25) ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hShb E)
      _ = Cfu * (N + 1) ^ (25 * E) := by rw [mul_pow, ← pow_mul]; ring
  -- the composite's outputs
  have hout := comp_out_le cf x B hq2
  rw [← hSh] at hout
  have hsupp := frame_len (supportsWord P.code (width s g N))
  -- the checked circuit and the PCPP's sizes
  have hm := checked_m_le (P := P) x B
  have hC := hCC N hν1 B.src
  have hpfs : B.pf.size ≤ Kd * (N + 1) ^ 25 :=
    (show B.pf.size ≤ (PCPPNative.descriptor B.pf).length from nodes_le_descriptor B.pf).trans hd2
  have hL := hcode (width s g N) hq2
  have hm1 : (checkedCircuit P.code (Worker.substituted s g x B)).m + 1 ≤ Cm * (N + 1) ^ 27 := by
    have h1 : (Outer.outC s.mw (g.sv s) (nu N) B.src).circuit.size * (B.pf.size + 1) ≤
        (CC * (N + 1)) * ((Kd + 1) * (N + 1) ^ 25) := Nat.mul_le_mul hC (by
          have : 1 ≤ (N + 1) ^ 25 := hX1
          have e : (Kd + 1) * (N + 1) ^ 25 = Kd * (N + 1) ^ 25 + (N + 1) ^ 25 := by ring
          omega)
    have e1 : (CC * (N + 1)) * ((Kd + 1) * (N + 1) ^ 25) = CC * (Kd + 1) * (N + 1) ^ 26 := by ring
    have h2 : P.code.length (width s g N) * (8 + 5 * width s g N) ≤ (Kc * (N + 1)) * (5 * (N + 1)) :=
      Nat.mul_le_mul (hL.trans (Nat.mul_le_mul_left _ (by omega))) (by omega)
    have e2 : (Kc * (N + 1)) * (5 * (N + 1)) = 5 * Kc * (N + 1) ^ 2 := by ring
    have hL' : P.code.length (width s g N) ≤ Kc * (N + 1) := hL.trans (Nat.mul_le_mul_left _ (by omega))
    have p26 : (N + 1) ^ 26 ≤ (N + 1) ^ 27 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p2 : (N + 1) ^ 2 ≤ (N + 1) ^ 27 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p1 : N + 1 ≤ (N + 1) ^ 27 := Nat.le_self_pow (by norm_num) _
    have e3 : Cm * (N + 1) ^ 27 = CC * (Kd + 1) * (N + 1) ^ 27 + Kc * 7 * (N + 1) ^ 27 + 10 * (N + 1) ^ 27 := by ring
    have q1 : CC * (Kd + 1) * (N + 1) ^ 26 ≤ CC * (Kd + 1) * (N + 1) ^ 27 := Nat.mul_le_mul_left _ p26
    have q2 : 5 * Kc * (N + 1) ^ 2 ≤ 5 * Kc * (N + 1) ^ 27 := Nat.mul_le_mul_left _ p2
    have q3 : Kc * (N + 1) ≤ Kc * (N + 1) ^ 27 := Nat.mul_le_mul_left _ p1
    have e4 : Kc * 7 * (N + 1) ^ 27 = 5 * Kc * (N + 1) ^ 27 + Kc * (N + 1) ^ 27 + Kc * (N + 1) ^ 27 := by ring
    rw [e3]
    omega
  obtain ⟨hpb, hrb⟩ := hP (checkedCircuit P.code (Worker.substituted s g x B))
  obtain ⟨m, hmdef⟩ : ∃ m, m = (checkedCircuit P.code (Worker.substituted s g x B)).m := ⟨_, rfl⟩
  rw [← hmdef] at hm1 hpb hrb
  have hmp : KP * (m + 1) ^ eP ≤ Cpb * (N + 1) ^ (27 * eP) := by
    calc KP * (m + 1) ^ eP ≤ KP * (Cm * (N + 1) ^ 27) ^ eP := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm1 eP)
      _ = Cpb * (N + 1) ^ (27 * eP) := by rw [mul_pow, ← pow_mul]; ring
  have hpbE : (pcpp s P g x B).proofBits = (P.output (checkedCircuit P.code (Worker.substituted s g x B))).proofBits :=
    rfl
  have hrbE : (pcpp s P g x B).randomBits =
      (P.output (checkedCircuit P.code (Worker.substituted s g x B))).randomBits := rfl
  have hpb' : (pcpp s P g x B).proofBits ≤ Cpb * (N + 1) ^ (27 * eP) := by rw [hpbE]; exact hpb.trans hmp
  have hrb' : (pcpp s P g x B).randomBits ≤ Cpb * (N + 1) ^ (27 * eP) := by
    rw [hrbE]; exact (Nat.lt_two_pow_self).le.trans (hrb.trans hmp)
  -- the base
  have hbase : nu N ^ (g.lenRoot + 1) ≤ Cb * (N + 1) := by
    have := hCb N
    have h1 : nu N ^ (g.lenRoot + 1) ≤ (nu N + 1) ^ (g.lenRoot + 1) := Nat.pow_le_pow_left (by omega) _
    omega
  -- everything at `X = (N+1)^EA`
  obtain ⟨g1, g2, g3⟩ := EA_ge E eP
  have e1 := pw N 1 (EA E eP) (by omega)
  have e25 := pw N 25 (EA E eP) (by omega)
  have e25E := pw N (25 * E) (EA E eP) (by omega)
  have e27 := pw N (27 * eP) (EA E eP) (by omega)
  have hp1 : N + 1 = (N + 1) ^ 1 := (pow_one _).symm
  obtain ⟨X, hX⟩ : ∃ n, n = (N + 1) ^ EA E eP := ⟨_, rfl⟩
  rw [← hX] at e1 e25 e25E e27
  have b0 : N + 1 ≤ X := by rw [hp1]; exact e1
  have bM : gadgets s g N ≤ CM * X := (hCM N).trans (Nat.mul_le_mul_left _ b0)
  have bpb : (pcpp s P g x B).proofBits ≤ Cpb * X := hpb'.trans (Nat.mul_le_mul_left _ e27)
  have brb : (pcpp s P g x B).randomBits ≤ Cpb * X := hrb'.trans (Nat.mul_le_mul_left _ e27)
  have bmw : (mwWord s g N B.src).length ≤ Cmw * X := hmw.trans (Nat.mul_le_mul_left _ e25)
  have bd1 : (PCPPNative.descriptor B.src).length ≤ Kd * X := hd1.trans (Nat.mul_le_mul_left _ e25)
  have bd2 : (PCPPNative.descriptor B.pf).length ≤ Kd * X := hd2.trans (Nat.mul_le_mul_left _ e25)
  have bfu : cf.C * Sh ^ cf.e ≤ Cfu * X := hfuel.trans (Nat.mul_le_mul_left _ e25E)
  have bb : nu N ^ (g.lenRoot + 1) ≤ Cb * X := hbase.trans (Nat.mul_le_mul_left _ b0)
  have haux : auxN s P g x B = (pcpp s P g x B).proofBits + gadgets s g N := rfl
  rw [haux, ← hSh, ← hX]
  have e : (1 + 1 + CM + (Cpb + CM) + Cpb + 2 * (Cmw + Kd + Cfu) + Cmw + Kd + Kd + Cfu + Cb + 10) * X =
      X + X + CM * X + (Cpb * X + CM * X) + Cpb * X + 2 * (Cmw * X + Kd * X + Cfu * X) + Cmw * X + Kd * X +
        Kd * X + Cfu * X + Cb * X + 10 * X := by ring
  rw [e]
  omega

end Core

end NearCubicGates.Close.Setup
