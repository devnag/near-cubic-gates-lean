import Proof.Gates.Setup.Core
import Proof.Gates.Setup.UniformSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu)
open NearCubicGates.Close.Worker.Format (readCount readField)

theorem guessWord_prefix (N : ℕ) (bits : List Bool) (pad : ℕ) :
    guessWord N bits pad = guessWord N (List.ofFn fun i : Fin (N / 16) => bits.getD i.val false) pad := by
  unfold guessWord Codec.prefixBits
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The rejecting runs' cost reads the witness only through its first `⌊N/16⌋` bits. -/
theorem rejectCostOf_prefix {s : GateSources} {g : GateParams} (W : OuterM.WidthDonor s.mw (g.sv s))
    (R : OuterM.ARun s.mw (g.sv s)) (N0 : ℕ) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) :
    rejectCostOf s g W R N0 x bits pad =
      rejectCostOf s g W R N0 x (List.ofFn fun i : Fin (N / 16) => bits.getD i.val false) pad := by
  unfold rejectCostOf costB
  rw [← guessWord_prefix]

theorem le_mulZ (a Z : ℕ) (h : 1 ≤ Z) : a ≤ a * Z := Nat.le_mul_of_pos_right a h

theorem e_facts (EA ep : ℕ) :
    25 ≤ (16 * EA + 100) * (ep + 1) ∧ EA ≤ (16 * EA + 100) * (ep + 1) ∧
      5 * EA + 15 * (ep + 1) ≤ (16 * EA + 100) * (ep + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

section Bounds
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- **The accepting run's set-up size** from the pad-free bound and the padding (pure arithmetic). -/
theorem setupSize_le (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) (q1 : width s g N + 1 ≤ N) (Cc XA Cp Z : ℕ)
    (hcore : N + width s g N + gadgets s g N + auxN s P g x B + (pcpp s P g x B).randomBits +
      (pcpp s P g x B).word.length + (supportsWord P.code (width s g N)).length + (mwWord s g N B.src).length +
      (PCPPNative.descriptor B.src).length + (PCPPNative.descriptor B.pf).length +
      D.cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ D.cf.e +
      nu N ^ (g.lenRoot + 1) ≤ Cc * XA)
    (hXA : 1 ≤ XA) (hZ : N + 1 ≤ Z) (hpadZ : pad ≤ Cp * Z) :
    setupSize D x bits pad B + 1 ≤ (Cc + Cp + D.N0 + 2 + 80 * Cc * (Cp + 2) ^ 2) * (XA * Z ^ 3) := by
  have hZ1 : 1 ≤ Z := by omega
  have hZ3 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) _
  have hW : XA ≤ XA * Z ^ 3 := le_mulZ XA (Z ^ 3) (by omega)
  have hZW : Z ≤ XA * Z ^ 3 := hZ3.trans (Nat.le_mul_of_pos_left _ (by omega))
  obtain ⟨W, hWdef⟩ : ∃ w, w = XA * Z ^ 3 := ⟨_, rfl⟩
  rw [← hWdef] at hW hZW ⊢
  have hwl : (guessWord N bits pad).length = N / 16 + pad := guessWord_length N bits pad
  have hcw := cwPrefix_le (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)) (auxN s P g x B)
  have hw1 : (guessWord N bits pad).length + 1 ≤ (Cp + 2) * Z := by
    have : N / 16 ≤ N := Nat.div_le_self _ _
    have e : (Cp + 2) * Z = Cp * Z + 2 * Z := by ring
    rw [hwl, e]; omega
  have hq1 : width s g N + 1 ≤ Z := by omega
  have hf : 80 * ((guessWord N bits pad).length + 1) ^ 2 * (width s g N + 1) ≤ 80 * (Cp + 2) ^ 2 * Z ^ 3 := by
    have h1 := Nat.pow_le_pow_left hw1 2
    have h2 : ((Cp + 2) * Z) ^ 2 * Z = (Cp + 2) ^ 2 * Z ^ 3 := by ring
    calc 80 * ((guessWord N bits pad).length + 1) ^ 2 * (width s g N + 1)
        ≤ 80 * ((Cp + 2) * Z) ^ 2 * Z := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) hq1
      _ = 80 * (Cp + 2) ^ 2 * Z ^ 3 := by rw [Nat.mul_assoc, h2, ← Nat.mul_assoc]
  have haux : auxN s P g x B ≤ Cc * XA := by omega
  have hcw2 : (Codec.cwPrefix (Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)))
      (auxN s P g x B)).length ≤ 80 * Cc * (Cp + 2) ^ 2 * W := by
    calc _ ≤ auxN s P g x B * (80 * ((guessWord N bits pad).length + 1) ^ 2 * (width s g N + 1)) := hcw
      _ ≤ (Cc * XA) * (80 * (Cp + 2) ^ 2 * Z ^ 3) := Nat.mul_le_mul haux hf
      _ = 80 * Cc * (Cp + 2) ^ 2 * W := by rw [hWdef]; ring
  have hpw : pad ≤ Cp * W := hpadZ.trans (Nat.mul_le_mul_left _ hZW)
  have hcW : Cc * XA ≤ Cc * W := Nat.mul_le_mul_left _ hW
  have hN0W : D.N0 + 2 ≤ (D.N0 + 2) * W := le_mulZ _ _ (by omega)
  have e : (Cc + Cp + D.N0 + 2 + 80 * Cc * (Cp + 2) ^ 2) * W =
      Cc * W + Cp * W + (D.N0 + 2) * W + 80 * Cc * (Cp + 2) ^ 2 * W := by ring
  rw [e, setupSize_eq]
  have hauxE : auxN s P g x B = (pcpp s P g x B).proofBits + gadgets s g N := rfl
  rw [hauxE] at hcw2 hcore
  omega

end Bounds

theorem setupU_of (s : GateSources) (P : ThreeQueryPCPP) (hC : CompU s P)
    (W : ∀ g : GateParams, OuterM.WidthDonor s.mw (g.sv s)) (R : ∀ g : GateParams, OuterM.ARun s.mw (g.sv s)) :
    SetupU s P := by
  obtain ⟨E, hE⟩ := hC
  obtain ⟨KP, eP, hP⟩ := P.outputSize
  obtain ⟨Kc, hcode⟩ := P.codeLength
  refine ⟨16 * EA E eP + 100, fun g tc N1' => ?_⟩
  obtain ⟨cf, hcfe⟩ := hE g
  obtain ⟨Nq, hNq⟩ := qpoly_le s g 1 1
  obtain ⟨T, hT⟩ : ∃ T, T = 2 ^ ((g.sv s).onset + 2) := ⟨_, rfl⟩
  set N0 := N1' + Nq + T + 4 with hN0def
  have hlog : ∀ N, N0 ≤ N → (g.sv s).onset + 2 ≤ nu N := fun N hN =>
    Nat.le_log_of_pow_le (by norm_num) (by rw [← hT]; omega)
  have hq : ∀ N, N0 ≤ N → 4 ≤ N ∧ width s g N + 1 ≤ N ∧ 1 ≤ nu N := fun N hN => by
    have h1 := hNq N (by omega)
    have h2 := hlog N hN
    simp only [one_mul, pow_one] at h1
    exact ⟨by omega, h1, by omega⟩
  have hN0 : ∀ N, N0 ≤ N → 4 ≤ N ∧ (width s g N).bits.length ≤ N + 1 := fun N hN => by
    obtain ⟨h4, hw, -⟩ := hq N hN
    exact ⟨h4, (LitDecode.bits_len_le _).trans (by omega)⟩
  have hon : ∀ N, N0 ≤ N → (g.sv s).onset ≤ nu N := fun N hN => by
    have h2 := hlog N hN
    omega
  set D := mkSetupData s P g cf (W g) (R g) tc N0 hN0 with hD
  obtain ⟨Cc, hCc⟩ := core_le s P g cf E hcfe (R g) KP eP hP Kc hcode N0 hq
  have hEA : EA E eP ≤ 16 * EA E eP + 100 := by omega
  refine ⟨D, ⟨setupP D (W g) (R g), setup_ideal cf (W g) (R g) tc N0 hN0 hon⟩, rfl, by
    show N1' ≤ N0; omega, ⟨Cc, fun N x bits pad B hN hpad hdec => ?_⟩, fun padF Cp ep hpadF hpadC => ?_⟩
  · have := hCc N x bits pad B hN hpad hdec
    exact (by omega : auxN s P g x B + gadgets s g N ≤ Cc * (N + 1) ^ EA E eP).trans (pw' N _ _ hEA Cc)
  obtain ⟨f1, f2, f3⟩ := e_facts (EA E eP) ep
  obtain ⟨E1, hE1⟩ : ∃ e, e = (16 * EA E eP + 100) * (ep + 1) := ⟨_, rfl⟩
  rw [← hE1] at f1 f2 f3
  obtain ⟨CK, hCK⟩ := costK_le g
  obtain ⟨CRr, hCRr⟩ := costR_le g s (R g)
  obtain ⟨CB, hCB⟩ := costB_le (s := s) (g := g) (W g)
  let K1 := Cc + Cp + D.N0 + 2 + 80 * Cc * (Cp + 2) ^ 2
  let Krej := 2000 * (N0 + 1) + 1000 + CB + CRr + CK + 100
  let Kacc := Krej + 2 * Cc + 1000000000000 * K1 ^ 5 + 100
  have hZ : ∀ N, N + 1 ≤ (N + 1) ^ (ep + 1) := fun N => Nat.le_self_pow (by omega) _
  have hpZ : ∀ N, padF N ≤ Cp * (N + 1) ^ (ep + 1) := fun N =>
    (hpadC N).trans (pw' N ep (ep + 1) (by omega) Cp)
  have hrejD : ∀ {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ),
      rejectCost D x bits pad = rejectCostOf s g (W g) (R g) N0 x bits pad := fun _ _ _ => rfl
  have hrej : ∀ N, N0 ≤ N → ∀ (x : BitInput N) (bits : List Bool),
      rejectCost D x bits (padF N) ≤ Krej * (N + 1) ^ E1 := by
    intro N hN x bits
    obtain ⟨h4, hqN, -⟩ := hq N hN
    rw [hrejD]
    unfold rejectCostOf powCostP
    have hB := hCB N x bits (padF N) (by omega) (by omega) (hpadF N)
    have hK := hCK N
    have hR := hCRr N
    have p1 : N + 1 ≤ (N + 1) ^ E1 := by have := pw N 1 E1 (by omega); simpa using this
    have p2 : (N + 1) ^ 2 ≤ (N + 1) ^ E1 := pw N 2 E1 (by omega)
    have p25 : (N + 1) ^ 25 ≤ (N + 1) ^ E1 := pw N 25 E1 f1
    have q1 : CB * (N + 1) ^ 25 ≤ CB * (N + 1) ^ E1 := Nat.mul_le_mul_left _ p25
    have q2 : CK * (N + 1) ^ 2 ≤ CK * (N + 1) ^ E1 := Nat.mul_le_mul_left _ p2
    have q3 : CRr * (N + 1) ≤ CRr * (N + 1) ^ E1 := Nat.mul_le_mul_left _ p1
    have q4 : 1000 * (N + 1) ^ 2 ≤ 1000 * (N + 1) ^ E1 := Nat.mul_le_mul_left _ p2
    have q5 : 2000 * (N + N0 + 1) ≤ 2000 * (N0 + 1) * (N + 1) ^ E1 := by
      have : N + N0 + 1 ≤ (N0 + 1) * (N + 1) := by nlinarith
      have h' : (N0 + 1) * (N + 1) ≤ (N0 + 1) * (N + 1) ^ E1 := Nat.mul_le_mul_left _ p1
      calc 2000 * (N + N0 + 1) ≤ 2000 * ((N0 + 1) * (N + 1) ^ E1) := Nat.mul_le_mul_left _ (this.trans h')
        _ = 2000 * (N0 + 1) * (N + 1) ^ E1 := by ring
    have hX1 : 1 ≤ (N + 1) ^ E1 := Nat.one_le_pow _ _ (by omega)
    have e : Krej * (N + 1) ^ E1 = 2000 * (N0 + 1) * (N + 1) ^ E1 + 1000 * (N + 1) ^ E1 + CB * (N + 1) ^ E1 +
        CRr * (N + 1) ^ E1 + CK * (N + 1) ^ E1 + 100 * (N + 1) ^ E1 := by ring
    rw [e]
    omega
  have hacc : ∀ N, N0 ≤ N → ∀ (x : BitInput N) (bits : List Bool) (B : Outer.OuterGuess (width s g N)),
      Worker.Decodes (width s g N) (guessWord N bits (padF N)) B →
      setupCost D x bits (padF N) B ≤ Kacc * (N + 1) ^ E1 := by
    intro N hN x bits B hdec
    obtain ⟨h4, hqN, -⟩ := hq N hN
    have hc := hCc N x bits (padF N) B hN (hpadF N) hdec
    have hXA : 1 ≤ (N + 1) ^ EA E eP := Nat.one_le_pow _ _ (by omega)
    have hS := setupSize_le D x bits (padF N) B hqN Cc _ Cp _ hc hXA (hZ N) (hpZ N)
    have hS5 : (setupSize D x bits (padF N) B + 1) ^ 5 ≤ K1 ^ 5 * (N + 1) ^ E1 := by
      have h1 := Nat.pow_le_pow_left hS 5
      have e : (K1 * ((N + 1) ^ EA E eP * ((N + 1) ^ (ep + 1)) ^ 3)) ^ 5 =
          K1 ^ 5 * (N + 1) ^ (5 * EA E eP + 15 * (ep + 1)) := by
        rw [mul_pow, ← pow_mul, mul_pow, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
      exact h1.trans (by rw [e]; exact pw' N _ _ f3 _)
    have hrj := hrej N hN x bits
    have hfuel : cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e ≤
        Cc * (N + 1) ^ E1 := by
      have := hc
      have h2 : Cc * (N + 1) ^ EA E eP ≤ Cc * (N + 1) ^ E1 := pw' N _ _ f2 Cc
      omega
    have hSC : setupCost D x bits (padF N) B = rejectCost D x bits (padF N) +
        2 * (cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e) +
        1000000000000 * (setupSize D x bits (padF N) B + 1) ^ 5 + 100 := rfl
    rw [hSC]
    have hX1 : 1 ≤ (N + 1) ^ E1 := Nat.one_le_pow _ _ (by omega)
    have e : Kacc * (N + 1) ^ E1 = Krej * (N + 1) ^ E1 + 2 * (Cc * (N + 1) ^ E1) +
        1000000000000 * (K1 ^ 5 * (N + 1) ^ E1) + 100 * (N + 1) ^ E1 := by ring
    rw [e]
    have : 1000000000000 * (setupSize D x bits (padF N) B + 1) ^ 5 ≤ 1000000000000 * (K1 ^ 5 * (N + 1) ^ E1) :=
      Nat.mul_le_mul_left _ hS5
    omega
  let Rs : ℕ → ℕ := fun N => Finset.univ.sup (fun p : BitInput N × BitInput (N / 16) =>
    rejectCostOf s g (W g) (R g) N0 p.1 (List.ofFn p.2) (padF N))
  refine ⟨fun N => if N0 ≤ N then (Kacc + Krej) * (N + 1) ^ E1 else Rs N, fun N x bits => ?_,
    fun N x bits B hN hdec => ?_, Kacc + Krej, N0, fun N hN => ?_⟩
  · dsimp only
    by_cases hN : N0 ≤ N
    · rw [if_pos hN]
      exact (hrej N hN x bits).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
    · rw [if_neg hN, hrejD, rejectCostOf_prefix (W g) (R g) N0 x bits (padF N)]
      have hm : (x, (fun i : Fin (N / 16) => bits.getD i.val false)) ∈
          (Finset.univ : Finset (BitInput N × BitInput (N / 16))) := Finset.mem_univ _
      have h := Finset.le_sup (f := fun p : BitInput N × BitInput (N / 16) =>
        rejectCostOf s g (W g) (R g) N0 p.1 (List.ofFn p.2) (padF N)) hm
      exact h
  · dsimp only
    have hN' : N0 ≤ N := hN
    rw [if_pos hN']
    exact (hacc N hN' x bits B hdec).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · dsimp only
    rw [← hE1, if_pos hN]

end NearCubicGates.Close.Setup
