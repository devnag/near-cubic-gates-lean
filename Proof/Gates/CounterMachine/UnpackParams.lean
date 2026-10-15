import Proof.Gates.CounterMachine.UnpackScript

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length readNatM readNatM_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec NearCubicGates.Close.Counter

variable {ns nr : ℕ} (cap : ℕ)

section Par
variable (IN : Fin (ns + 1)) (Q : Fin 16 ↪ Fin nr)

/-- Rewind a stream by the output counter `Q 15` (scratch `Q 7`, `Q 3`). -/
def rewQ (I : Fin (ns + 1)) : WM ns nr := .seq (copyR (Q 15) (Q 7) (Q 3)) (WM.rewind I (Q 7))

theorem rewQ_spec (I : Fin (ns + 1)) (σ : WState ns nr) (hz : QZero Q σ) (hle : σ.sh I ≤ σ.val (Q 15))
    (hcap : σ.val (Q 15) ≤ cap) : WExec cap (rewQ Q I) σ (σ.seth I 0) (23 * σ.val (Q 15) + 6) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have h7 : σ.val (Q 7) = 0 := hz 7 (by decide)
  have e1 := copyR_spec cap (v := Q 15) (d := Q 7) (t := Q 3) (hQ (by decide)) (hQ (by decide)) (hQ (by decide)) σ
    (hz 3 (by decide)) (by rw [h7]; omega)
  rw [h7, Nat.zero_add] at e1
  have e2 := wrewind_spec cap I (Q 7) (σ.val (Q 15)) (σ.setv (Q 7) (σ.val (Q 15))) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  have e : σ.setv (Q 7) 0 = σ := by rw [← h7, wsetv_same]
  rw [wsetv_setv, e, WState.setv_sh, show σ.sh I - σ.val (Q 15) = 0 by omega]

/-- The parameter fields, first part. -/
def parOps1 (Rk RP E RJ : Fin nr) (PR TMP FA : Fin (ns + 1)) : List (FOp ns nr) :=
  [.skip 6, .read Rk, .skip 3, .read RP, .read E, .copyC PR, .skip 9, .copy 1 TMP, .read RJ, .copyC FA]

def parSegs1 (p : Params) : List (List ℕ) :=
  [[p.n, bitN p.pair, p.W] ++ ratN p.beta, [p.k], [p.T, p.m, p.Dmax], [p.P], [p.e],
    [(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·), [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0,
    [p.M1], [p.J], [p.factors.length] ++ p.factors]

def parOps2 (FA : Fin (ns + 1)) : List (FOp ns nr) := [.copy 1 FA, .skip 1]

def parSegs2 (p : Params) : List (List ℕ) := [[p.A], [p.Lambda]]

theorem paramsN_segs (p : Params) : paramsN p = (parSegs1 p).flatten ++ (parSegs2 p).flatten := by
  simp [paramsN, parSegs1, parSegs2, List.append_assoc]

/-- Unpack the parameters. -/
def unPar (Rk RP E RJ : Fin nr) (PR TMP FA : Fin (ns + 1)) : WM ns nr :=
  .seq (scriptProg IN Q (parOps1 Rk RP E RJ PR TMP FA))
  (.seq (rewQ Q TMP) (.seq (scriptProg TMP Q [.copy 1 FA]) (scriptProg IN Q (parOps2 FA))))

theorem forall2_par1 (Rk RP E RJ : Fin nr) (PR TMP FA : Fin (ns + 1)) (p : Params) (Λ : ℕ)
    (hRd : ∀ v ∈ [p.k, p.P, p.e, p.J, (p.primes.sort (· ≤ ·)).length, p.factors.length], 2 ^ (natBitLength v + 1) ≤ Λ) :
    List.Forall₂ (fun o x => FOp.Seg o x ∧ FOp.ReadOK Λ o x) (parOps1 Rk RP E RJ PR TMP FA) (parSegs1 p) := by
  simp only [parOps1, parSegs1, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨⟨by simp [FOp.Seg, ratN, intN], trivial⟩, ⟨by simp [FOp.Seg], hRd _ (by simp)⟩, ⟨by simp [FOp.Seg], trivial⟩,
    ⟨by simp [FOp.Seg], hRd _ (by simp)⟩, ⟨by simp [FOp.Seg], hRd _ (by simp)⟩,
    ⟨⟨_, rfl⟩, by simpa [FOp.ReadOK] using hRd _ (by simp)⟩, ⟨by simp [FOp.Seg, ratN, intN], trivial⟩,
    ⟨by simp [FOp.Seg], trivial⟩, ⟨by simp [FOp.Seg], hRd _ (by simp)⟩,
    ⟨⟨_, rfl⟩, by simpa [FOp.ReadOK] using hRd _ (by simp)⟩⟩

/-- The state after the first parameter script, explicitly. -/
theorem scriptEff_par1 (Rk RP E RJ : Fin nr) (PR TMP FA : Fin (ns + 1)) (p : Params) (σ : WState ns nr) :
    scriptEff Q (parOps1 Rk RP E RJ PR TMP FA) (parSegs1 p) σ =
      appendO (((appendO (appendO ((((σ.setv Rk p.k).setv RP p.P).setv E p.e)) PR (Q 15)
        (encN (p.primes.sort (· ≤ ·)))) TMP (Q 15) (encN [p.M1])).setv RJ p.J)) FA (Q 15) (encN p.factors) := by
  simp [scriptEff, parOps1, parSegs1, FOp.eff]

/-- **The parameters unpacked.** -/
theorem unPar_spec (Rk RP E RJ : Fin nr) (PR TMP FA : Fin (ns + 1)) (hS : [IN, PR, TMP, FA].Nodup)
    (hR : [Rk, RP, E, RJ].Nodup) (hQR : ∀ i, Q i ∉ [Rk, RP, E, RJ]) (p : Params) (A B : List ℕ) (rest : List Bool)
    (σ : WState ns nr) (hσ : NatAt IN (A ++ paramsN p ++ B) rest σ A.length) (hz : QZero Q σ)
    (h0 : ∀ r ∈ [Rk, RP, E, RJ], σ.val r = 0) (hPR : σ.sh PR = (σ.st PR).length) (hFA : σ.sh FA = (σ.st FA).length)
    (hTMP : σ.st TMP = [] ∧ σ.sh TMP = 0) (Λ : ℕ) (hbits : ∀ y ∈ A ++ paramsN p ++ B, natBitLength y + 2 ≤ Λ)
    (hlen : (A ++ paramsN p ++ B).length ≤ Λ)
    (hRd : ∀ v ∈ [p.k, p.P, p.e, p.J, (p.primes.sort (· ≤ ·)).length, p.factors.length], 2 ^ (natBitLength v + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 10 * (encN (A ++ paramsN p ++ B)).length + σ.val (Q 15) ≤ cap) :
    ∃ τ, WExec cap (unPar IN Q Rk RP E RJ PR TMP FA) σ τ (20000 * (Λ + 1) ^ 2 + 23 * σ.val (Q 15)) ∧
      NatAt IN (A ++ paramsN p ++ B) rest τ (A ++ paramsN p).length ∧ QZero Q τ ∧
      τ.val Rk = p.k ∧ τ.val RP = p.P ∧ τ.val E = p.e ∧ τ.val RJ = p.J ∧
      τ.st PR = σ.st PR ++ encN (p.primes.sort (· ≤ ·)) ∧ τ.sh PR = (τ.st PR).length ∧
      τ.st FA = σ.st FA ++ encN (p.factors ++ [p.M1, p.A]) ∧ τ.sh FA = (τ.st FA).length ∧
      τ.sh TMP = (encN [p.M1]).length ∧
      τ.val (Q 15) ≤ σ.val (Q 15) + 2 * (encN (A ++ paramsN p ++ B)).length ∧
      σ.val (Q 15) + (encN (p.factors ++ [p.M1, p.A])).length ≤ τ.val (Q 15) ∧
      (∀ X, X ∉ [IN, PR, TMP, FA] → τ.st X = σ.st X ∧ τ.sh X = σ.sh X) ∧
      (∀ r, r ∉ [Rk, RP, E, RJ, Q 15] → τ.val r = σ.val r) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hS hR
  obtain ⟨⟨iP, iT, iF⟩, ⟨pT, pF⟩, tF⟩ := hS
  obtain ⟨⟨kP, kE, kJ⟩, ⟨PE, PJ⟩, EJ⟩ := hR
  have qr : ∀ i r, r ∈ [Rk, RP, E, RJ] → Q i ≠ r := fun i r hr h => hQR i (h ▸ hr)
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hseg := paramsN_segs p
  rw [hseg] at hσ hbits hlen hcap ⊢
  have hS2e : (parSegs2 p).flatten = [p.A, p.Lambda] := by simp [parSegs2]
  have hLsum := natWords_sum_le (A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B) Λ (fun y hy => by have := hbits y hy; omega)
  have hencL : (encN (A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B)).length ≤ 2 * ((A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B).length * (2 * Λ + 1)) := by
    rw [encN_length]; omega
  -- 1. the first script
  have e1 := script_spec cap IN Q rest Λ (parOps1 Rk RP E RJ PR TMP FA) (parSegs1 p)
    (forall2_par1 Rk RP E RJ PR TMP FA p Λ hRd) A ((parSegs2 p).flatten ++ B) σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) hz
    (fun r hr => by
      simp only [parOps1, List.flatMap_cons, List.flatMap_nil, FOp.regs, List.append_nil, List.nil_append,
        List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      exact ⟨fun i => qr i r (by simp; tauto), h0 r (by simp; tauto)⟩)
    (by simp [parOps1, FOp.regs, kP, kE, kJ, PE, PJ, EJ])
    (fun Z hZ => by
      simp only [parOps1, List.flatMap_cons, List.flatMap_nil, FOp.strs, List.append_nil, List.nil_append,
        List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hZ
      rcases hZ with rfl | rfl | rfl
      · exact ⟨iP, hPR⟩
      · exact ⟨iT, by rw [hTMP.1, hTMP.2]; rfl⟩
      · exact ⟨iF, hFA⟩)
    (fun y hy => hbits y (by simp only [List.mem_append] at hy ⊢; tauto))
    (by simp only [List.length_append] at hlen ⊢; omega)
    (by have : (encN (A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B))).length = (encN (A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B)).length := by
          simp [List.append_assoc]
        have h2 := encN_le_mid A (parSegs1 p).flatten ((parSegs2 p).flatten ++ B)
        rw [show A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B) = A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h2
        omega)
  rw [scriptEff_par1] at e1
  set σ1 := (appendO (((appendO (appendO (((σ.setv Rk p.k).setv RP p.P).setv E p.e) PR (Q 15)
    (encN (p.primes.sort (· ≤ ·)))) TMP (Q 15) (encN [p.M1])).setv RJ p.J)) FA (Q 15) (encN p.factors)).seth IN
    (encN (A ++ (parSegs1 p).flatten)).length with hσ1
  have v1 : ∀ r, r ∉ [Rk, RP, E, RJ, Q 15] → σ1.val r = σ.val r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hσ1, appendO, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
      Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.2.2.2.2]
  have z1 : QZero Q σ1 := fun i hi => by
    rw [v1 _ (fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h
      · exact qr i Rk (by simp) h
      · exact qr i RP (by simp) h
      · exact qr i E (by simp) h
      · exact qr i RJ (by simp) h
      · exact hi (Q.injective h))]
    exact hz i hi
  have q15_1 : σ1.val (Q 15) = σ.val (Q 15) + (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length +
      (encN p.factors).length := by
    simp [hσ1, appendO, Function.update_of_ne (qr 15 RJ (by simp)), Function.update_of_ne (qr 15 E (by simp)),
      Function.update_of_ne (qr 15 RP (by simp)), Function.update_of_ne (qr 15 Rk (by simp))]
  have hTsh1 : σ1.sh TMP = (encN [p.M1]).length := by
    simp [hσ1, appendO, Function.update_of_ne (Ne.symm iT), Function.update_of_ne tF, Function.update_of_ne (Ne.symm pT),
      hTMP.2]
  have hTst1 : σ1.st TMP = encN [p.M1] := by
    simp [hσ1, appendO, Function.update_of_ne tF, Function.update_of_ne (Ne.symm pT), hTMP.1]
  -- 2. rewind `TMP`
  have e2 := rewQ_spec cap Q TMP σ1 z1 (by rw [hTsh1, q15_1]; omega) (by
    rw [q15_1]
    have h1 := encN_le_mid A (parSegs1 p).flatten ((parSegs2 p).flatten ++ B)
    have h2 : (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length + (encN p.factors).length ≤
        (encN (parSegs1 p).flatten).length := by
      simp only [parSegs1, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
    rw [show A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B) = A ++ ((parSegs1 p).flatten ++
      (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h1
    omega)
  set σ2 := σ1.seth TMP 0 with hσ2
  have hM1 : p.M1 ∈ A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B := by simp [parSegs1]
  -- 3. M₁ from `TMP` to `FA`
  have e3 := script_spec cap TMP Q [] Λ [.copy 1 FA] [[p.M1]]
    (List.Forall₂.cons ⟨by simp [FOp.Seg], trivial⟩ List.Forall₂.nil) [] [] σ2
    ⟨by simp [hσ2, hTst1], by simp [hσ2]; rfl⟩ (fun i hi => by rw [hσ2, WState.seth_val]; exact z1 i hi)
    (by simp [FOp.regs]) (by simp [FOp.regs])
    (fun Z hZ => by
      simp only [List.flatMap_cons, List.flatMap_nil, FOp.strs, List.append_nil, List.mem_singleton] at hZ
      subst hZ
      refine ⟨tF, ?_⟩
      simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm tF), Function.update_of_ne (Ne.symm iF),
        Function.update_of_ne (Ne.symm pF), hFA])
    (fun y hy => by simp at hy; subst hy; exact hbits _ hM1)
    (by have := hbits _ hM1; simp; omega)
    (by rw [hσ2, WState.seth_val, q15_1]
        have h1 := encN_le_mid A (parSegs1 p).flatten ((parSegs2 p).flatten ++ B)
        have h2 : (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length + (encN p.factors).length ≤
            (encN (parSegs1 p).flatten).length := by
          simp only [parSegs1, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
        have h3 : (encN [p.M1]).length ≤ (encN (parSegs1 p).flatten).length := by
          simp only [parSegs1, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
        rw [show A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B) = A ++ ((parSegs1 p).flatten ++
          (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h1
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append]
        omega)
  simp only [scriptEff, FOp.eff, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append] at e3
  set σ3 := (appendO σ2 FA (Q 15) (encN [p.M1])).seth TMP (encN [p.M1]).length with hσ3
  have q15_3 : σ3.val (Q 15) = σ1.val (Q 15) + (encN [p.M1]).length := by simp [hσ3, hσ2, appendO]
  have hst3 : σ3.st IN = σ.st IN := by
    simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne iF, Function.update_of_ne iT, Function.update_of_ne iP]
  have hA : p.A ∈ A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B := by simp [parSegs2]
  -- 4. A, then step over Λ
  have e4 := script_spec cap IN Q rest Λ (parOps2 FA) (parSegs2 p)
    (List.Forall₂.cons ⟨by simp [FOp.Seg], trivial⟩ (List.Forall₂.cons ⟨by simp [FOp.Seg], trivial⟩ List.Forall₂.nil))
    (A ++ (parSegs1 p).flatten) B σ3
    ⟨by rw [hst3, hσ.1]; simp [List.append_assoc],
     by rw [take_prefix]; simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne iF, Function.update_of_ne iT]⟩
    (fun i hi => by simp [hσ3, hσ2, appendO, Function.update_of_ne (hQ hi)]; exact z1 i hi)
    (by simp [parOps2, FOp.regs]) (by simp [parOps2, FOp.regs])
    (fun Z hZ => by
      simp only [parOps2, List.flatMap_cons, List.flatMap_nil, FOp.strs, List.append_nil, List.mem_singleton,
        List.nil_append] at hZ
      subst hZ
      refine ⟨iF, ?_⟩
      simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm tF), Function.update_of_ne (Ne.symm iF),
        Function.update_of_ne (Ne.symm pF), hFA]; omega)
    (fun y hy => hbits y (by simp only [List.mem_append] at hy ⊢; tauto))
    (by simp only [List.length_append] at hlen ⊢; omega)
    (by rw [q15_3, q15_1]
        have h1 := encN_le_mid A (parSegs1 p).flatten ((parSegs2 p).flatten ++ B)
        have h2 : (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length + (encN p.factors).length ≤
            (encN (parSegs1 p).flatten).length := by
          simp only [parSegs1, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
        have h3 := encN_le_mid (A ++ (parSegs1 p).flatten) (parSegs2 p).flatten B
        have h4 : (encN [p.M1]).length ≤ (encN (parSegs1 p).flatten).length := by
          simp only [parSegs1, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
        rw [show A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B) = A ++ ((parSegs1 p).flatten ++
          (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h1
        rw [show A ++ (parSegs1 p).flatten ++ (parSegs2 p).flatten ++ B = A ++ ((parSegs1 p).flatten ++
          (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h3
        rw [show A ++ (parSegs1 p).flatten ++ (parSegs2 p).flatten ++ B = A ++ ((parSegs1 p).flatten ++
          (parSegs2 p).flatten) ++ B by simp [List.append_assoc]]
        omega)
  rw [show scriptEff Q (parOps2 FA) (parSegs2 p) σ3 = appendO σ3 FA (Q 15) (encN [p.A]) by
    simp [scriptEff, parOps2, parSegs2, FOp.eff]] at e4
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hL1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [parOps1, parOps2, List.length_cons, List.length_nil]
    rw [q15_1]
    have h2 : (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length + (encN p.factors).length ≤
        (encN (A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B)).length := by
      have h1 := encN_le_mid A (parSegs1 p).flatten ((parSegs2 p).flatten ++ B)
      rw [show A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B) = A ++ ((parSegs1 p).flatten ++
        (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h1
      have : (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length + (encN p.factors).length ≤
          (encN (parSegs1 p).flatten).length := by
        simp only [parSegs1, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
      omega
    have h3 : (encN (A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B)).length ≤
        2 * ((A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B).length * (2 * Λ + 1)) := hencL
    have h4 : (A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B).length * (2 * Λ + 1) ≤
        Λ * (2 * Λ + 1) := Nat.mul_le_mul_right _ hlen
    have h5 : Λ * (2 * Λ + 1) ≤ 2 * (Λ + 1) ^ 2 := by nlinarith
    omega
  · refine ⟨by simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne iF, Function.update_of_ne iT,
      Function.update_of_ne iP, hσ.1], ?_⟩
    simp only [WState.seth_sh, Function.update_self]
    rw [show A ++ ((parSegs1 p).flatten ++ (parSegs2 p).flatten) ++ B = (A ++ ((parSegs1 p).flatten ++
      (parSegs2 p).flatten)) ++ B by simp, List.take_left]
    simp [List.append_assoc]
  · intro i hi
    simp [hσ3, hσ2, appendO, Function.update_of_ne (hQ hi)]; exact z1 i hi
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (qr 15 Rk (by simp)).symm, Function.update_of_ne kJ,
      Function.update_of_ne kE, Function.update_of_ne kP]
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (qr 15 RP (by simp)).symm, Function.update_of_ne PJ,
      Function.update_of_ne PE]
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (qr 15 E (by simp)).symm, Function.update_of_ne EJ]
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (qr 15 RJ (by simp)).symm]
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm pF), Function.update_of_ne pT,
      Function.update_of_ne (Ne.symm iP), Function.update_of_ne pF]
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm pF), Function.update_of_ne pT,
      Function.update_of_ne (Ne.symm iP), Function.update_of_ne pF, hPR]
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm tF), Function.update_of_ne (Ne.symm pF),
      Function.update_of_ne (Ne.symm iF), encN_append, List.append_assoc]
    rw [← encN_append]; rfl
  · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm tF), Function.update_of_ne (Ne.symm pF),
      Function.update_of_ne (Ne.symm iF), Function.update_of_ne tF, hFA]
    ring
  · simp [hσ3, hσ2, appendO, Function.update_of_ne iT, Function.update_of_ne (Ne.symm tF), Function.update_of_ne tF]
    rw [Function.update_of_ne (Ne.symm iT), Function.update_of_ne tF, Function.update_self]
  · simp only [WState.seth_val, appendO, WState.setv_val, Function.update_self, WState.sets_val]
    rw [q15_3, q15_1]
    have h1 := encN_le_mid A (parSegs1 p).flatten ((parSegs2 p).flatten ++ B)
    rw [show A ++ (parSegs1 p).flatten ++ ((parSegs2 p).flatten ++ B) = A ++ ((parSegs1 p).flatten ++
      (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h1
    have h2 : (encN (p.primes.sort (· ≤ ·))).length + (encN [p.M1]).length + (encN p.factors).length +
        (encN [p.M1]).length + (encN [p.A]).length ≤ 2 * (encN (parSegs1 p).flatten).length +
        (encN (parSegs2 p).flatten).length := by
      simp only [parSegs1, parSegs2, List.flatten_cons, List.flatten_nil, encN_append, List.length_append]; omega
    have h3 := encN_le_mid (A ++ (parSegs1 p).flatten) (parSegs2 p).flatten B
    rw [show A ++ (parSegs1 p).flatten ++ (parSegs2 p).flatten ++ B = A ++ ((parSegs1 p).flatten ++
      (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h3
    have h4 : (encN (A ++ (parSegs1 p).flatten ++ (parSegs2 p).flatten ++ B)).length ≥
        (encN (parSegs1 p).flatten).length + (encN (parSegs2 p).flatten).length := by
      simp only [encN_append, List.length_append]; omega
    rw [show A ++ (parSegs1 p).flatten ++ (parSegs2 p).flatten ++ B = A ++ ((parSegs1 p).flatten ++
      (parSegs2 p).flatten) ++ B by simp [List.append_assoc]] at h4
    omega
  · simp only [WState.seth_val, appendO, WState.setv_val, Function.update_self, WState.sets_val]
    rw [q15_3, q15_1]
    simp only [encN_append, List.length_append]
    rw [show (encN [p.M1, p.A]).length = (encN [p.M1]).length + (encN [p.A]).length by
      rw [show [p.M1, p.A] = [p.M1] ++ [p.A] from rfl, encN_append, List.length_append]]
    omega
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hX
    simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hX.1, Function.update_of_ne hX.2.1,
      Function.update_of_ne hX.2.2.1, Function.update_of_ne hX.2.2.2]
  · intro r hr
    have h15 : r ≠ Q 15 := fun h => hr (by simp [h])
    simp [hσ3, hσ2, appendO, Function.update_of_ne h15]; exact v1 r hr

end Par

end NearCubicGates.Close.CounterMachine
