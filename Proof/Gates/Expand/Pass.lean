import Proof.Gates.Expand.PassV

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp readNatM readNatM_spec)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {ns nr : ℕ}

theorem frame_enc (w : List Bool) : frame w = enc true w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [frame, ih, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc, if_true,
      NearCubicWires.RepairOrdinary.Streaming.marks, List.flatMap_cons,
      List.cons_append, List.nil_append]

theorem frame_formulaWord (r : FormulaReq) : frame (formulaWord r) =
    enc true (natWord r.1) ++ enc true (natWord (toks r.2).length) ++ enc true ((toks r.2).flatMap tokWord) ++
      [false] := by
  rw [frame_enc, formulaWord, listWord]
  simp only [NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, List.append_assoc]

theorem notMem_evR {R : Fin 12 ↪ Fin nr} {X : Fin nr} (h : ∀ j, R j ≠ X) : X ∉ evR R ++ [R 11] := by
  intro hm
  simp only [evR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with ((hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm) | hm) <;> exact h _ hm.symm

section Pass
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

def evalPass (RL RL2 : Fin nr) (hs : List (WMX ns nr)) : WMX ns nr :=
  .seq (.wm (Codec.skipNat true (U 0) (R 7) (R 8)))
    (.seq (.wm (readNatM true (U 0) (R 7) (R 8) (R 11) (R 9) (R 10)))
      (.seq (tokLoop U R hs) (.seq (pop U R) (repK RL RL2 (WMX.bwd (U 0))))))

def evalCost (Wb c Vn N L : ℕ) : ℕ :=
  (20 * natBitLength Vn + 20) + 1 + (((natBitLength N + 2) * (40 * 2 ^ natBitLength N + 40)) + 1 +
    ((N * ((tagCost + 1 + (c + 3 * 7 + 1)) + 4) + 1) + 1 + (popCost Wb + 1 + ((2 * L + 1) * (1 + 8) +
      7 * (2 * L + 1) + 3))))

variable {U R}

theorem evalPass_spec (cap Wb m k t c : ℕ) (A : Alg) (hA : A.Closed m) (hm2 : 2 ≤ m) (hs : List (WMX ns nr))
    (hlen : hs.length = 7) (r : FormulaReq)
    (hh : ∀ tok ∈ toks r.2, HSpec U R cap Wb m k t A (hs.getD (tagOf tok) WMX.skip) tok c)
    (RL RL2 : Fin nr) (hRL : ∀ j, R j ≠ RL) (hRL2 : ∀ j, R j ≠ RL2) (hRR : RL ≠ RL2) (σ : WState ns nr)
    (hE : EvAt U R Wb m k t (frame (formulaWord r)) 0 [] σ) (h11 : σ.val (R 11) = 0)
    (hRLv : σ.val RL = 2 * (formulaWord r).length + 1) (hRL2v : σ.val RL2 = 0)
    (hdepth : m ^ ((toks r.2).length + 2) ≤ 2 ^ Wb) (hcapW : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ ((formulaWord r).length + 4) ≤ cap) :
    Runs cap (evalPass U R RL RL2 hs) σ (evalCost Wb c r.1 (toks r.2).length (formulaWord r).length)
      (fun τ => EvAt U R Wb m k t (frame (formulaWord r)) 0 [] τ ∧ NumOn τ (U 2) Wb (A.eval r.2) ∧
        τ.val (R 11) = 0 ∧ τ.val RL = σ.val RL ∧ τ.val RL2 = 0 ∧
        SameExcept σ τ (evS U) (evR R ++ [R 11])) := by
  set N := (toks r.2).length with hN
  set L := (formulaWord r).length with hL
  have hfw := frame_formulaWord r
  rw [← hN] at hfw
  have hlenV : (natWord r.1).length ≤ L := by
    simp only [hL, formulaWord, listWord, List.length_append]; omega
  have hlenN : (natWord N).length ≤ L := by
    simp only [hL, formulaWord, listWord, List.length_append, ← hN]; omega
  have hnbV : natBitLength r.1 + 1 ≤ L := by
    have := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length r.1; omega
  have hnbN : natBitLength N + 1 ≤ L := by
    have := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length N; omega
  have hLdec : L = (natWord r.1).length + (natWord N).length + ((toks r.2).flatMap tokWord).length := by
    simp only [hL, formulaWord, listWord, List.length_append, ← hN]; omega
  have hNL : N ≤ L := by
    have : N ≤ ((toks r.2).flatMap tokWord).length := by
      rw [hN, List.length_flatMap]
      have : ∀ t ∈ toks r.2, 1 ≤ (tokWord t).length := by
        intro t _; rw [tokWord_eq, List.length_append, natWord_len]; omega
      calc (toks r.2).length = ((toks r.2).map fun _ => 1).sum := by simp
        _ ≤ ((toks r.2).map fun t => (tokWord t).length).sum := List.sum_le_sum (fun t ht => this t ht)
    omega
  have h4L : 4 * L + 2 + 2 ^ 4 + N ≤ cap := by
    have h1 : L < 2 ^ L := Nat.lt_two_pow_self
    have h2 : 2 ^ (L + 4) = 2 ^ L * 16 := by rw [pow_add]; norm_num
    omega
  have hpowL : 2 ^ L ≤ cap := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcapL
  have hLcap : L + 4 ≤ cap := le_trans (Nat.lt_two_pow_self).le hcapL
  -- skip `natWord V`
  have h1 := Codec.skipNat_spec cap true (U 0) (R 7) (R 8) (rN R (by decide)) r.1 []
    (enc true (natWord N) ++ enc true ((toks r.2).flatMap tokWord) ++ [false]) σ
    (by rw [hE.inp, hfw]; simp only [List.nil_append, List.append_assoc]) (by rw [hE.hd]; rfl)
    (hE.ev.reg 7) (hE.ev.reg 8) (by omega)
  set σ1 := σ.seth (U 0) ([].length + stp true * (natWord r.1).length) with hσ1
  -- read the token count into `R 11`
  have h2 := readNatM_spec (cap := cap) true (U 0) (R 7) (R 8) (R 11) (R 9) (R 10) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) N (enc true (natWord r.1))
    (enc true ((toks r.2).flatMap tokWord) ++ [false]) σ1
    (by rw [hσ1]; simp only [WState.seth_st]; rw [hE.inp, hfw]; simp only [List.append_assoc])
    (by rw [hσ1]; simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length, stp])
    (by rw [hσ1]; simpa using hE.ev.reg 7) (by rw [hσ1]; simpa using hE.ev.reg 8)
    (by rw [hσ1]; simpa using hE.ev.reg 9) (by rw [hσ1]; simpa using hE.ev.reg 10)
    (by
      rw [hσ1]; simp only [WState.seth_val, h11, zero_add]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcapL)
  set P0 := enc true (natWord r.1) ++ enc true (natWord N) with hP0
  have hP0len : P0.length = 2 * (natWord r.1).length + 2 * (natWord N).length := by
    simp [hP0, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length, stp]
  set σ2 := (σ1.seth (U 0) ((enc true (natWord r.1)).length + stp true * (natWord N).length)).setv (R 11)
    (σ1.val (R 11) + N) with hσ2
  have hE2 : EvAt U R Wb m k t (P0 ++ enc true ((toks r.2).flatMap tokWord) ++ [false]) P0.length [] σ2 := by
    refine ⟨(hE.ev.seth _).seth _ |>.setv 11 rfl _, ?_, ?_, ?_⟩
    · rw [hσ2, hσ1]; simp only [WState.setv_st, WState.seth_st]; rw [hE.inp, hfw, hP0]
    · rw [hσ2, hσ1, hP0len]
      simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length, stp]
    · have := hE.stk
      exact ⟨by rw [hσ2, hσ1]; simpa using this.1, by
        rw [hσ2, hσ1]; simp only [WState.setv_sh, WState.seth_sh]
        rw [Function.update_of_ne (uN U (by decide)), Function.update_of_ne (uN U (by decide))]; exact this.2⟩
  have h2N : σ2.val (R 11) = N := by rw [hσ2, hσ1]; simp [h11]
  -- the token loop
  have h3 := tokLoop_spec cap Wb m k t c A hA hs hlen (toks r.2) hh P0 [false] σ2 hE2 h2N hdepth
    (by omega)
  refine Runs.seqE (WXExec.wm h1) (Runs.seqE (WXExec.wm h2) (Runs.seq h3 (fun τ3 ⟨⟨hE3, hF3⟩, hK3⟩ => ?_)))
  rw [A.foldl_toks_nil] at hE3
  -- pop the result
  have hm0 : 0 < m := by omega
  have hres : A.eval r.2 < m := A.eval_lt hA r.2
  have hpop := pop_spec cap Wb m k t τ3 hE3.ev (A.eval r.2) [] hE3.stk hres
    (by
      have := senc_lt m [A.eval r.2] (by simpa using hres)
      refine lt_of_lt_of_le this (le_trans ?_ hdepth)
      exact Nat.pow_le_pow_right hm0 (by simp))
    (by
      have : m * m ≤ 2 ^ Wb := le_trans (by rw [← pow_two]; exact Nat.pow_le_pow_right hm0 (by omega)) hdepth
      nlinarith) hcapW
  refine Runs.seq hpop (fun τ4 ⟨hE4, hS4, hA4, hF4⟩ => ?_)
  -- rewind the input
  have hpos : τ4.sh (U 0) ≤ 2 * L + 1 := by
    rw [hF4.sh (by simp [uN U])]
    rw [hE3.hd, hP0len]
    omega
  have hRLτ4 : τ4.val RL = 2 * L + 1 := by
    rw [hF4.val (by simp), hF3.val (notMem_evR hRL), hσ2, hσ1]
    simp [Function.update_of_ne (hRL 11).symm, hRLv]
  have hRL2τ4 : τ4.val RL2 = 0 := by
    rw [hF4.val (by simp), hF3.val (notMem_evR hRL2), hσ2, hσ1]
    simp [Function.update_of_ne (hRL2 11).symm, hRL2v]
  have hrw := Runs.repE (cap := cap) (body := WMX.bwd (U 0)) hRR 1 (2 * L + 1)
    (fun j => τ4.seth (U 0) (τ4.sh (U 0) - j)) (by omega) (fun j => by simp) (fun j => by simp)
    (fun j _ v1 v2 => by
      refine (WXExec.bwd cap (U 0) _).cast cap ?_ le_rfl
      apply WState.eq
      · funext i; by_cases hi : i = U 0
        · subst hi; simp <;> omega
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl
      · rfl) (by simp [hRLτ4]) (by simp [hRL2τ4])
  have e0 : τ4.seth (U 0) (τ4.sh (U 0) - 0) = τ4 := by
    apply WState.eq
    · funext i; by_cases hi : i = U 0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  rw [e0, show τ4.sh (U 0) - (2 * L + 1) = 0 by omega] at hrw
  refine ⟨_, hrw, ⟨hE4.seth 0, ?_, by simp, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; rw [hF4.st (by simp [uN U]), hE3.inp, hfw, hP0]
  · exact ⟨by simpa using hS4.1, by simp [Function.update_of_ne (uN U (by decide : (1 : Fin 10) ≠ 0)), hS4.2]⟩
  · exact ⟨by simpa using hA4.1, by simp [Function.update_of_ne (uN U (by decide : (2 : Fin 10) ≠ 0)), hA4.2]⟩
  · simp only [WState.seth_val]; rw [hF4.val (by simp)]; exact hK3
  · simp only [WState.seth_val]; rw [hRLτ4, hRLv]
  · simp only [WState.seth_val]; exact hRL2τ4
  · have f1 : SameExcept σ σ2 (evS U) (evR R ++ [R 11]) := by
      rw [hσ2, hσ1]
      exact SameExcept.trans (SameExcept.trans (sameExcept_seth σ (by simp [evS]) _) (sameExcept_seth _ (by simp [evS]) _))
        (sameExcept_setv _ (by simp) _)
    have f4 : SameExcept τ3 τ4 (evS U) (evR R ++ [R 11]) :=
      hF4.weaken (fun x hx => by simp [evS] at hx ⊢; rcases hx with h | h | h | h <;> simp [h]) (fun _ h => by simp at h)
    exact SameExcept.trans (SameExcept.trans (SameExcept.trans f1 hF3) f4) (sameExcept_seth _ (by simp [evS]) _)

end Pass

end NearCubicGates.Close.Expand
