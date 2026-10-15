import Proof.Gates.CounterMachine.UnpackCircuit

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
open NearCubicGates.Close.Codec

variable {ns nr : ℕ} (cap : ℕ)

/-- `r := r + m` by `m` increments. -/
def incN (r : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | m + 1 => .seq (incN r m) (.inc r)

theorem incN_spec (r : Fin nr) : ∀ (m : ℕ) (σ : WState ns nr), σ.val r + m ≤ cap →
    WExec cap (incN r m) σ (σ.setv r (σ.val r + m)) (4 * m)
  | 0, σ, _ => by simpa [incN, wsetv_same] using WExec.skip (cap := cap) σ
  | m + 1, σ, h => by
    have e1 := incN_spec r m σ (by omega)
    have e2 := WExec.inc (cap := cap) r (σ.setv r (σ.val r + m)) (by simp; omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
    simp [wsetv_setv]; ring_nf

/-- A field operation. -/
inductive FOp (ns nr : ℕ) where
  | skip (m : ℕ)
  | read (r : Fin nr)
  | copy (m : ℕ) (Z : Fin (ns + 1))
  | skipC
  | copyC (Z : Fin (ns + 1))
  | copyI (Z : Fin (ns + 1))

section Script
variable (IN : Fin (ns + 1)) (Q : Fin 16 ↪ Fin nr)

def FOp.prog : FOp ns nr → WM ns nr
  | .skip m => .seq (incN (Q 6) m) (listLoop (Q 6) (skipNat true IN (Q 0) (Q 1)))
  | .read r => readNatM true IN (Q 0) (Q 1) r (Q 2) (Q 3)
  | .copy m Z => .seq (incN (Q 4) m) (listLoop (Q 4) (copyNat true IN Z (Rq Q)))
  | .skipC => .seq (readNatM true IN (Q 0) (Q 1) (Q 6) (Q 2) (Q 3)) (listLoop (Q 6) (skipNat true IN (Q 0) (Q 1)))
  | .copyC Z => .seq (readNatM true IN (Q 0) (Q 1) (Q 4) (Q 2) (Q 3)) (listLoop (Q 4) (copyNat true IN Z (Rq Q)))
  | .copyI Z => .seq (readNatM true IN (Q 0) (Q 1) (Q 5) (Q 2) (Q 3)) (.seq (copyR (Q 5) (Q 4) (Q 3))
      (.seq (copyR (Q 5) (Q 4) (Q 3)) (.seq (WM.clear (Q 5)) (listLoop (Q 4) (copyNat true IN Z (Rq Q))))))

def scriptProg : List (FOp ns nr) → WM ns nr
  | [] => .skip
  | o :: os => .seq (o.prog IN Q) (scriptProg os)

/-- The segment an operation consumes. -/
def FOp.Seg : FOp ns nr → List ℕ → Prop
  | .skip m, xs => xs.length = m
  | .read _, xs => xs.length = 1
  | .copy m _, xs => xs.length = m
  | .skipC, xs => ∃ ys, xs = [ys.length] ++ ys
  | .copyC _, xs => ∃ ys, xs = [ys.length] ++ ys
  | .copyI _, xs => ∃ zs : List ℤ, xs = [zs.length] ++ zs.flatMap intN

/-- The read fields are small enough for unary registers. -/
def FOp.ReadOK (Λ : ℕ) : FOp ns nr → List ℕ → Prop
  | .skip _, _ => True
  | .copy _ _, _ => True
  | _, x => 2 ^ (natBitLength (x.headD 0) + 1) ≤ Λ

/-- Its effect besides the input head. -/
def FOp.eff : FOp ns nr → List ℕ → WState ns nr → WState ns nr
  | .skip _, _, σ => σ
  | .read r, xs, σ => σ.setv r (xs.headD 0)
  | .copy _ Z, xs, σ => appendO σ Z (Q 15) (encN xs)
  | .skipC, _, σ => σ
  | .copyC Z, xs, σ => appendO σ Z (Q 15) (encN xs.tail)
  | .copyI Z, xs, σ => appendO σ Z (Q 15) (encN xs.tail)

def scriptEff : List (FOp ns nr) → List (List ℕ) → WState ns nr → WState ns nr
  | o :: os, x :: xs, σ => scriptEff os xs (o.eff Q x σ)
  | _, _, σ => σ

/-- The registers an operation writes, the streams it appends to. -/
def FOp.regs : FOp ns nr → List (Fin nr)
  | .read r => [r]
  | _ => []

def FOp.strs : FOp ns nr → List (Fin (ns + 1))
  | .copy _ Z => [Z]
  | .copyC Z => [Z]
  | .copyI Z => [Z]
  | _ => []

theorem nd_read (r : Fin nr) (hr : ∀ i, Q i ≠ r) : [Q 0, Q 1, r, Q 2, Q 3].Nodup := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true]
  exact ⟨⟨hQ (by decide), hr 0, hQ (by decide), hQ (by decide)⟩, ⟨hr 1, hQ (by decide), hQ (by decide)⟩,
    ⟨(hr 2).symm, (hr 3).symm⟩, hQ (by decide)⟩

/-- **One field operation.** -/
theorem FOp.prog_spec (o : FOp ns nr) (x A B : List ℕ) (hx : o.Seg x) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ x ++ B) rest σ A.length) (hz : QZero Q σ)
    (hr : ∀ r ∈ o.regs, (∀ i, Q i ≠ r) ∧ σ.val r = 0) (hs : ∀ Z ∈ o.strs, IN ≠ Z ∧ σ.sh Z = (σ.st Z).length)
    (Λ : ℕ) (hfit : ∀ y ∈ A ++ x ++ B, natBitLength y + 2 ≤ Λ) (hrd : o.ReadOK Λ x)
    (hlen : (A ++ x ++ B).length ≤ Λ) (hcap : 20 * (Λ + 1) ^ 2 + 4 * (encN (A ++ x ++ B)).length + σ.val (Q 15) ≤ cap) :
    WExec cap (o.prog IN Q) σ ((o.eff Q x σ).seth IN (encN (A ++ x)).length) (400 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hΛcap : Λ + 1 ≤ cap := by nlinarith
  have hfit' := fit_cap cap hfit (by omega)
  have hlen' := hlen
  simp only [List.length_append] at hlen'
  have hL1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hLL : Λ * Λ + 2 * Λ + 1 = (Λ + 1) ^ 2 := by ring
  cases o with
  | skip m =>
    simp only [FOp.Seg] at hx
    have e1 := incN_spec cap (Q 6) m σ (by rw [hz' 6 (by decide)]; omega)
    rw [hz' 6 (by decide), Nat.zero_add] at e1
    have e2 := skipF_spec cap IN rest (Q 6) (Q 0) (Q 1) (hQ (by decide)) (hQ (by decide)) (hQ (by decide)) A x B
      (σ.setv (Q 6) m) hσ (by simp [hx]) (by simp [Function.update_of_ne (hQ (show (0 : Fin 16) ≠ 6 by decide))]; exact hz' 0 (by decide))
      (by simp [Function.update_of_ne (hQ (show (1 : Fin 16) ≠ 6 by decide))]; exact hz' 1 (by decide)) hfit' (by omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · rw [wsetv_setv, show (0 : ℕ) = σ.val (Q 6) from (hz' 6 (by decide)).symm, wsetv_same]; rfl
    · have c := skipSum_le x Λ (fun y hy => by have := hfit y (by simp [hy]); omega)
      have : x.length * (20 * Λ + 24) ≤ 20 * (Λ * Λ) + 24 * Λ := by nlinarith
      generalize Λ * Λ = P at *; omega
  | read r =>
    simp only [FOp.Seg] at hx
    obtain ⟨v, rfl⟩ : ∃ v, x = [v] := by
      match x, hx with
      | [v], _ => exact ⟨v, rfl⟩
    simp only [FOp.ReadOK, List.headD_cons] at hrd
    have hrr := hr r (by simp [FOp.regs])
    have e := readF_spec cap IN rest (Q 0) (Q 1) r (Q 2) (Q 3) (nd_read Q r hrr.1) A B v σ hσ (hz' 0 (by decide))
      (hz' 1 (by decide)) (hz' 2 (by decide)) (hz' 3 (by decide))
      (by rw [hrr.2]; have := hrd; omega)
    rw [hrr.2, Nat.zero_add] at e
    refine WExec.cast cap e ?_ ?_
    · simp [FOp.eff, wseth_setv]
    · have := readCost_le v Λ (hfit v (by simp)) hrd
      have : (natBitLength v + 2) * (40 * 2 ^ natBitLength v + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by nlinarith
      generalize Λ * Λ = P at *; omega
  | copy m Z =>
    simp only [FOp.Seg] at hx
    have hZ := hs Z (by simp [FOp.strs])
    have e1 := incN_spec cap (Q 4) m σ (by rw [hz' 4 (by decide)]; omega)
    rw [hz' 4 (by decide), Nat.zero_add] at e1
    have e2 := copyF_spec cap IN rest Z hZ.1 (Rq Q) (Q 4) (fun j => hRq_ne Q j 4 (by decide)) A x B (σ.setv (Q 4) m)
      hσ (by simp [hx])
      (by rw [show Rq Q 1 = Q 9 from rfl]; simp [Function.update_of_ne (hQ (show (9 : Fin 16) ≠ 4 by decide))]; exact hz' 9 (by decide))
      (by rw [show Rq Q 2 = Q 10 from rfl]; simp [Function.update_of_ne (hQ (show (10 : Fin 16) ≠ 4 by decide))]; exact hz' 10 (by decide))
      (by simp; exact hZ.2)
      (by rw [show Rq Q 7 = Q 15 from rfl]; simp [Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide))]
          have := hcap; simp only [List.append_assoc] at this; omega) (by omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · simp only [FOp.eff, show Rq Q 7 = Q 15 from rfl]
      apply WState.eq
      · simp [appendO]
      · simp [appendO]
      · funext q; by_cases q4 : q = Q 4
        · subst q4; simp [Function.update_of_ne (hQ (show (4 : Fin 16) ≠ 15 by decide))]; exact (hz' 4 (by decide)).symm
        · by_cases q15 : q = Q 15
          · subst q15; simp [Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide))]
          · simp [Function.update_of_ne q4, Function.update_of_ne q15]
      · simp [appendO]
    · have c := copySum_le x Λ (fun y hy => by have := hfit y (by simp [hy]); omega)
      have : x.length * (120 * Λ + 124) ≤ 120 * (Λ * Λ) + 124 * Λ := by nlinarith
      generalize Λ * Λ = P at *; omega
  | skipC =>
    obtain ⟨ys, rfl⟩ := hx
    simp only [FOp.ReadOK, List.singleton_append, List.headD_cons] at hrd
    have e1 := readF_spec cap IN rest (Q 0) (Q 1) (Q 6) (Q 2) (Q 3)
      (by have : [Q 0, Q 1, Q 6, Q 2, Q 3] = [0, 1, 6, 2, 3].map Q := rfl
          rw [this]; exact List.Nodup.map Q.injective (by decide)) A (ys ++ B) ys.length σ
      (natAt_congr IN rest (by simp [List.append_assoc]) hσ) (hz' 0 (by decide)) (hz' 1 (by decide))
      (hz' 2 (by decide)) (hz' 3 (by decide)) (by rw [hz' 6 (by decide)]; have := hrd; omega)
    rw [hz' 6 (by decide), Nat.zero_add] at e1
    have e2 := skipF_spec cap IN rest (Q 6) (Q 0) (Q 1) (hQ (by decide)) (hQ (by decide)) (hQ (by decide))
      (A ++ [ys.length]) ys B ((σ.seth IN (encN (A ++ [ys.length])).length).setv (Q 6) ys.length)
      ⟨by simp only [WState.setv_st, WState.seth_st]; rw [hσ.1]; simp [List.append_assoc],
       by simp only [WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩ (by simp)
      (by simp [Function.update_of_ne (hQ (show (0 : Fin 16) ≠ 6 by decide))]; exact hz' 0 (by decide))
      (by simp [Function.update_of_ne (hQ (show (1 : Fin 16) ≠ 6 by decide))]; exact hz' 1 (by decide))
      (fun y hy => hfit' y (by simp only [List.mem_append, List.mem_singleton] at hy ⊢; tauto)) (by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · simp only [FOp.eff, wsetv_setv, wseth_setv, wseth_seth, List.append_assoc]
      rw [show (0 : ℕ) = σ.val (Q 6) from (hz' 6 (by decide)).symm, wsetv_same]
    · have r := readCost_le ys.length Λ (hfit _ (by simp)) hrd
      have c := skipSum_le ys Λ (fun y hy => by have := hfit y (by simp [hy]); omega)
      have : ys.length * (20 * Λ + 24) ≤ 20 * (Λ * Λ) + 24 * Λ := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; nlinarith
      have : (natBitLength ys.length + 2) * (40 * 2 ^ natBitLength ys.length + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by
        nlinarith
      clear r; generalize Λ * Λ = P at *; omega
  | copyC Z =>
    obtain ⟨ys, rfl⟩ := hx
    simp only [FOp.ReadOK, List.singleton_append, List.headD_cons] at hrd
    have hZ := hs Z (by simp [FOp.strs])
    have e1 := readF_spec cap IN rest (Q 0) (Q 1) (Q 4) (Q 2) (Q 3)
      (by have : [Q 0, Q 1, Q 4, Q 2, Q 3] = [0, 1, 4, 2, 3].map Q := rfl
          rw [this]; exact List.Nodup.map Q.injective (by decide)) A (ys ++ B) ys.length σ
      (natAt_congr IN rest (by simp [List.append_assoc]) hσ) (hz' 0 (by decide)) (hz' 1 (by decide))
      (hz' 2 (by decide)) (hz' 3 (by decide)) (by rw [hz' 4 (by decide)]; have := hrd; omega)
    rw [hz' 4 (by decide), Nat.zero_add] at e1
    have e2 := copyF_spec cap IN rest Z hZ.1 (Rq Q) (Q 4) (fun j => hRq_ne Q j 4 (by decide)) (A ++ [ys.length]) ys B
      ((σ.seth IN (encN (A ++ [ys.length])).length).setv (Q 4) ys.length)
      ⟨by simp only [WState.setv_st, WState.seth_st]; rw [hσ.1]; simp [List.append_assoc],
       by simp only [WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩ (by simp)
      (by rw [show Rq Q 1 = Q 9 from rfl]; simp [Function.update_of_ne (hQ (show (9 : Fin 16) ≠ 4 by decide))]; exact hz' 9 (by decide))
      (by rw [show Rq Q 2 = Q 10 from rfl]; simp [Function.update_of_ne (hQ (show (10 : Fin 16) ≠ 4 by decide))]; exact hz' 10 (by decide))
      (by simp [Function.update_of_ne (Ne.symm hZ.1)]; exact hZ.2)
      (by rw [show Rq Q 7 = Q 15 from rfl]
          simp only [WState.setv_val, WState.seth_val, Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide))]
          have := hcap
          rw [show A ++ ([ys.length] ++ ys) ++ B = A ++ [ys.length] ++ ys ++ B by simp] at this
          omega) (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · simp only [FOp.eff, show Rq Q 7 = Q 15 from rfl, List.tail_append_of_ne_nil, List.cons_append,
        List.singleton_append, List.tail_cons]
      apply WState.eq
      · funext j; by_cases jI : j = IN
        · subst jI; simp [appendO, Function.update_of_ne hZ.1, List.append_assoc]
        · by_cases jZ : j = Z
          · subst jZ; simp [appendO, Function.update_of_ne (Ne.symm hZ.1)]
          · simp [appendO, Function.update_of_ne jI, Function.update_of_ne jZ]
      · simp [appendO, Function.update_of_ne hZ.1]
      · funext q; by_cases q4 : q = Q 4
        · subst q4; simp [Function.update_of_ne (hQ (show (4 : Fin 16) ≠ 15 by decide))]; exact (hz' 4 (by decide)).symm
        · by_cases q15 : q = Q 15
          · subst q15; simp [Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide))]
          · simp [Function.update_of_ne q4, Function.update_of_ne q15]
      · simp [appendO]
    · have r := readCost_le ys.length Λ (hfit _ (by simp)) hrd
      have c := copySum_le ys Λ (fun y hy => by have := hfit y (by simp [hy]); omega)
      have : ys.length * (120 * Λ + 124) ≤ 120 * (Λ * Λ) + 124 * Λ := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; nlinarith
      have : (natBitLength ys.length + 2) * (40 * 2 ^ natBitLength ys.length + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by
        nlinarith
      clear r; generalize Λ * Λ = P at *; omega

  | copyI Z =>
    obtain ⟨zs, rfl⟩ := hx
    simp only [FOp.ReadOK, List.singleton_append, List.headD_cons] at hrd
    have hZ := hs Z (by simp [FOp.strs])
    have hzl := flatMap_intN_length zs
    have e1 := readF_spec cap IN rest (Q 0) (Q 1) (Q 5) (Q 2) (Q 3)
      (by have : [Q 0, Q 1, Q 5, Q 2, Q 3] = [0, 1, 5, 2, 3].map Q := rfl
          rw [this]; exact List.Nodup.map Q.injective (by decide)) A (zs.flatMap intN ++ B) zs.length σ
      (natAt_congr IN rest (by simp [List.append_assoc]) hσ) (hz' 0 (by decide)) (hz' 1 (by decide))
      (hz' 2 (by decide)) (hz' 3 (by decide)) (by rw [hz' 5 (by decide)]; have := hrd; omega)
    rw [hz' 5 (by decide), Nat.zero_add] at e1
    set σ1 := (σ.seth IN (encN (A ++ [zs.length])).length).setv (Q 5) zs.length with hσ1
    have v1 : ∀ i : Fin 16, i ≠ 5 → σ1.val (Q i) = σ.val (Q i) := fun i hi => by
      simp [hσ1, Function.update_of_ne (hQ hi)]
    have e2 := copyR_spec cap (v := Q 5) (d := Q 4) (t := Q 3) (hQ (by decide)) (hQ (by decide)) (hQ (by decide)) σ1
      (by rw [v1 3 (by decide)]; exact hz' 3 (by decide))
      (by rw [v1 4 (by decide), hz' 4 (by decide)]; simp [hσ1]
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega)
    rw [v1 4 (by decide), hz' 4 (by decide), Nat.zero_add, show σ1.val (Q 5) = zs.length by simp [hσ1]] at e2
    have e3 := copyR_spec cap (v := Q 5) (d := Q 4) (t := Q 3) (hQ (by decide)) (hQ (by decide)) (hQ (by decide))
      (σ1.setv (Q 4) zs.length)
      (by simp [Function.update_of_ne (hQ (show (3 : Fin 16) ≠ 4 by decide))]; rw [v1 3 (by decide)]
          exact hz' 3 (by decide))
      (by simp [Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)), hσ1]
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega)
    simp only [WState.setv_val, Function.update_self, Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)),
      wsetv_setv] at e3
    rw [show σ1.val (Q 5) = zs.length by simp [hσ1]] at e3
    have e4 := wclear_spec cap (Q 5) zs.length (σ1.setv (Q 4) (zs.length + zs.length))
      (by simp [Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)), hσ1])
      (by simp [Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)), hσ1]
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega)
    set σ4 := (σ1.setv (Q 4) (zs.length + zs.length)).setv (Q 5) 0 with hσ4
    have v4 : ∀ i : Fin 16, i ≠ 4 → σ4.val (Q i) = σ.val (Q i) := fun i hi => by
      by_cases i5 : i = 5
      · subst i5; simp [hσ4]; exact (hz' 5 (by decide)).symm
      · simp [hσ4, Function.update_of_ne (hQ i5), Function.update_of_ne (hQ hi)]; exact v1 i i5
    have e5 := copyF_spec cap IN rest Z hZ.1 (Rq Q) (Q 4) (fun j => hRq_ne Q j 4 (by decide)) (A ++ [zs.length])
      (zs.flatMap intN) B σ4
      ⟨by simp only [hσ4, hσ1, WState.setv_st, WState.seth_st]; rw [hσ.1]; simp [List.append_assoc],
       by simp only [hσ4, hσ1, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
      (by simp [hσ4, Function.update_of_ne (hQ (show (4 : Fin 16) ≠ 5 by decide)), hzl]; ring)
      (by rw [show Rq Q 1 = Q 9 from rfl, v4 9 (by decide)]; exact hz' 9 (by decide))
      (by rw [show Rq Q 2 = Q 10 from rfl, v4 10 (by decide)]; exact hz' 10 (by decide))
      (by simp [hσ4, hσ1, Function.update_of_ne (Ne.symm hZ.1)]; exact hZ.2)
      (by rw [show Rq Q 7 = Q 15 from rfl, v4 15 (by decide)]
          have := hcap
          rw [show A ++ ([zs.length] ++ zs.flatMap intN) ++ B = A ++ [zs.length] ++ zs.flatMap intN ++ B by simp] at this
          omega) (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
    · simp only [FOp.eff, show Rq Q 7 = Q 15 from rfl, List.cons_append, List.singleton_append, List.tail_cons]
      apply WState.eq
      · funext j; by_cases jI : j = IN
        · subst jI; simp [appendO, Function.update_of_ne hZ.1, List.append_assoc]
        · by_cases jZ : j = Z
          · subst jZ; simp [hσ4, hσ1, appendO, Function.update_of_ne (Ne.symm hZ.1)]
          · simp [hσ4, hσ1, appendO, Function.update_of_ne jI, Function.update_of_ne jZ]
      · simp [hσ4, hσ1, appendO, Function.update_of_ne hZ.1]
      · funext q; by_cases q4 : q = Q 4
        · subst q4; simp [Function.update_of_ne (hQ (show (4 : Fin 16) ≠ 15 by decide))]; exact (hz' 4 (by decide)).symm
        · by_cases q15 : q = Q 15
          · subst q15
            simp [hσ4, hσ1, Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide)),
              Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 5 by decide))]
          · by_cases q5 : q = Q 5
            · subst q5; simp [hσ4, Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)),
                Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 15 by decide))]; exact (hz' 5 (by decide)).symm
            · simp [hσ4, hσ1, Function.update_of_ne q4, Function.update_of_ne q15, Function.update_of_ne q5]
      · simp [hσ4, hσ1, appendO]
    · have r := readCost_le zs.length Λ (hfit _ (by simp)) hrd
      have c := copySum_le (zs.flatMap intN) Λ (fun y hy => by have := hfit y (by simp [hy]); omega)
      have hzs : zs.length ≤ Λ := by simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; omega
      have : (zs.flatMap intN).length * (120 * Λ + 124) ≤ 120 * (Λ * Λ) + 124 * Λ := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen'; nlinarith
      have : (natBitLength zs.length + 2) * (40 * 2 ^ natBitLength zs.length + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by
        nlinarith
      have : zs.length * Λ ≤ Λ * Λ := Nat.mul_le_mul_right _ hzs
      clear r; generalize Λ * Λ = P at *; omega

theorem FOp.eff_seth (o : FOp ns nr) (x : List ℕ) (σ : WState ns nr) (X : Fin (ns + 1)) (hX : ∀ Z ∈ o.strs, X ≠ Z)
    (p : ℕ) : o.eff Q x (σ.seth X p) = (o.eff Q x σ).seth X p := by
  cases o with
  | skip m => rfl
  | read r => rfl
  | copy m Z =>
    have hZ := hX Z (by simp [FOp.strs])
    simp only [FOp.eff]
    apply WState.eq
    · funext j; by_cases jX : j = X
      · subst jX; simp [appendO, Function.update_of_ne hZ]
      · by_cases jZ : j = Z
        · subst jZ; simp [appendO, Function.update_of_ne (Ne.symm hZ)]
        · simp [appendO, Function.update_of_ne jX, Function.update_of_ne jZ]
    · simp [appendO]
    · simp [appendO]
    · simp [appendO]
  | skipC => rfl
  | copyC Z =>
    have hZ := hX Z (by simp [FOp.strs])
    simp only [FOp.eff]
    apply WState.eq
    · funext j; by_cases jX : j = X
      · subst jX; simp [appendO, Function.update_of_ne hZ]
      · by_cases jZ : j = Z
        · subst jZ; simp [appendO, Function.update_of_ne (Ne.symm hZ)]
        · simp [appendO, Function.update_of_ne jX, Function.update_of_ne jZ]
    · simp [appendO]
    · simp [appendO]
    · simp [appendO]
  | copyI Z =>
    have hZ := hX Z (by simp [FOp.strs])
    simp only [FOp.eff]
    apply WState.eq
    · funext j; by_cases jX : j = X
      · subst jX; simp [appendO, Function.update_of_ne hZ]
      · by_cases jZ : j = Z
        · subst jZ; simp [appendO, Function.update_of_ne (Ne.symm hZ)]
        · simp [appendO, Function.update_of_ne jX, Function.update_of_ne jZ]
    · simp [appendO]
    · simp [appendO]
    · simp [appendO]

theorem FOp.eff_st_ne (o : FOp ns nr) (x : List ℕ) (σ : WState ns nr) (X : Fin (ns + 1)) (hX : ∀ Z ∈ o.strs, X ≠ Z) :
    (o.eff Q x σ).st X = σ.st X ∧ (o.eff Q x σ).sh X = σ.sh X := by
  cases o with
  | skip m => exact ⟨rfl, rfl⟩
  | read r => exact ⟨rfl, rfl⟩
  | copy m Z => simp [FOp.eff, appendO, Function.update_of_ne (hX Z (by simp [FOp.strs]))]
  | skipC => exact ⟨rfl, rfl⟩
  | copyC Z => simp [FOp.eff, appendO, Function.update_of_ne (hX Z (by simp [FOp.strs]))]
  | copyI Z => simp [FOp.eff, appendO, Function.update_of_ne (hX Z (by simp [FOp.strs]))]

theorem FOp.eff_val_ne (o : FOp ns nr) (x : List ℕ) (σ : WState ns nr) (r : Fin nr) (hr : r ∉ o.regs)
    (h15 : r ≠ Q 15) : (o.eff Q x σ).val r = σ.val r := by
  cases o with
  | skip m => rfl
  | read q =>
    have hq : r ≠ q := fun h => hr (by simp [FOp.regs, h])
    simp [FOp.eff, Function.update_of_ne hq]
  | copy m Z => simp [FOp.eff, appendO, Function.update_of_ne h15]
  | skipC => rfl
  | copyC Z => simp [FOp.eff, appendO, Function.update_of_ne h15]
  | copyI Z => simp [FOp.eff, appendO, Function.update_of_ne h15]

theorem FOp.eff_15 (o : FOp ns nr) (x : List ℕ) (σ : WState ns nr) (hr : Q 15 ∉ o.regs) :
    (o.eff Q x σ).val (Q 15) ≤ σ.val (Q 15) + (encN x).length := by
  cases o with
  | skip m => simp [FOp.eff]
  | read q =>
    have hq : Q 15 ≠ q := fun h => hr (by simp [FOp.regs, h])
    simp [FOp.eff, Function.update_of_ne hq]
  | copy m Z => simp [FOp.eff, appendO]
  | skipC => simp [FOp.eff]
  | copyC Z =>
    simp only [FOp.eff, appendO, WState.setv_val, Function.update_self, WState.seth_val, WState.sets_val]
    cases x with
    | nil => simp [encN]
    | cons y ys => rw [List.tail_cons, encN_cons, List.length_append]; omega
  | copyI Z =>
    simp only [FOp.eff, appendO, WState.setv_val, Function.update_self, WState.seth_val, WState.sets_val]
    cases x with
    | nil => simp [encN]
    | cons y ys => rw [List.tail_cons, encN_cons, List.length_append]; omega

theorem FOp.eff_sh_end (o : FOp ns nr) (x : List ℕ) (σ : WState ns nr) (Z : Fin (ns + 1))
    (h : σ.sh Z = (σ.st Z).length) : (o.eff Q x σ).sh Z = ((o.eff Q x σ).st Z).length := by
  cases o with
  | skip m => exact h
  | read q => exact h
  | copy m Y => by_cases hZ : Z = Y
                · subst hZ; simp [FOp.eff, appendO, h]
                · simp [FOp.eff, appendO, Function.update_of_ne hZ, h]
  | skipC => exact h
  | copyC Y => by_cases hZ : Z = Y
               · subst hZ; simp [FOp.eff, appendO, h]
               · simp [FOp.eff, appendO, Function.update_of_ne hZ, h]
  | copyI Y => by_cases hZ : Z = Y
               · subst hZ; simp [FOp.eff, appendO, h]
               · simp [FOp.eff, appendO, Function.update_of_ne hZ, h]

theorem scriptEff_seth : ∀ (ops : List (FOp ns nr)) (segs : List (List ℕ)) (σ : WState ns nr) (X : Fin (ns + 1)),
    (∀ Z ∈ ops.flatMap FOp.strs, X ≠ Z) → ∀ p, scriptEff Q ops segs (σ.seth X p) = (scriptEff Q ops segs σ).seth X p
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | o :: os, x :: xs, σ, X, h, p => by
    simp only [scriptEff]
    rw [FOp.eff_seth Q o x σ X (fun Z hZ => h Z (by simp [hZ])) p]
    exact scriptEff_seth os xs _ X (fun Z hZ => h Z (by simp [hZ])) p

/-- **A whole unpacking script.** -/
theorem script_spec (rest : List Bool) (Λ : ℕ) : ∀ (ops : List (FOp ns nr)) (segs : List (List ℕ)),
    List.Forall₂ (fun o x => FOp.Seg o x ∧ FOp.ReadOK Λ o x) ops segs → ∀ (A B : List ℕ) (σ : WState ns nr),
    NatAt IN (A ++ segs.flatten ++ B) rest σ A.length → QZero Q σ →
    (∀ r ∈ ops.flatMap FOp.regs, (∀ i, Q i ≠ r) ∧ σ.val r = 0) → (ops.flatMap FOp.regs).Nodup →
    (∀ Z ∈ ops.flatMap FOp.strs, IN ≠ Z ∧ σ.sh Z = (σ.st Z).length) →
    (∀ y ∈ A ++ segs.flatten ++ B, natBitLength y + 2 ≤ Λ) →
    (A ++ segs.flatten ++ B).length ≤ Λ →
    20 * (Λ + 1) ^ 2 + 4 * (encN (A ++ segs.flatten ++ B)).length + σ.val (Q 15) + (encN segs.flatten).length ≤ cap →
    WExec cap (scriptProg IN Q ops) σ ((scriptEff Q ops segs σ).seth IN (encN (A ++ segs.flatten)).length)
      (ops.length * (400 * (Λ + 1) ^ 2 + 1))
  | [], [], _, A, B, σ, hσ, _, _, _, _, _, _, _ => by
    simp only [scriptProg, scriptEff, List.flatten_nil, List.append_nil, List.length_nil, Nat.zero_mul]
    have h2 : σ.sh IN = (encN A).length := by rw [hσ.2]; simp
    rw [← h2, wseth_same]; exact WExec.skip σ
  | o :: os, x :: xs, List.Forall₂.cons hx hrest, A, B, σ, hσ, hz, hr, hnd, hs, hfit, hlen, hcap => by
    have hQ15 : Q 15 ∉ o.regs := fun h => by
      have := (hr (Q 15) (by simp [h])).1 15; exact this rfl
    have hfl : (x :: xs).flatten = x ++ xs.flatten := rfl
    rw [hfl] at hσ hfit hlen hcap ⊢
    have e1 := FOp.prog_spec cap IN Q o x A (xs.flatten ++ B) hx.1 rest σ
      (natAt_congr IN rest (by simp [List.append_assoc]) hσ) hz
      (fun r h => hr r (by simp [h])) (fun Z h => hs Z (by simp [h])) Λ
      (fun y hy => hfit y (by simp only [List.mem_append] at hy ⊢; tauto)) hx.2
      (by simp only [List.length_append] at hlen ⊢; omega)
      (by have : (encN (A ++ x ++ (xs.flatten ++ B))).length = (encN (A ++ (x ++ xs.flatten) ++ B)).length := by
            simp [List.append_assoc]
          omega)
    set σ1 := (o.eff Q x σ).seth IN (encN (A ++ x)).length with hσ1
    have hsIN : ∀ Z ∈ o.strs, IN ≠ Z := fun Z h => (hs Z (by simp [h])).1
    have e2 := script_spec rest Λ os xs hrest (A ++ x) B σ1
      ⟨by rw [hσ1, WState.seth_st, (FOp.eff_st_ne Q o x σ IN hsIN).1, hσ.1]; simp [List.append_assoc],
       by simp only [hσ1, WState.seth_sh, Function.update_self]
          rw [show A ++ x ++ xs.flatten ++ B = (A ++ x) ++ (xs.flatten ++ B) by simp [List.append_assoc], List.take_left]⟩
      (fun i hi => by
        rw [hσ1, WState.seth_val, FOp.eff_val_ne Q o x σ (Q i) (fun h => (hr (Q i) (by simp [h])).1 i rfl)
          (fun h => hi (Q.injective h))]
        exact hz i hi)
      (fun r h => by
        have hro : r ∉ o.regs := fun h' => by
          have := List.nodup_append.1 (by simpa using hnd); exact this.2.2 r h' r (by simpa using h) rfl
        have h15 : r ≠ Q 15 := fun e => (hr r (by simp [h])).1 15 e.symm
        refine ⟨(hr r (by simp [h])).1, ?_⟩
        rw [hσ1, WState.seth_val, FOp.eff_val_ne Q o x σ r hro h15]; exact (hr r (by simp [h])).2)
      (by have := hnd; simp only [List.flatMap_cons] at this; exact (List.nodup_append.1 this).2.1)
      (fun Z h => by
        refine ⟨(hs Z (by simp [h])).1, ?_⟩
        simp only [hσ1, WState.seth_sh, WState.seth_st, Function.update_of_ne (Ne.symm (hs Z (by simp [h])).1)]
        exact FOp.eff_sh_end Q o x σ Z (hs Z (by simp [h])).2)
      (fun y hy => hfit y (by simp only [List.mem_append] at hy ⊢; tauto))
      (by simp only [List.length_append] at hlen ⊢; omega)
      (by have h15 := FOp.eff_15 Q o x σ hQ15
          have hσ15 : σ1.val (Q 15) = (o.eff Q x σ).val (Q 15) := by rw [hσ1, WState.seth_val]
          have : (encN (A ++ x ++ xs.flatten ++ B)).length = (encN (A ++ (x ++ xs.flatten) ++ B)).length := by
            simp [List.append_assoc]
          have : (encN (x ++ xs.flatten)).length = (encN x).length + (encN xs.flatten).length := by
            rw [encN_append, List.length_append]
          omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · simp only [scriptEff]
      rw [hσ1, scriptEff_seth Q os xs _ IN (fun Z h => (hs Z (by simp [h])).1) _, wseth_seth,
        List.append_assoc]
    · simp only [List.length_cons]; ring_nf; omega

end Script

end NearCubicGates.Close.CounterMachine
