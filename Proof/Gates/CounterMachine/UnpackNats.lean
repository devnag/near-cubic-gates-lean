import Proof.Gates.CounterMachine.FormulaOut

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

section Nats
variable (IN : Fin (ns + 1)) (L : List ℕ) (rest : List Bool)

/-- The head of `IN` stands at field `i` of `L`. -/
def NatAt (σ : WState ns nr) (i : ℕ) : Prop :=
  σ.st IN = encN L ++ rest ∧ σ.sh IN = (encN (L.take i)).length

theorem encN_mid (i m : ℕ) :
    encN L = encN (L.take i) ++ ((L.drop i).take m).flatMap (fun x => enc true (natWord x)) ++
      encN (L.drop (i + m)) := by
  conv_lhs => rw [← List.take_append_drop i L, ← List.take_append_drop m (L.drop i)]
  rw [List.drop_drop, encN_append, encN_append]
  simp [encN, List.flatMap, List.append_assoc, Nat.add_comm]

theorem encN_take_add (i m : ℕ) :
    (encN (L.take (i + m))).length =
      (encN (L.take i)).length + (((L.drop i).take m).flatMap (fun x => enc true (natWord x))).length := by
  rw [List.take_add, encN_append, List.length_append]
  simp [encN, List.flatMap]

theorem encN_eq_marks (L' : List ℕ) : encN L' = marks (L'.flatMap natWord) := by
  induction L' with
  | nil => simp [encN, marks]
  | cons x xs ih =>
    rw [encN_cons, List.flatMap_cons, marksApp, ih]
    simp [WireExponent3_5.PrimAsm.ParseNat.enc]

/-- Step over `m` fields (`m` in `K`; scratch `f`, `c`). -/
theorem skipNs_spec (K f c : Fin nr) (hKf : K ≠ f) (hKc : K ≠ c) (hfc : f ≠ c) (σ : WState ns nr) (i m : ℕ)
    (hσ : NatAt IN L rest σ i) (hK : σ.val K = m) (hm : i + m ≤ L.length) (hf : σ.val f = 0) (hc : σ.val c = 0)
    (hfit : ∀ x ∈ L, natBitLength x + 1 ≤ cap) (hcm : m ≤ cap) :
    WExec cap (listLoop K (skipNat true IN f c)) σ ((σ.setv K 0).seth IN (encN (L.take (i + m))).length)
      ((((L.drop i).take m).map fun x => 20 * natBitLength x + 20 + 4).sum + 1) := by
  have e := listLoop_spec cap IN K (skipNat true IN f c) (fun x => enc true (natWord x))
    (fun x => 20 * natBitLength x + 20) (fun τ => τ.val f = 0 ∧ τ.val c = 0)
    (fun τ x h => ⟨by simpa using h.1, by simpa using h.2⟩)
    (fun τ x h => ⟨by simp [Function.update_of_ne (Ne.symm hKf), h.1], by simp [Function.update_of_ne (Ne.symm hKc), h.2]⟩)
    ((L.drop i).take m)
    (fun x hx pre rest' τ h hst' hsh' => by
      have := skipNat_spec cap true IN f c hfc x pre rest' τ hst' hsh' h.1 h.2
        (hfit x (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
      simpa [enc_length, stp] using this)
    (encN (L.take i)) (encN (L.drop (i + m)) ++ rest) σ ⟨hf, hc⟩
    (by rw [hσ.1, encN_mid L i m]; simp [List.append_assoc]) hσ.2 (by rw [hK]; simp; omega) (by simp; omega)
  rw [← encN_take_add] at e
  simpa using e

/-- Append the next `m` fields to `X` (`m` in `K`; the register file `R` of `copyNat`, position `R 7`). -/
theorem copyNs_spec (X : Fin (ns + 1)) (hIX : IN ≠ X) (R : Fin 8 ↪ Fin nr) (K : Fin nr) (hKR : ∀ j, R j ≠ K)
    (σ : WState ns nr) (i m : ℕ) (hσ : NatAt IN L rest σ i) (hK : σ.val K = m) (hm : i + m ≤ L.length)
    (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0) (hX : σ.sh X = (σ.st X).length)
    (V : ℕ) (hV : σ.val (R 7) + (encN ((L.drop i).take m)).length ≤ V)
    (hfit : V + 2 * (L.map fun x => (natWord x).length).sum + 4 ≤ cap) (hcm : m ≤ cap) :
    WExec cap (listLoop K (copyNat true IN X R)) σ
      (((appendO σ X (R 7) (encN ((L.drop i).take m))).setv K 0).seth IN (encN (L.take (i + m))).length)
      ((((L.drop i).take m).map fun x => 60 * (natWord x).length + 60 + 4).sum + 1) := by
  have hRne : ∀ {a b : Fin 8}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have hsum : ∀ x ∈ L, (natWord x).length ≤ (L.map fun x => (natWord x).length).sum := fun x hx =>
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  have e := copyLoop_spec cap IN X hIX K (R 7) (hKR 7).symm (copyNat true IN X R) (fun x => enc true (natWord x))
    natWord (fun x => 60 * (natWord x).length + 60) (fun τ => τ.val (R 1) = 0 ∧ τ.val (R 2) = 0) V
    (fun τ x h => ⟨by simpa using h.1, by simpa using h.2⟩)
    (fun τ x h => ⟨by simp [Function.update_of_ne (hKR 1), h.1], by simp [Function.update_of_ne (hKR 2), h.2]⟩)
    (fun τ w h => ⟨by simp [appendO, Function.update_of_ne (hRne (show (1 : Fin 8) ≠ 7 by decide)), h.1],
      by simp [appendO, Function.update_of_ne (hRne (show (2 : Fin 8) ≠ 7 by decide)), h.2]⟩)
    ((L.drop i).take m)
    (fun x hx pre rest' τ h hst' hsh' ho hVτ => by
      have hxL := List.mem_of_mem_drop (List.mem_of_mem_take hx)
      have := copyNat_spec cap true IN X hIX R x pre rest' τ hst' hsh' ho h.1 h.2
        (by rw [marks_length] at hVτ; have := hsum x hxL; omega)
      simpa [enc_length, stp] using this)
    (encN (L.take i)) (encN (L.drop (i + m)) ++ rest) σ ⟨h1, h2⟩
    (by rw [hσ.1, encN_mid L i m]; simp [List.append_assoc]) hσ.2 hX (by rw [hK]; simp; omega) (by simp; omega)
    (by rw [← encN_eq_marks]; exact hV)
  rw [← encN_take_add, ← encN_eq_marks] at e
  simpa using e

/-- Add the next field's value to `v` (scratch `f c p t`). -/
theorem readN_spec (f c v p t : Fin nr) (hd : [f, c, v, p, t].Nodup) (σ : WState ns nr) (i : ℕ)
    (hσ : NatAt IN L rest σ i) (hi : i < L.length) (hf : σ.val f = 0) (hc : σ.val c = 0) (hp : σ.val p = 0)
    (ht : σ.val t = 0) (hcap : σ.val v + 2 ^ (natBitLength L[i] + 1) ≤ cap) :
    WExec cap (readNatM true IN f c v p t) σ ((σ.seth IN (encN (L.take (i + 1))).length).setv v (σ.val v + L[i]))
      ((natBitLength L[i] + 2) * (40 * 2 ^ natBitLength L[i] + 40)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨fc, fv, fp, ft⟩, ⟨cv, cp, ct⟩, ⟨vp, vt⟩, pt⟩ := hd
  have e := readNatM_spec cap true IN f c v p t fc fv fp ft cv cp ct (Ne.symm vp) pt vt L[i] (encN (L.take i))
    (encN (L.drop (i + 1)) ++ rest) σ (by rw [hσ.1, encN_split L i hi]; simp [List.append_assoc]) hσ.2 hf hc hp ht hcap
  rw [show (encN (L.take i)).length + stp true * (natWord L[i]).length = (encN (L.take (i + 1))).length by
    rw [encN_take_succ L i hi]; simp [stp]] at e
  exact e

/-- The list `A ++ P ++ B` read from field `|A|`: the next `|P|` fields are `P`. -/
theorem drop_take_mid {α : Type} (A P B : List α) : ((A ++ P ++ B).drop A.length).take P.length = P := by simp

theorem take_mid {α : Type} (A P B : List α) : (A ++ P ++ B).take (A.length + P.length) = A ++ P := by
  simp [List.take_append]

theorem getElem_mid {α : Type} (A B : List α) (x : α) :
    (A ++ [x] ++ B)[A.length]'(by simp) = x := by simp

theorem lt_two_pow_nbl (x : ℕ) : x < 2 ^ natBitLength x := Nat.lt_pow_succ_log_self (by norm_num) x

theorem encN_length (L' : List ℕ) : (encN L').length = 2 * (L'.map fun x => (natWord x).length).sum := by
  induction L' with
  | nil => rfl
  | cons x xs ih => rw [encN_cons, List.length_append, ih]; simp [WireExponent3_5.PrimAsm.ParseNat.enc_length, stp]; ring

theorem natWords_sum_le (L' : List ℕ) (Λ : ℕ) (h : ∀ x ∈ L', natBitLength x ≤ Λ) :
    (L'.map fun x => (natWord x).length).sum ≤ L'.length * (2 * Λ + 1) :=
  sum_map_le L' _ _ fun x hx => by rw [natWord_length']; have := h x hx; omega

theorem take_prefix {α : Type} (P X S : List α) : (P ++ X ++ S).take P.length = P := by simp

theorem encN_le_mid (P X S : List ℕ) : (encN X).length ≤ (encN (P ++ X ++ S)).length := by
  rw [encN_append, encN_append]; simp only [List.length_append]; omega

theorem readCost_le (x Λ : ℕ) (h1 : natBitLength x + 2 ≤ Λ) (h2 : 2 ^ (natBitLength x + 1) ≤ Λ) :
    (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ Λ * (40 * Λ + 40) := by
  have : 2 ^ natBitLength x ≤ 2 ^ (natBitLength x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.mul_le_mul h1 (by omega)

theorem copySum_le (X : List ℕ) (Λ : ℕ) (hX : ∀ x ∈ X, natBitLength x ≤ Λ) :
    (X.map fun x => 60 * (natWord x).length + 60 + 4).sum ≤ X.length * (120 * Λ + 124) :=
  sum_map_le X _ _ fun x hx => by rw [natWord_length']; have := hX x hx; omega

theorem skipSum_le (X : List ℕ) (Λ : ℕ) (hX : ∀ x ∈ X, natBitLength x ≤ Λ) :
    (X.map fun x => 20 * natBitLength x + 20 + 4).sum ≤ X.length * (20 * Λ + 24) :=
  sum_map_le X _ _ fun x hx => by have := hX x hx; omega

/-! ## Field steps on `A ++ X ++ B` -/

theorem readF_spec (f c v p t : Fin nr) (hd : [f, c, v, p, t].Nodup) (A B : List ℕ) (x : ℕ) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ [x] ++ B) rest σ A.length) (hf : σ.val f = 0) (hc : σ.val c = 0) (hp : σ.val p = 0)
    (ht : σ.val t = 0) (hcap : σ.val v + 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (readNatM true IN f c v p t) σ ((σ.seth IN (encN (A ++ [x])).length).setv v (σ.val v + x))
      ((natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)) := by
  have e := readN_spec cap IN (A ++ [x] ++ B) rest f c v p t hd σ A.length hσ (by simp) hf hc hp ht
    (by rw [getElem_mid]; exact hcap)
  rw [getElem_mid, show A.length + 1 = A.length + [x].length by simp, take_mid] at e
  exact e

theorem skipF_spec (K f c : Fin nr) (hKf : K ≠ f) (hKc : K ≠ c) (hfc : f ≠ c) (A X B : List ℕ) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ X ++ B) rest σ A.length) (hK : σ.val K = X.length) (hf : σ.val f = 0) (hc : σ.val c = 0)
    (hfit : ∀ x ∈ A ++ X ++ B, natBitLength x + 1 ≤ cap) (hcm : X.length ≤ cap) :
    WExec cap (listLoop K (skipNat true IN f c)) σ ((σ.setv K 0).seth IN (encN (A ++ X)).length)
      ((X.map fun x => 20 * natBitLength x + 20 + 4).sum + 1) := by
  have e := skipNs_spec cap IN (A ++ X ++ B) rest K f c hKf hKc hfc σ A.length X.length hσ hK (by simp) hf hc hfit hcm
  rw [take_mid, drop_take_mid] at e
  exact e

theorem copyF_spec (Z : Fin (ns + 1)) (hIZ : IN ≠ Z) (R : Fin 8 ↪ Fin nr) (K : Fin nr) (hKR : ∀ j, R j ≠ K)
    (A X B : List ℕ) (σ : WState ns nr) (hσ : NatAt IN (A ++ X ++ B) rest σ A.length) (hK : σ.val K = X.length)
    (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0) (hZ : σ.sh Z = (σ.st Z).length)
    (hfit : σ.val (R 7) + 3 * (encN (A ++ X ++ B)).length + 4 ≤ cap) (hcm : X.length ≤ cap) :
    WExec cap (listLoop K (copyNat true IN Z R)) σ
      (((appendO σ Z (R 7) (encN X)).setv K 0).seth IN (encN (A ++ X)).length)
      ((X.map fun x => 60 * (natWord x).length + 60 + 4).sum + 1) := by
  have hle := encN_le_mid A X B
  have hlen := encN_length (A ++ X ++ B)
  have e := copyNs_spec cap IN (A ++ X ++ B) rest Z hIZ R K hKR σ A.length X.length hσ hK (by simp) h1 h2 hZ
    (σ.val (R 7) + (encN X).length) (by rw [drop_take_mid]) (by omega) hcm
  rw [take_mid, drop_take_mid] at e
  exact e

theorem natAt_congr {L L' : List ℕ} (h : L = L') {σ : WState ns nr} {i : ℕ} (hσ : NatAt IN L rest σ i) :
    NatAt IN L' rest σ i := h ▸ hσ

end Nats

end NearCubicGates.Close.CounterMachine
