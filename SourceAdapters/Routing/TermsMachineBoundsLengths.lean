import SourceAdapters.Joins.TermsCircuit
import SourceAdapters.Routing.CircuitEncodingCount
import SourceAdapters.Proximity.TrimSizes

/-! # Serialized request lengths and the exact circuit gate count -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Bounds

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMACSP
open NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Close.Cells (natWord_length natBitLength_pos)

variable {F : Type}

theorem flatMap_length_lower {α β : Type} (g : α → List β) (xs : List α) (c : ℕ)
    (h : ∀ x ∈ xs, c ≤ (g x).length) : c * xs.length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hs := ih (fun y hy => h y (by simp [hy]))
      simp only [List.length_cons, List.flatMap_cons, List.length_append, Nat.mul_add, Nat.mul_one]
      omega

theorem natWord_three (x : ℕ) : 3 ≤ (natWord x).length := by
  rw [natWord_length]
  have := natBitLength_pos x
  omega

theorem token_length (t : TermTok) : 6 ≤ (termTokWord t).length := by
  cases t <;> simp only [termTokWord, List.length_append] <;>
    have h1 := natWord_three 0 <;> have h2 := natWord_three 1 <;>
    have h3 := natWord_three 2 <;> have h4 := natWord_three 3 <;>
    have h5 := natWord_three 4
  · have := natWord_three ‹ℕ›; omega
  · have := natWord_three (varCode ‹Vars›); omega
  all_goals omega

theorem tokens_length (mk : F → ℕ) (E : Expr F) : (exprToks mk E).length = gateCount E := by
  induction E <;> simp_all [exprToks, gateCount, Nat.add_assoc]

theorem expr_length_lower (mk : F → ℕ) (E : Expr F) :
    6 * (gateCount E + 1) ≤ (exprWord mk E).length := by
  have ht := flatMap_length_lower termTokWord (exprToks mk E) 6 (fun t _ => token_length t)
  have h0 := natWord_three 0
  have h5 := natWord_three 5
  rw [tokens_length] at ht
  simp only [exprWord, List.length_append]
  omega

theorem pattern_length_lower {m : ℕ} (g : Pattern m) : 3 * m ≤ (patternWord g).length := by
  have hh := flatMap_length_lower (fun o => natWord (guardCode o)) (List.ofFn g) 3
    (fun o _ => natWord_three (guardCode o))
  simpa only [List.length_ofFn, patternWord] using hh

theorem itemCost_le_word (mk : F → ℕ) {m : ℕ} (item : Pattern m × Expr F) :
    itemCost item ≤ (itemWord mk item).length := by
  have hp := patternCost_sum_le item.1 (List.finRange m)
  simp only [List.length_finRange] at hp
  have hg := pattern_length_lower item.1
  have he := expr_length_lower mk item.2
  have h1 := natWord_three 1
  simp only [itemCost, itemWord, List.length_append]
  omega

theorem item_tokens_le_word (mk : F → ℕ) {m : ℕ} (item : Pattern m × Expr F) :
    (exprToks mk item.2).length + 1 ≤ (itemWord mk item).length := by
  have he := expr_length_lower mk item.2
  rw [tokens_length]
  simp only [itemWord, List.length_append]
  omega

theorem items_cost_le_word (mk : F → ℕ) {m : ℕ} (items : List (Pattern m × Expr F)) :
    (items.map itemCost).sum ≤ (items.flatMap (itemWord mk)).length := by
  induction items with
  | nil => simp
  | cons i items ih =>
      have := itemCost_le_word mk i
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
      omega

theorem items_tokens_le_word (mk : F → ℕ) {m : ℕ} (items : List (Pattern m × Expr F)) :
    (items.map fun i => (exprToks mk i.2).length + 1).sum ≤ (items.flatMap (itemWord mk)).length := by
  induction items with
  | nil => simp
  | cons i items ih =>
      have := item_tokens_le_word mk i
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
      omega

theorem items_length_le_word (mk : F → ℕ) {m : ℕ} (items : List (Pattern m × Expr F)) :
    items.length ≤ (items.flatMap (itemWord mk)).length := by
  have hh := flatMap_length_lower (itemWord mk) items 1 (fun i _ => by
    have := natWord_three 1
    simp only [itemWord, List.length_append]
    omega)
  simpa only [one_mul] using hh

theorem coord_length (p : TermsReq) (h : TermsOk p) :
    (termsCoordWord p h).length = p.l.m * p.l.m * p.f := by
  simp [termsCoordWord, List.length_flatMap, WilliamsLoaderForms.fixedWidthNatBits, Nat.mul_assoc]

theorem input_length (p : TermsReq) (h : TermsOk p) :
    (termsInput p h).length = (natWord p.f).length + (natWord p.l.m).length + p.l.m * p.l.m * p.f +
      (listWord natWord (globalBank p.l)).length +
      (p.items.flatMap (itemWord (termsMask p h))).length + (natWord 0).length := by
  simp only [termsInput, List.length_append, coord_length]
  omega

theorem request_size (p : TermsReq) (h : TermsOk p) :
    let rawN := (termsInput p h).length
    p.f ≤ rawN ∧ p.l.m ≤ rawN ∧ p.l.m * p.l.m ≤ rawN ∧
      (globalBank p.l).length ≤ rawN ∧ p.items.length ≤ rawN ∧
      (p.items.map fun i => (exprToks (termsMask p h) i.2).length + 1).sum ≤ rawN := by
  intro rawN
  have hh := input_length p h
  have hm : 1 ≤ p.l.m := h.2.2.1
  have hf : 1 ≤ p.f := by have := h.2.2.2; omega
  have hsq : 1 ≤ p.l.m * p.l.m := Nat.mul_pos hm hm
  have hff : p.f ≤ p.l.m * p.l.m * p.f := by nlinarith
  have hmsq : p.l.m ≤ p.l.m * p.l.m := by nlinarith
  have hsqf : p.l.m * p.l.m ≤ p.l.m * p.l.m * p.f := by nlinarith
  have hb := NearCubicGates.Adapters.Proximity.Trim.fieldWords_count_le (globalBank p.l)
  have hi := items_length_le_word (termsMask p h) p.items
  have ht := items_tokens_le_word (termsMask p h) p.items
  have hbl : (listWord natWord (globalBank p.l)).length =
      (natWord (globalBank p.l).length).length + ((globalBank p.l).flatMap natWord).length := by
    simp [listWord, List.flatMap_def]
  dsimp only [rawN]
  omega

theorem bank_bitLength_le (p : TermsReq) (h : TermsOk p) {x : ℕ} (hx : x ∈ globalBank p.l) :
    natBitLength x ≤ (termsInput p h).length := by
  have hb := NearCubicGates.Adapters.Proximity.Trim.field_bitLength_le hx
  have hh := input_length p h
  have hbl : (listWord natWord (globalBank p.l)).length =
      (natWord (globalBank p.l).length).length + ((globalBank p.l).flatMap natWord).length := by
    simp [listWord, List.flatMap_def]
  omega

theorem mask_lt (p : TermsReq) (h : TermsOk p) (c : Field2 p.irr) : termsMask p h c < 2 ^ p.f :=
  WireExponent3_5.GF.ofPoly_lt _ _

theorem circuit_length_le (p : TermsReq) (h : TermsOk p) :
    (termsCircuit p h).length ≤ 10 * ((termsInput p h).length + 1) := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  have hc := Encoding.compileTerms_length p.l (monoBasis p.irr p.l.m)
    (explicitCoordinates (monoBasis p.irr p.l.m) (termsIndependent p h)) p.items
  have hs := request_size p h
  have hi := items_cost_le_word (termsMask p h) p.items
  have hl := input_length p h
  simp only [termsCircuit, List.length_map]
  rw [hc]
  rw [pow_two]
  omega

end NearCubicGates.Adapters.Routing.TermsMachine.Bounds
