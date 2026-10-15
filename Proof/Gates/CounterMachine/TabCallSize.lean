import Proof.Gates.CounterMachine.TabCallSplit
import Proof.Gates.CounterMachine.FormulaCost
import Proof.Gates.Cells.InputLen
import Proof.Gates.Cells.Sys
import Proof.Gates.Counter.Main
import Proof.Gates.CheckedPCPP.PolyClass

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.CounterMachine.TabCallSizes

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

/-! ## Bit lengths -/

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega

theorem nbl_le_self' (v : ℕ) : natBitLength v ≤ v + 1 := Cells.nbl_le_self v

theorem size_le_nbl (v : ℕ) : Nat.size v ≤ natBitLength v := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) v)

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := Cells.natWord_length v

/-! ## One measure for size, weight and the formula word -/

/-- Dominates size (exponents in unary), weight, token count and every token payload's bit length. -/
def fw {V : ℕ} : Formula V → ℕ
  | .const a => natBitLength a.natAbs + 1
  | .var _ => 1
  | .add f g => fw f + fw g + 1
  | .neg f => fw f + 1
  | .sub f g => fw f + fw g + 1
  | .mul f g => fw f + fw g + 1
  | .pow f e => (e + 1) * (fw f + 1) + natBitLength e

variable {V : ℕ}

theorem fw_pos (F : Formula V) : 1 ≤ fw F := by
  cases F <;> simp only [fw] <;> nlinarith

theorem size_le_fw (F : Formula V) : F.size ≤ fw F := by
  induction F with
  | const a => simp [Formula.size, fw]
  | var v => simp [Formula.size, fw]
  | add f g ihf ihg => simp only [Formula.size, fw]; omega
  | neg f ih => simp only [Formula.size, fw]; omega
  | sub f g ihf ihg => simp only [Formula.size, fw]; omega
  | mul f g ihf ihg => simp only [Formula.size, fw]; omega
  | pow f e ih => simp only [Formula.size, fw]; nlinarith

theorem weight_le_fw (F : Formula V) : F.weight ≤ fw F := by
  induction F with
  | const a => simp only [Formula.weight, fw]; have := size_le_nbl a.natAbs; omega
  | var v => simp [Formula.weight, fw]
  | add f g ihf ihg => simp only [Formula.weight, fw]; omega
  | neg f ih => simp only [Formula.weight, fw]; omega
  | sub f g ihf ihg => simp only [Formula.weight, fw]; omega
  | mul f g ihf ihg => simp only [Formula.weight, fw]; omega
  | pow f e ih => simp only [Formula.weight, fw]; nlinarith

theorem toks_length_le_fw (F : Formula V) : (toks F).length ≤ fw F := by
  induction F with
  | const a => simp [toks, fw]
  | var v => simp [toks, fw]
  | add f g ihf ihg => simp only [toks, fw, List.length_append, List.length_singleton]; omega
  | neg f ih => simp only [toks, fw, List.length_append, List.length_singleton]; omega
  | sub f g ihf ihg => simp only [toks, fw, List.length_append, List.length_singleton]; omega
  | mul f g ihf ihg => simp only [toks, fw, List.length_append, List.length_singleton]; omega
  | pow f e ih => simp only [toks, fw, List.length_append, List.length_singleton]; nlinarith

theorem tokWord_le_fw (F : Formula V) : ∀ t ∈ toks F, (tokWord t).length ≤ 2 * fw F + 2 * natBitLength V + 30 := by
  induction F with
  | const a =>
    intro t ht
    simp only [toks, List.mem_singleton] at ht
    subst ht
    have := intWord_length_le a
    simp only [tokWord, List.length_append, natWord_len, fw]
    have h0 : natBitLength 0 = 1 := by simp [natBitLength]
    omega
  | var v =>
    intro t ht
    simp only [toks, List.mem_singleton] at ht
    subst ht
    have h1 := nbl_mono (le_of_lt v.isLt)
    have h1' : natBitLength 1 = 1 := by simp [natBitLength]
    simp only [tokWord, List.length_append, natWord_len, fw]
    omega
  | add f g ihf ihg =>
    intro t ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with (h | h) | h
    · have := ihf t h; simp only [fw]; omega
    · have := ihg t h; simp only [fw]; omega
    · subst h; simp only [tokWord, natWord_len]; have : natBitLength 2 = 2 := by decide
      omega
  | neg f ih =>
    intro t ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with h | h
    · have := ih t h; simp only [fw]; omega
    · subst h; simp only [tokWord, natWord_len]; have : natBitLength 3 = 2 := by decide
      omega
  | sub f g ihf ihg =>
    intro t ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with (h | h) | h
    · have := ihf t h; simp only [fw]; omega
    · have := ihg t h; simp only [fw]; omega
    · subst h; simp only [tokWord, natWord_len]; have : natBitLength 4 = 3 := by decide
      omega
  | mul f g ihf ihg =>
    intro t ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    rcases ht with (h | h) | h
    · have := ihf t h; simp only [fw]; omega
    · have := ihg t h; simp only [fw]; omega
    · subst h; simp only [tokWord, natWord_len]; have : natBitLength 5 = 3 := by decide
      omega
  | pow f e ih =>
    intro t ht
    simp only [toks, List.mem_append, List.mem_singleton] at ht
    have hm : fw f ≤ (e + 1) * (fw f + 1) := by nlinarith
    rcases ht with h | h
    · have := ih t h; simp only [fw]; omega
    · subst h; simp only [tokWord, List.length_append, natWord_len, fw]; have : natBitLength 6 = 3 := by decide
      omega

theorem formulaWord_le (F : Formula V) :
    (formulaWord ⟨V, F⟩).length ≤ 2 * natBitLength V + 1 + (2 * fw F + 3) +
      fw F * (2 * fw F + 2 * natBitLength V + 30) := by
  simp only [formulaWord, listWord, List.length_append, natWord_len]
  have h1 := toks_length_le_fw F
  have h2 := nbl_le_self' (toks F).length
  have h3 := Cells.flatMap_len_le (toks F) tokWord _ (tokWord_le_fw F)
  have h4 : (toks F).length * (2 * fw F + 2 * natBitLength V + 30) ≤
      fw F * (2 * fw F + 2 * natBitLength V + 30) := Nat.mul_le_mul_right _ h1
  omega

/-! ## The measure through the constructors -/

theorem nbl_zero : natBitLength 0 = 1 := by simp [natBitLength]
theorem nbl_one : natBitLength 1 = 1 := by simp [natBitLength]

theorem fw_sumList_le (M : ℕ) : ∀ fs : List (Formula V), (∀ f ∈ fs, fw f ≤ M) →
    fw (Formula.sumList fs) ≤ fs.length * (M + 1) + 2
  | [], _ => by simp [Formula.sumList, fw, nbl_zero]
  | f :: fs, h => by
    have h1 := h f (by simp)
    have h2 := fw_sumList_le M fs (fun g hg => h g (by simp [hg]))
    simp only [Formula.sumList, fw, List.length_cons]
    nlinarith

theorem fw_prodList_le (M : ℕ) : ∀ fs : List (Formula V), (∀ f ∈ fs, fw f ≤ M) →
    fw (Formula.prodList fs) ≤ fs.length * (M + 1) + 2
  | [], _ => by simp [Formula.prodList, fw, nbl_one]
  | f :: fs, h => by
    have h1 := h f (by simp)
    have h2 := fw_prodList_le M fs (fun g hg => h g (by simp [hg]))
    simp only [Formula.prodList, fw, List.length_cons]
    nlinarith

theorem fw_varN (i : ℕ) : fw (varN (V := V) i) ≤ 2 := by
  unfold varN; split <;> simp [fw, nbl_zero]

theorem nbl_getD_le (a : List ℤ) (Λ : ℕ) (ha : ∀ z ∈ a, natBitLength z.natAbs ≤ Λ) (t : ℕ) :
    natBitLength (a.getD t 0).natAbs ≤ Λ + 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : a[t]? with
  | none => simp [nbl_zero]
  | some z => have := ha z (List.mem_of_getElem? h); simp; omega

theorem fw_linF (o m : ℕ) (a : List ℤ) (Λ : ℕ) (ha : ∀ z ∈ a, natBitLength z.natAbs ≤ Λ) :
    fw (linF (V := V) o m a) ≤ m * (Λ + 6) + 2 := by
  unfold linF
  have h := fw_sumList_le (Λ + 5) ((List.range m).map fun t =>
    (Formula.mul (.const (a.getD t 0)) (varN (V := V) (o + t)))) (by
      intro f hf
      simp only [List.mem_map, List.mem_range] at hf
      obtain ⟨t, _, rfl⟩ := hf
      have h1 := nbl_getD_le a Λ ha t
      have h2 := fw_varN (V := V) (o + t)
      simp only [fw]; omega)
  simp only [List.length_map, List.length_range] at h
  exact h

theorem nbl_choose_le (e j : ℕ) (hj : j < e) : natBitLength ((e - 1 + j).choose j) ≤ 2 * e := by
  apply Cells.nbl_le_of_lt _ (by omega)
  calc (e - 1 + j).choose j ≤ 2 ^ (e - 1 + j) := Nat.choose_le_two_pow _ _
    _ < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem fw_amp (e : ℕ) (t : Formula V) : fw (Formula.amp e t) ≤ 3 * (e + 1) ^ 2 * (fw t + 4) := by
  unfold Formula.amp
  have hs := fw_sumList_le ((e + 1) * (fw t + 4) - 1) ((List.range e).map fun j =>
    (Formula.mul (.const (((e - 1 + j).choose j : ℕ) : ℤ)) (Formula.pow t j))) (by
      intro f hf
      simp only [List.mem_map, List.mem_range] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have h1 := nbl_choose_le e j hj
      have h2 := nbl_le_self' j
      have h3 : (j + 1) * (fw t + 1) ≤ e * (fw t + 1) := Nat.mul_le_mul_right _ (by omega)
      have h4 : 1 ≤ fw t := fw_pos t
      have hc : (((e - 1 + j).choose j : ℕ) : ℤ).natAbs = (e - 1 + j).choose j := by simp
      simp only [fw, hc]
      have : e * (fw t + 1) + 3 * e + 3 ≤ (e + 1) * (fw t + 4) := by nlinarith
      omega)
  simp only [List.length_map, List.length_range] at hs
  have h4 : 1 ≤ fw t := fw_pos t
  have hn := nbl_le_self' e
  have hpos : 4 ≤ (e + 1) * (fw t + 4) := by nlinarith
  rw [Nat.sub_add_cancel (by omega)] at hs
  simp only [fw, Int.natAbs_one, nbl_one]
  have hsq : (e + 1) * (fw t + 4) + e * ((e + 1) * (fw t + 4)) = (e + 1) ^ 2 * (fw t + 4) := by ring
  have h8 : 8 * (e + 1) ≤ 2 * ((e + 1) ^ 2 * (fw t + 4)) := by nlinarith
  have h9 : (e + 1) * (fw t + 1 + 1 + 1 + 1) = (e + 1) * (fw t + 4) := by ring
  nlinarith

/-- A Fermat factor `1 − (f − ρ)^{q−1}`. -/
theorem fw_fermat (f : Formula V) (ρ : ℤ) (q : ℕ) :
    fw (Formula.sub (.const 1) (.pow (.sub f (.const ρ)) (q - 1))) ≤ (q + 1) * (fw f + natBitLength ρ.natAbs + 7) := by
  simp only [fw, Int.natAbs_one, nbl_one]
  have h1 := nbl_le_self' (q - 1)
  have h2 : (q - 1 + 1) * (fw f + (natBitLength ρ.natAbs + 1) + 1 + 1) ≤
      (q + 1) * (fw f + natBitLength ρ.natAbs + 3) := by
    have : q - 1 + 1 ≤ q + 1 := by omega
    calc (q - 1 + 1) * (fw f + (natBitLength ρ.natAbs + 1) + 1 + 1) = (q - 1 + 1) * (fw f + natBitLength ρ.natAbs + 3) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  nlinarith

theorem fw_resF {R : ℕ} (q e : ℕ) (f : Fin R → Formula V) (ρ : Fin R → ℤ) (M B : ℕ) (hf : ∀ i, fw (f i) ≤ M)
    (hρ : ∀ i, natBitLength (ρ i).natAbs ≤ B) :
    fw (resF q e f ρ) ≤ 3 * (e + 1) ^ 2 * (R * ((q + 1) * (M + B + 7) + 1) + 6) := by
  unfold resF
  refine (fw_amp e _).trans ?_
  have hp := fw_prodList_le ((q + 1) * (M + B + 7)) ((List.finRange R).map fun i =>
    (Formula.sub (.const 1) (.pow (.sub (f i) (.const (ρ i))) (q - 1)) : Formula V)) (by
      intro g hg
      simp only [List.mem_map, List.mem_finRange, true_and] at hg
      obtain ⟨i, rfl⟩ := hg
      refine (fw_fermat (f i) (ρ i) q).trans (Nat.mul_le_mul_left _ ?_)
      have := hf i; have := hρ i; omega)
  simp only [List.length_map, List.length_finRange] at hp
  have : fw (Formula.prodList ((List.finRange R).map fun i =>
      (Formula.sub (.const 1) (.pow (.sub (f i) (.const (ρ i))) (q - 1)) : Formula V))) + 4 ≤
      R * ((q + 1) * (M + B + 7) + 1) + 6 := by omega
  exact Nat.mul_le_mul_left _ this

/-! ## The request's data are naturals of the cell input -/

theorem len_le_flatMap {α : Type} (f : α → List Bool) : ∀ (L : List α) (v : α), v ∈ L →
    (f v).length ≤ (L.flatMap f).length
  | [], v, h => absurd h (by simp)
  | a :: L, v, h => by
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := len_le_flatMap f L v h; omega

theorem nbl_cellN_le {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) (v : ℕ) (hv : v ∈ cellN r.c r.p r.wt) :
    natBitLength v ≤ (cellInput r).length := by
  have h1 := len_le_flatMap natWord _ v hv
  rw [cellN_word] at h1
  have h2 := Cells.nbl_le_word v
  unfold cellInput; omega

theorem coef_mem (c : Call) (p : Params) (wt : Wit c.n) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind)
    (z : ℤ) (hz : z ∈ wt.coef s r) : z.natAbs ∈ cellN c p wt := by
  unfold cellN witN
  apply List.mem_append_right
  apply List.mem_append_right
  refine List.mem_flatMap.2 ⟨(s, r), ?_, ?_⟩
  · unfold srList
    exact List.mem_flatMap.2 ⟨s, List.mem_range.2 hs, List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨z, hz, by simp [intN]⟩

theorem circ_coef_mem (c : Call) (p : Params) (wt : Wit c.n) (r : ℕ) (z : ℤ) (hz : z ∈ (circ c r).coeffs) :
    z.natAbs ∈ cellN c p wt := by
  have hm : z.natAbs ∈ circN (circ c r) := by
    unfold circN
    simp only [List.mem_append]
    left; left; right
    exact List.mem_flatMap.2 ⟨z, hz, by simp [intN]⟩
  unfold cellN callN
  apply List.mem_append_left; apply List.mem_append_left
  unfold circ at hm
  split_ifs at hm
  · simp only [List.mem_append]; left; left; left; left; right; exact hm
  · simp only [List.mem_append]; left; left; left; right; exact hm

theorem params_mem (c : Call) (p : Params) (wt : Wit c.n) (v : ℕ) (hv : v ∈ paramsN p) : v ∈ cellN c p wt := by
  unfold cellN; exact List.mem_append_left _ (List.mem_append_right _ hv)

theorem M1_mem (p : Params) : p.M1 ∈ paramsN p := by unfold paramsN; simp
theorem A_mem (p : Params) : p.A ∈ paramsN p := by unfold paramsN; simp
theorem factor_mem (p : Params) (f : ℕ) (hf : f ∈ p.factors) : f ∈ paramsN p := by unfold paramsN; simp [hf]

/-! ## The request identifiers -/

theorem mem_residue {c : Call} {p : Params} {part : Option Bool} {q : ℕ} {κ σ : List ℕ}
    (h : ReqId.residue part q κ σ ∈ reqIds c p) :
    q ∈ p.primes ∧ κ ∈ vecs q (roleCount c.kind * p.J) ∧ σ ∈ vecs q (roleCount c.kind) := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, q', hq', κ', hκ', σ', hσ', h⟩ | ⟨_, _, (⟨_, _, h⟩ | h)⟩
  · cases h; exact ⟨by simpa using hq', hκ', hσ'⟩
  · cases h
  · cases h

theorem mem_digit {c : Call} {p : Params} {r j : ℕ} (h : ReqId.digitMoment r j ∈ reqIds c p) :
    r < roleCount c.kind ∧ j < p.J := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, q', _, κ', _, σ', _, h⟩ | ⟨r', hr', (⟨j', hj', h⟩ | h)⟩
  · cases h
  · cases h; exact ⟨hr', hj'⟩
  · cases h

theorem mem_phi {c : Call} {p : Params} {r : ℕ} (h : ReqId.phiMoment r ∈ reqIds c p) : r < roleCount c.kind := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, q', _, κ', _, σ', _, h⟩ | ⟨r', hr', (⟨j', _, h⟩ | h)⟩
  · cases h
  · cases h
  · cases h; exact hr'

/-! ## The request formulas -/

/-- The bound of every linear form (stage, score). -/
def Lf (n Λ : ℕ) : ℕ := 2 * n ^ 4 * (Λ + 6) + 2

section Forms
variable (c : Call) (p : Params) (wt : Wit c.n) (Λ : ℕ)
  (hcoef : ∀ s < p.J, ∀ r < roleCount c.kind, ∀ z ∈ wt.coef s r, natBitLength z.natAbs ≤ Λ)
  (hcirc : ∀ r, ∀ z ∈ (circ c r).coeffs, natBitLength z.natAbs ≤ Λ)
  (hrate : ∀ j, natBitLength (rateOf p j).natAbs ≤ Λ + 1)
  (hM1 : natBitLength p.M1 ≤ Λ) (hA : natBitLength p.A ≤ Λ)
  (hm : ∀ r, (circ c r).gates.length ≤ 2 * c.n ^ 4) (hJ1 : 1 ≤ p.J)
include hcoef hcirc hrate hm

theorem fw_lin_coef (o r s : ℕ) (hr : r < roleCount c.kind) (hs : s < p.J) :
    fw (linF (V := V) o (circ c r).gates.length (wt.coef s r)) ≤ Lf c.n Λ := by
  refine (fw_linF o _ _ Λ (hcoef s hs r hr)).trans ?_
  unfold Lf; have := Nat.mul_le_mul_right (Λ + 6) (hm r); omega

theorem fw_lin_circ (o r : ℕ) : fw (linF (V := V) o (circ c r).gates.length (circ c r).coeffs) ≤ Lf c.n Λ := by
  refine (fw_linF o _ _ Λ (hcirc r)).trans ?_
  unfold Lf; have := Nat.mul_le_mul_right (Λ + 6) (hm r); omega

theorem fw_digF (r j : ℕ) (hr : r < roleCount c.kind) (hj : j < p.J) :
    fw (digF (V := V) c p wt r j) ≤ 2 * Lf c.n Λ + Λ + 4 := by
  cases j with
  | zero => have := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) (offR c r) r 0 hr hj; simp only [digF, stageF]; omega
  | succ j =>
    have h1 := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) (offR c r) r (j + 1) hr hj
    have h2 := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) (offR c r) r j hr (by omega)
    have h3 := hrate j
    simp only [digF, stageF, fw]; omega

theorem fw_digO (o r j : ℕ) (hr : r < roleCount c.kind) (hj : j < p.J) :
    fw (digO (V := V) c p wt o r j) ≤ 2 * Lf c.n Λ + Λ + 4 := by
  cases j with
  | zero => have := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) o r 0 hr hj; simp only [digO, stO]; omega
  | succ j =>
    have h1 := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) o r (j + 1) hr hj
    have h2 := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) o r j hr (by omega)
    have h3 := hrate j
    simp only [digO, stO, fw]; omega

include hM1 hA hJ1 in
theorem fw_phiO (o r : ℕ) (hr : r < roleCount c.kind) :
    fw (phiO (V := V) c p wt o r) ≤ 2 * Lf c.n Λ + 2 * Λ + 5 := by
  have h1 := fw_lin_coef c p wt Λ hcoef hcirc hrate hm (V := V) o r (p.J - 1) hr (by omega)
  have h2 := fw_lin_circ c p wt Λ hcoef hcirc hrate hm (V := V) o r
  simp only [phiO, stO, scO, fw]
  have e1 : ((p.M1 : ℤ)).natAbs = p.M1 := by simp
  have e2 : ((p.A : ℤ)).natAbs = p.A := by simp
  rw [e1, e2]; omega

include hJ1 in
theorem fw_resForm (i : ℕ) :
    fw (resForm (V := V) c p wt i) ≤ 2 * Lf c.n Λ + Λ + 4 := by
  unfold resForm
  split_ifs with h
  · exact fw_digF c p wt Λ hcoef hcirc hrate hm _ _ (by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h)
      (Nat.mod_lt _ (by omega))
  · have := fw_lin_circ c p wt Λ hcoef hcirc hrate hm (V := V) (offR c (i - roleCount c.kind * p.J))
      (i - roleCount c.kind * p.J)
    unfold scoreF; omega

end Forms

/-! ## The bound -/

/-- The residue formulas' measure bound. -/
def ResB (n Λ : ℕ) : ℕ := 3 * (2 * n + 3) ^ 2 * ((2 * n + 4) * ((n + 1) * (2 * Lf n Λ + Λ + n + 12) + 1) + 6)
/-- The moment formulas' measure bound. -/
def MomB (n Λ : ℕ) : ℕ := (2 * n + 1) * (4 * Lf n Λ + 4 * Λ + 12) + 2 * n + 1
/-- Every request formula's measure bound. -/
def Wb (n Λ : ℕ) : ℕ := ResB n Λ + MomB n Λ
/-- The request size bound. -/
def Tb (n Λ : ℕ) : ℕ := n + 4 * n ^ 4 + 4 * n * (n + 1) + 4 * n ^ 4 + (2 * (4 * n ^ 4 + 1) + 1 + (2 * Wb n Λ + 3) +
  Wb n Λ * (2 * Wb n Λ + 2 * (4 * n ^ 4 + 1) + 30)) + Wb n Λ + Wb n Λ + 1

theorem tabSize_le_of (R : TabReq) (W : ℕ) (hG : R.G ≤ 4 * R.n ^ 4) (hV : R.V ≤ 4 * R.n ^ 4)
    (hB : R.B ≤ 4 * R.n * (R.n + 1)) (hW : fw R.F ≤ W) :
    tabSize R ≤ R.n + 4 * R.n ^ 4 + 4 * R.n * (R.n + 1) + 4 * R.n ^ 4 + (2 * (4 * R.n ^ 4 + 1) + 1 + (2 * W + 3) +
      W * (2 * W + 2 * (4 * R.n ^ 4 + 1) + 30)) + W + W + 1 := by
  unfold tabSize
  have h1 := formulaWord_le R.F
  have h2 := size_le_fw R.F
  have h3 := weight_le_fw R.F
  have h4 := nbl_le_self' R.V
  have h5 : fw R.F * (2 * fw R.F + 2 * natBitLength R.V + 30) ≤ W * (2 * W + 2 * (4 * R.n ^ 4 + 1) + 30) :=
    Nat.mul_le_mul hW (by omega)
  omega

theorem B0_le (n : ℕ) : Call.B0 n ≤ 4 * n * (n + 1) := by
  unfold Call.B0
  exact Nat.mul_le_mul_left _ (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)

theorem roleCount_le (κ : CallKind) : roleCount κ ≤ 2 := by cases κ <;> simp [roleCount]

theorem getD_le_of_vecs {q d : ℕ} {v : List ℕ} (hv : v ∈ vecs q d) (i : ℕ) : v.getD i 0 < q ∨ v.getD i 0 = 0 := by
  rw [Cells.mem_vecs_iff] at hv
  by_cases hi : i < v.length
  · exact Or.inl (hv.2 i hi)
  · right; rw [List.getD_eq_default _ _ (by omega)]

/-- **The pointwise bound.** -/
theorem tab_le {B1 B2 cT : ℕ} (x : TabCallReq B1 B2 cT) : tabSize (tabCallTab x) ≤ Tb x.r.c.n (cellInput x.r).length := by
  have hs := cellReq_spec x.r
  have hadm := x.r.adm
  have hcoef : ∀ s < x.r.p.J, ∀ r < roleCount x.r.c.kind, ∀ z ∈ x.r.wt.coef s r,
      natBitLength z.natAbs ≤ (cellInput x.r).length :=
    fun s hs' r hr z hz => nbl_cellN_le x.r _ (coef_mem _ _ _ s r hs' hr z hz)
  have hcirc : ∀ r, ∀ z ∈ (circ x.r.c r).coeffs, natBitLength z.natAbs ≤ (cellInput x.r).length :=
    fun r z hz => nbl_cellN_le x.r _ (circ_coef_mem _ _ _ r z hz)
  have hrate : ∀ j, natBitLength (rateOf x.r.p j).natAbs ≤ (cellInput x.r).length + 1 := by
    intro j
    unfold rateOf
    rw [List.getD_eq_getElem?_getD]
    cases h : x.r.p.factors[j]? with
    | none => simp [nbl_zero]
    | some f =>
      have := nbl_cellN_le x.r f (params_mem _ _ _ f (factor_mem _ f (List.mem_of_getElem? h)))
      simp; omega
  have hM1 := nbl_cellN_le x.r _ (params_mem _ _ _ _ (M1_mem x.r.p))
  have hA := nbl_cellN_le x.r _ (params_mem _ _ _ _ (A_mem x.r.p))
  have hm : ∀ r, (circ x.r.c r).gates.length ≤ 2 * x.r.c.n ^ 4 := fun r => by
    have := circ_gates_le x.r.c hadm r; unfold G0 at this; omega
  have hJ1 : 1 ≤ x.r.p.J := hs.J_pos
  have hJ : x.r.p.J ≤ x.r.c.n + 1 := (J_le_Jmax x.r.c x.r.p hs).trans (Cells.Jmax_le x.r.c x.r.p hadm hs)
  have hk : x.r.p.k ≤ x.r.c.n := k_le_n x.r.c x.r.p hs
  have he : x.r.p.e ≤ 2 * (x.r.p.k + 1) := (leastUpTo_spec _ _ _ hs.e_eq).2.1
  have hrc := roleCount_le x.r.c.kind
  have hB := B0_le x.r.c.n
  have he' : x.r.p.e + 1 ≤ 2 * x.r.c.n + 3 := by omega
  have hLf : 2 * Lf x.r.c.n (cellInput x.r).length + (cellInput x.r).length + 4 ≤
      2 * Lf x.r.c.n (cellInput x.r).length + 2 * (cellInput x.r).length + 5 := by omega
  unfold tabCallTab
  split
  · rename_i part q κ σ hid
    have hmem := x.mem
    rw [hid] at hmem
    obtain ⟨hq, hκ, hσ⟩ := mem_residue hmem
    have hqn : q ≤ x.r.c.n := (primes_le hs q hq).trans (P_le_n x.r.c x.r.p hs)
    apply le_trans (tabSize_le_of _ (Wb x.r.c.n (cellInput x.r).length) ?_ ?_ ?_ ?_) (le_refl _)
    · show (resGates x.r.c).length ≤ 4 * x.r.c.n ^ 4
      have := resGates_le x.r.c hadm; unfold G0 at this; omega
    · show (resGates x.r.c).length ≤ 4 * x.r.c.n ^ 4
      have := resGates_le x.r.c hadm; unfold G0 at this; omega
    · exact hB
    · show fw (resFormula x.r.c x.r.p x.r.wt q κ σ) ≤ _
      unfold resFormula
      refine le_trans (fw_resF q x.r.p.e _ _ (2 * Lf x.r.c.n (cellInput x.r).length + (cellInput x.r).length + 4)
        (x.r.c.n + 1) (fun i => fw_resForm x.r.c x.r.p x.r.wt _ hcoef hcirc hrate hm hJ1 i.val) ?_) ?_
      · intro i
        unfold resRho
        split_ifs
        · have := getD_le_of_vecs hκ i.val
          have h2 := nbl_le_self' (κ.getD i.val 0)
          simp only [Int.natAbs_natCast]
          rcases this with h | h <;> omega
        · have := getD_le_of_vecs hσ (i.val - roleCount x.r.c.kind * x.r.p.J)
          have h2 := nbl_le_self' (σ.getD (i.val - roleCount x.r.c.kind * x.r.p.J) 0)
          simp only [Int.natAbs_natCast]
          rcases this with h | h <;> omega
      · unfold Wb ResB
        refine le_trans ?_ (Nat.le_add_right _ _)
        have hR : roleCount x.r.c.kind * x.r.p.J + roleCount x.r.c.kind ≤ 2 * x.r.c.n + 4 := by nlinarith
        have a1 : (x.r.p.e + 1) ^ 2 ≤ (2 * x.r.c.n + 3) ^ 2 := Nat.pow_le_pow_left he' 2
        have a2 : (q + 1) * (2 * Lf x.r.c.n (cellInput x.r).length + (cellInput x.r).length + 4 + (x.r.c.n + 1) + 7) ≤
            (x.r.c.n + 1) * (2 * Lf x.r.c.n (cellInput x.r).length + (cellInput x.r).length + x.r.c.n + 12) :=
          Nat.mul_le_mul (by omega) (by omega)
        have a3 := Nat.mul_le_mul hR (Nat.add_le_add_right a2 1)
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 a1) (by omega)
  · rename_i r j hid
    have hmem := x.mem
    rw [hid] at hmem
    obtain ⟨hr, hj⟩ := mem_digit hmem
    apply le_trans (tabSize_le_of _ (Wb x.r.c.n (cellInput x.r).length) ?_ ?_ ?_ ?_) (le_refl _)
    · show (circ x.r.c r).gates.length ≤ 4 * x.r.c.n ^ 4
      have := hm r; omega
    · show 2 * (circ x.r.c r).gates.length ≤ 4 * x.r.c.n ^ 4
      have := hm r; omega
    · exact hB
    · show fw (momF (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt r (some j)) ≤ _
      have h1 := fw_digO x.r.c x.r.p x.r.wt _ hcoef hcirc hrate hm (V := 2 * (circ x.r.c r).gates.length) 0 r j hr hj
      have h2 := fw_digO x.r.c x.r.p x.r.wt _ hcoef hcirc hrate hm (V := 2 * (circ x.r.c r).gates.length)
        (circ x.r.c r).gates.length r j hr hj
      have h3 := nbl_le_self' (2 * x.r.p.k)
      simp only [momF, fw]
      unfold Wb MomB
      refine le_trans ?_ (Nat.le_add_left _ _)
      have h4 : (2 * x.r.p.k + 1) * (fw (digO (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt 0 r j) +
          fw (digO (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt (circ x.r.c r).gates.length r j) + 1 + 1)
          ≤ (2 * x.r.c.n + 1) * (4 * Lf x.r.c.n (cellInput x.r).length + 4 * (cellInput x.r).length + 12) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  · rename_i r hid
    have hmem := x.mem
    rw [hid] at hmem
    have hr := mem_phi hmem
    apply le_trans (tabSize_le_of _ (Wb x.r.c.n (cellInput x.r).length) ?_ ?_ ?_ ?_) (le_refl _)
    · show (circ x.r.c r).gates.length ≤ 4 * x.r.c.n ^ 4
      have := hm r; omega
    · show 2 * (circ x.r.c r).gates.length ≤ 4 * x.r.c.n ^ 4
      have := hm r; omega
    · exact hB
    · show fw (momF (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt r none) ≤ _
      have h1 := fw_phiO x.r.c x.r.p x.r.wt _ hcoef hcirc hrate hM1 hA hm hJ1 (V := 2 * (circ x.r.c r).gates.length) 0 r hr
      have h2 := fw_phiO x.r.c x.r.p x.r.wt _ hcoef hcirc hrate hM1 hA hm hJ1 (V := 2 * (circ x.r.c r).gates.length)
        (circ x.r.c r).gates.length r hr
      have h3 := nbl_le_self' (2 * x.r.p.k)
      simp only [momF, fw]
      unfold Wb MomB
      refine le_trans ?_ (Nat.le_add_left _ _)
      have h4 : (2 * x.r.p.k + 1) * (fw (phiO (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt 0 r) +
          fw (phiO (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt (circ x.r.c r).gates.length r) + 1 + 1)
          ≤ (2 * x.r.c.n + 1) * (4 * Lf x.r.c.n (cellInput x.r).length + 4 * (cellInput x.r).length + 12) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega

/-! ## The class -/

section Class
variable {B1 B2 cT : ℕ}

open NearCubicGates.Close.CheckedPCPP

theorem poly_Tb : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => Tb x.r.c.n (cellInput x.r).length) := by
  have hn : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => x.r.c.n) := PolyB.size
  obtain ⟨C0, e0, h0⟩ := Cells.cellInput_length_le B1 B2 cT
  have hΛ : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => (cellInput x.r).length) := ⟨C0, e0, fun x => h0 x.r⟩
  have hLf : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => Lf x.r.c.n (cellInput x.r).length) :=
    (PolyB.add (PolyB.mul (PolyB.mul (PolyB.const 2) (PolyB.pow hn 4)) (PolyB.add hΛ (PolyB.const 6)))
      (PolyB.const 2)).mono fun x => le_refl _
  have hRes : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => ResB x.r.c.n (cellInput x.r).length) :=
    (PolyB.mul (PolyB.mul (PolyB.const 3) (PolyB.pow (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 3)) 2))
      (PolyB.add (PolyB.mul (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 4))
        (PolyB.add (PolyB.mul (PolyB.add hn (PolyB.const 1))
          (PolyB.add (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) hLf) hΛ) hn) (PolyB.const 12)))
          (PolyB.const 1))) (PolyB.const 6))).mono fun x => le_refl _
  have hMom : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => MomB x.r.c.n (cellInput x.r).length) :=
    (PolyB.add (PolyB.add (PolyB.mul (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 1))
      (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 4) hLf) (PolyB.mul (PolyB.const 4) hΛ)) (PolyB.const 12)))
      (PolyB.mul (PolyB.const 2) hn)) (PolyB.const 1)).mono fun x => le_refl _
  have hW : PolyB (fun x : TabCallReq B1 B2 cT => x.r.c.n) (fun x => Wb x.r.c.n (cellInput x.r).length) :=
    (PolyB.add hRes hMom).mono fun x => le_refl _
  have hn4 := PolyB.mul (PolyB.const 4) (PolyB.pow hn 4)
  exact (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add hn hn4)
    (PolyB.mul (PolyB.mul (PolyB.const 4) hn) (PolyB.add hn (PolyB.const 1)))) hn4)
    (PolyB.add (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add hn4 (PolyB.const 1))) (PolyB.const 1))
      (PolyB.add (PolyB.mul (PolyB.const 2) hW) (PolyB.const 3)))
      (PolyB.mul hW (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) hW)
        (PolyB.mul (PolyB.const 2) (PolyB.add hn4 (PolyB.const 1)))) (PolyB.const 30))))) hW) hW)
    (PolyB.const 1)) (PolyB.const 0)).mono fun x => by unfold Tb; omega

end Class

end NearCubicGates.Close.CounterMachine.TabCallSizes

namespace NearCubicGates.Close.CounterMachine

theorem tabCallSize (B1 B2 cT : ℕ) : TabCallSize B1 B2 cT := by
  obtain ⟨C, e, h⟩ := TabCallSizes.poly_Tb (B1 := B1) (B2 := B2) (cT := cT)
  exact ⟨C, e, fun x => (TabCallSizes.tab_le x).trans (h x)⟩

end NearCubicGates.Close.CounterMachine
