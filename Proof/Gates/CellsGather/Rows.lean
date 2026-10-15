import Proof.Gates.CellsGather.Keys
import Proof.Gates.CellsSys.Math

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih (fun a ha => h a (by simp [ha]))]

section R
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

theorem kmod_getD (v : List ℕ) (q : ℕ) (rj : Role c × Fin p.J) :
    (kmod c p wt y v q).getD (rj.1.val * p.J + rj.2.val) 0 = (kappaOf c p wt y v rj % (q : ℤ)).toNat := by
  unfold kmod
  rw [List.getD_eq_getElem _ _ (by simp [idx_lt c p rj]), List.getElem_ofFn]
  simp only [rjOf_idx]

theorem kmod_mem (v : List ℕ) (q : ℕ) (hq : 0 < q) : kmod c p wt y v q ∈ vecs q (roleCount c.kind * p.J) := by
  rw [mem_vecs_iff]
  refine ⟨by simp [kmod], fun k hk => ?_⟩
  have hk' : k < nDig c p := by simpa [kmod] using hk
  rw [List.getD_eq_getElem _ _ hk]
  unfold kmod
  rw [List.getElem_ofFn]
  have key : ∀ z : ℤ, (z % (q : ℤ)).toNat < q := fun z => by
    have h1 := Int.emod_nonneg z (by omega : (q : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos z (by omega : (0 : ℤ) < q)
    omega
  exact key _

theorem jointCount_congr (q : ℕ) (part : Option Bool) (κ κ' : Role c × Fin p.J → ℤ) (σ : Role c → ℤ)
    (h : ∀ rj, κ rj ≡ κ' rj [ZMOD (q : ℤ)]) :
    jointCount c p wt q part y κ σ = jointCount c p wt q part y κ' σ := by
  unfold jointCount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun rj => (h2 rj).trans (h rj), h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun rj => (h2 rj).trans (h rj).symm, h3⟩

theorem reqValue_query (part : Option Bool) (v : List ℕ) (q : ℕ) (hq : 0 < q) (σl : List ℕ) :
    reqValue c p wt y (ReqId.residue part q (kmod c p wt y v q) σl) =
      jointCount c p wt q part y (kappaOf c p wt y v) (fun r => (σl.getD r.val 0 : ℤ)) := by
  simp only [reqValue]
  apply jointCount_congr
  intro rj
  rw [kmod_getD]
  have h1 := Int.emod_nonneg (kappaOf c p wt y v rj) (by omega : (q : ℤ) ≠ 0)
  rw [Int.toNat_of_nonneg h1]
  exact Int.mod_modEq _ _

theorem prime_pos_of {cT : ℕ} (hs : Spec cT (header c) p) (q : ℕ) (hq : q ∈ p.primes.sort (· ≤ ·)) : 0 < q :=
  (primes_prime hs q (by simpa using hq)).pos

/-- **The table value at each query key is the joint count of `rowVals`.** -/
theorem rowKeys_map_F {cT : ℕ} (hs : Spec cT (header c) p) :
    (rowKeys c p wt y).map (F c p wt y) = rowVals c p wt y := by
  unfold rowKeys rowVals
  simp only [List.map_flatMap, List.map_map]
  refine flatMap_congr' (fun part hpart => flatMap_congr' (fun v _ => flatMap_congr' (fun q hq => ?_)))
  refine List.map_congr_left (fun σl hσl => ?_)
  have hq0 := prime_pos_of c p hs q hq
  simp only [Function.comp]
  rw [F_key c p wt hs y _ ((mem_reqIds_residue c p).2 ⟨hpart, hq, kmod_mem c p wt y v q hq0, hσl⟩),
    reqValue_query c p wt y part v q hq0 σl]

/-- Every query key is a request key. -/
theorem rowKeys_mem {cT : ℕ} (hs : Spec cT (header c) p) (k : ℕ) (hk : k ∈ rowKeys c p wt y) :
    ∃ id ∈ reqIds c p, reqKey c p id = k := by
  unfold rowKeys at hk
  simp only [List.mem_flatMap, List.mem_map] at hk
  obtain ⟨part, hpart, v, _, q, hq, σl, hσl, rfl⟩ := hk
  exact ⟨_, (mem_reqIds_residue c p).2 ⟨hpart, hq, kmod_mem c p wt y v q (prime_pos_of c p hs q hq), hσl⟩, rfl⟩

theorem rowKeys_length : (rowKeys c p wt y).length = (rowVals c p wt y).length := by
  unfold rowKeys rowVals
  simp only [List.length_flatMap, List.length_map]

theorem vecs_card (q d : ℕ) : (vecs q d).length = q ^ d := by
  rw [vecs_eq_vecsM, vecsM_length, prod_replicate]

theorem sum_le_len_mul {α : Type} (l : List α) (f : α → ℕ) (M : ℕ) (h : ∀ a ∈ l, f a ≤ M) :
    (l.map f).sum ≤ l.length * M := by
  have := List.sum_le_card_nsmul (l.map f) M (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; exact h a ha)
  simpa using this

theorem parts_len : (parts c).length ≤ 2 := by unfold parts; split <;> simp

theorem nP_le {cT : ℕ} (hs : Spec cT (header c) p) : (p.primes.sort (· ≤ ·)).length ≤ p.P + 1 := by
  rw [Finset.length_sort, hs.primes_eq]
  unfold dyadicPrimes
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem wWin_le_P {cT : ℕ} (hs : Spec cT (header c) p) : wWin p ≤ p.P := by
  have := hs.hE_eq; unfold wWin; omega

/-- **The number of queries.** -/
theorem rowKeys_le {cT : ℕ} (hs : Spec cT (header c) p) :
    (rowKeys c p wt y).length ≤ 2 * wWin p ^ nDig c p * ((p.P + 1) * p.P ^ 2) := by
  have hrc := roleCount_le_two c
  have hP1 : 1 ≤ p.P := by have := hs.P_large; omega
  unfold rowKeys
  simp only [List.length_flatMap, List.length_map, vecs_card]
  have hq : ∀ q ∈ p.primes.sort (· ≤ ·), q ^ roleCount c.kind ≤ p.P ^ 2 := by
    intro q hq
    have h1 : q ≤ p.P := primes_le hs q (by simpa using hq)
    calc q ^ roleCount c.kind ≤ p.P ^ roleCount c.kind := Nat.pow_le_pow_left h1 _
      _ ≤ p.P ^ 2 := Nat.pow_le_pow_right hP1 hrc
  have hS : ∀ v ∈ vecsM (List.replicate (nDig c p) (wWin p)),
      ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum ≤ (p.P + 1) * p.P ^ 2 :=
    fun _ _ => (sum_le_len_mul _ _ _ hq).trans (Nat.mul_le_mul_right _ (nP_le c p hs))
  have hV : ∀ part ∈ parts c, ((vecsM (List.replicate (nDig c p) (wWin p))).map fun v =>
      ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum).sum ≤
        wWin p ^ nDig c p * ((p.P + 1) * p.P ^ 2) := by
    intro _ _
    have := sum_le_len_mul _ _ _ hS
    rwa [vecsM_length, prod_replicate] at this
  have := sum_le_len_mul _ _ _ hV
  calc _ ≤ _ := this
    _ ≤ 2 * (wWin p ^ nDig c p * ((p.P + 1) * p.P ^ 2)) := Nat.mul_le_mul_right _ (parts_len c)
    _ = _ := by ring

theorem rowKeys_le_n {cT : ℕ} (hs : Spec cT (header c) p) :
    (rowKeys c p wt y).length ≤ 2 * wWin p ^ nDig c p * (c.n + 1) ^ 3 := by
  have hP := P_le_n c p hs
  refine (rowKeys_le c p wt y hs).trans (Nat.mul_le_mul_left _ ?_)
  calc (p.P + 1) * p.P ^ 2 ≤ (c.n + 1) * (c.n + 1) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
    _ = (c.n + 1) ^ 3 := by ring

theorem P1_lt_keyBits (p : Params) : p.P + 1 < 2 ^ keyBits p := by
  unfold keyBits
  exact lt_of_le_of_lt (by omega) (Nat.lt_size_self (p.P + p.J + 3))

/-- **The tags fit:** fewer queries than `2^{keyW}`. -/
theorem rowKeys_lt {cT : ℕ} (hs : Spec cT (header c) p) : (rowKeys c p wt y).length < 2 ^ keyW c p := by
  have hrc := roleCount_pos c.kind
  have hW := wWin_le_P c p hs
  have hB := P1_lt_keyBits p
  set B := p.P + 1 with hBdef
  have h1 : 2 * wWin p ^ nDig c p * ((p.P + 1) * p.P ^ 2) ≤ B ^ (nDig c p + 4) := by
    have e1 : wWin p ^ nDig c p ≤ B ^ nDig c p := Nat.pow_le_pow_left (by omega) _
    have e2 : p.P ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) _
    have e3 : 2 ≤ B := by have := hs.P_large; omega
    calc 2 * wWin p ^ nDig c p * ((p.P + 1) * p.P ^ 2) = 2 * wWin p ^ nDig c p * B * p.P ^ 2 := by
          rw [hBdef]; ring
      _ ≤ B * B ^ nDig c p * B * B ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul e3 e1)) e2
      _ = B ^ (nDig c p + 4) := by ring
  have h2 : B ^ (nDig c p + 4) < (2 ^ keyBits p) ^ (nDig c p + 4) :=
    Nat.pow_lt_pow_left hB (by omega)
  have h3 : (2 ^ keyBits p) ^ (nDig c p + 4) ≤ 2 ^ keyW c p := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    unfold keyW keyLen nDig
    apply Nat.mul_le_mul_left
    nlinarith
  exact lt_of_le_of_lt ((rowKeys_le c p wt y hs).trans h1) (lt_of_lt_of_le h2 h3)

end R

end NearCubicGates.Close.Cells.GatherPhase
