import Proof.Gates.CounterMachine.TabCallSpec
import Proof.Gates.CounterMachine.CellTablesSpec
import Proof.Gates.CounterMachine.CellTablesBodySpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTablesValue

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

/-- The prime of a residue request lifts the inner sum: `2^k < q^e`, `q` prime, `e ≥ 1`. -/
theorem lift_facts (r : CellReq B1 B2 cT) {q : ℕ} (hq : q ∈ r.p.primes) :
    Nat.Prime q ∧ 1 ≤ r.p.e ∧ 2 ^ r.p.k < q ^ r.p.e := by
  have hs := cellReq_spec r
  have hq' : q ∈ dyadicPrimes r.p.P := by rw [← hs.primes_eq]; exact hq
  rw [mem_dyadicPrimes] at hq'
  obtain ⟨hle, hpr, hlt⟩ := hq'
  obtain ⟨⟨he1, hpass⟩, _, _⟩ := leastUpTo_spec _ _ _ hs.e_eq
  refine ⟨hpr, he1, ?_⟩
  have h1 : r.p.P ^ r.p.e < (2 * q) ^ r.p.e := Nat.pow_lt_pow_left hlt (by omega)
  rw [mul_pow] at h1
  have h2 : 2 ^ (r.p.k + 1 + r.p.e) = 2 ^ (r.p.k + 1) * 2 ^ r.p.e := by rw [pow_add]
  have h3 : 2 ^ (r.p.k + 1) * 2 ^ r.p.e < q ^ r.p.e * 2 ^ r.p.e := by nlinarith
  have h4 : 2 ^ (r.p.k + 1) < q ^ r.p.e := Nat.lt_of_mul_lt_mul_right h3
  have : 2 ^ r.p.k < 2 ^ (r.p.k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- Table (a) through RK: the entry at outer index `i`, reduced mod `q^e`, is the request's value on cell `i`. -/
theorem tabCall_value_res (x : TabCallReq B1 B2 cT) {part : Option Bool} {q : ℕ} {κ σ : List ℕ}
    (h : x.id = .residue part q κ σ) (i : ℕ) :
    (tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i) % ((q ^ x.r.p.e : ℕ) : ℤ)).toNat =
      reqValue x.r.c x.r.p x.r.wt (cellOf x.r.wt.I i) x.id := by
  obtain ⟨r, id, mem⟩ := x
  simp only at h ⊢
  subst h
  obtain ⟨hpr, he, hlift⟩ := lift_facts r (mem_reqIds_residue mem)
  unfold tabCallTab
  dsimp only
  rw [Nat.cast_pow]
  erw [resReq_value _ _ _ _ _ _ _ _ _ _ hpr he hlift i]
  simp [reqValue]

/-- Table (b) through RK: the entry at outer index `i` is the moment on cell `i` (`≥ 0` there). -/
theorem tabCall_value_mom (x : TabCallReq B1 B2 cT) (hx : ∀ part q κ σ, x.id ≠ .residue part q κ σ) (i : ℕ) :
    (tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i)).toNat =
      reqValue x.r.c x.r.p x.r.wt (cellOf x.r.wt.I i) x.id := by
  obtain ⟨r, id, mem⟩ := x
  simp only at hx ⊢
  cases id with
  | residue part q κ σ => exact absurd rfl (hx part q κ σ)
  | digitMoment ro j =>
    unfold tabCallTab; dsimp only
    erw [momReq_value]; rfl
  | phiMoment ro =>
    unfold tabCallTab; dsimp only
    erw [momReq_value]; rfl

theorem recOf_tabCall (x : TabCallReq B1 B2 cT) (QE : ℕ) (res : Bool)
    (hres : ∀ part q κ σ, x.id = .residue part q κ σ → res = true ∧ QE = q ^ x.r.p.e)
    (hmom : (∀ part q κ σ, x.id ≠ .residue part q κ σ) → res = false) (i : ℕ) :
    CellTables.recOf (2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p + valueWidth x.r.c x.r.p))
      (reqKey x.r.c x.r.p x.id * 2 ^ valueWidth x.r.c x.r.p) QE res i (tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i)) =
      cellRec x.r.c x.r.p x.r.wt i x.id := by
  have hval : (if res then (tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i) % (QE : ℤ)).toNat
      else (tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i)).toNat) =
      reqValue x.r.c x.r.p x.r.wt (cellOf x.r.wt.I i) x.id := by
    by_cases hr : ∃ part q κ σ, x.id = .residue part q κ σ
    · obtain ⟨part, q, κ, σ, h⟩ := hr
      obtain ⟨h1, h2⟩ := hres part q κ σ h
      rw [if_pos h1, h2]; exact tabCall_value_res x h i
    · simp only [not_exists] at hr
      rw [if_neg (by rw [hmom hr]; decide)]; exact tabCall_value_mom x hr i
  unfold CellTables.recOf cellRec
  rw [hval, pow_add]
  ring

theorem printerOrder_mem' (s x : ℕ) : x ∈ printerOrder s ↔ x < 2 ^ s := by
  unfold printerOrder
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  have hs : 2 ^ s = 2 ^ ((s + 1) / 2) * 2 ^ (s / 2) := by rw [← pow_add]; congr 1; omega
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    rw [hs]
    have : 2 ^ ((s + 1) / 2) * j + 2 ^ ((s + 1) / 2) ≤ 2 ^ ((s + 1) / 2) * 2 ^ (s / 2) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    omega
  · intro hx
    have hp : 0 < 2 ^ ((s + 1) / 2) := Nat.two_pow_pos _
    refine ⟨x % 2 ^ ((s + 1) / 2), Nat.mod_lt _ hp, x / 2 ^ ((s + 1) / 2), ?_, ?_⟩
    · rw [hs] at hx; exact Nat.div_lt_of_lt_mul hx
    · exact Nat.mod_add_div x _

theorem printerOrder_nodup' (s : ℕ) : (printerOrder s).Nodup := by
  unfold printerOrder
  have hp : 0 < 2 ^ ((s + 1) / 2) := Nat.two_pow_pos _
  rw [List.nodup_flatMap]
  refine ⟨fun i hi => ?_, ?_⟩
  · refine (List.nodup_range).map_on fun a _ b _ h => ?_
    have : 2 ^ ((s + 1) / 2) * a = 2 ^ ((s + 1) / 2) * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hp this
  · refine List.nodup_range.pairwise_of_forall_ne fun i hi i' hi' hne => ?_
    simp only [List.mem_range] at hi hi'
    intro x hx hx'
    simp only [List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, _, rfl⟩ := hx
    obtain ⟨j', _, e⟩ := hx'
    have h1 := congrArg (· % 2 ^ ((s + 1) / 2)) e
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
    exact hne h1.symm

theorem printerOrder_perm' (s : ℕ) : (printerOrder s).Perm (List.range (2 ^ s)) :=
  (List.perm_ext_iff_of_nodup (printerOrder_nodup' s) List.nodup_range).mpr fun x => by
    rw [printerOrder_mem', List.mem_range]

/-- Swapping the two loops of a double `flatMap` permutes the list. -/
theorem flatMap_swap_perm {α β γ : Type} (f : α → β → γ) : ∀ (l1 : List α) (l2 : List β),
    (l1.flatMap fun a => l2.map (f a)).Perm (l2.flatMap fun b => l1.map fun a => f a b)
  | [], l2 => by simp
  | a :: l1, l2 => by
    rw [List.flatMap_cons]
    refine (List.Perm.append_left _ (flatMap_swap_perm f l1 l2)).trans ?_
    simpa using List.map_append_flatMap_perm l2 (f a) (fun b => l1.map fun a => f a b)

theorem insertionSort_eq_of_perm {l1 l2 : List ℕ} (h : l1.Perm l2) :
    l1.insertionSort (· ≤ ·) = l2.insertionSort (· ≤ ·) :=
  ((List.perm_insertionSort _ l1).trans (h.trans (List.perm_insertionSort _ l2).symm)).eq_of_sortedLE
    List.sortedLE_insertionSort List.sortedLE_insertionSort

theorem recs_sort (r : CellReq B1 B2 cT) (L : List ReqId) (hL : L.Perm (reqIds r.c r.p)) :
    (L.flatMap fun id => (printerOrder (r.c.n - r.p.k)).map fun i => cellRec r.c r.p r.wt i id).insertionSort (· ≤ ·) =
      ((List.range (2 ^ cellBits r.wt.I)).flatMap fun i =>
        (reqIds r.c r.p).map (cellRec r.c r.p r.wt i)).insertionSort (· ≤ ·) := by
  apply insertionSort_eq_of_perm
  have hs : cellBits r.wt.I = r.c.n - r.p.k := outerCoords_length r.wt.I (cellReq_hk r)
  rw [hs]
  refine (List.Perm.flatMap_right _ hL).trans ?_
  refine (List.Perm.flatMap_left _ fun id _ => (printerOrder_perm' _).map _).trans ?_
  exact flatMap_swap_perm (fun id i => cellRec r.c r.p r.wt i id) _ _

theorem recs_cellWord (r : CellReq B1 B2 cT) (L : List ReqId) (hL : L.Perm (reqIds r.c r.p)) :
    WordPrograms.recStream (((L.flatMap fun id => (printerOrder (r.c.n - r.p.k)).map fun i =>
      cellRec r.c r.p r.wt i id).insertionSort (· ≤ ·)).map (RepairOrdinary.SignedSortKey.binary (recWidth r.c r.p r.wt))) =
      cellWord r.c r.p r.wt := by
  rw [recs_sort r L hL]; rfl

/-- **F-VAL** (CellTables-SPLIT2). -/
theorem sorted_recs : CellTablesProg.ValSpec := fun r => recs_sort r _ (List.Perm.refl _)

end NearCubicGates.Close.CounterMachine.CellTablesValue
