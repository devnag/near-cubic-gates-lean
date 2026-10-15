import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells

section Gather
variable (Z Z' : ℕ)

/-- Flag, key and payload of a combined record. -/
def gFlag (x : ℕ) : ℕ := x / 2 ^ Z % 2
def gKey (x : ℕ) : ℕ := x / 2 ^ Z / 2
def gPay (x : ℕ) : ℕ := x % 2 ^ Z

/-- A table record and a query record. -/
def tRec (k v : ℕ) : ℕ := (2 * k) * 2 ^ Z + v
def qRec (k t : ℕ) : ℕ := (2 * k + 1) * 2 ^ Z + t

/-- The sweep: remember the last table payload; answer each query `t` with `t·2^{Z'} + last`. -/
def sweep : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: xs, last => if gFlag Z x = 0 then sweep xs (gPay Z x) else (gPay Z x * 2 ^ Z' + last) :: sweep xs last

/-- The last table payload of a list (or `l0`). -/
def lastV (l : List ℕ) (l0 : ℕ) : ℕ := l.foldl (fun acc x => if gFlag Z x = 0 then gPay Z x else acc) l0

theorem sweep_append (A B : List ℕ) (l0 : ℕ) :
    sweep Z Z' (A ++ B) l0 = sweep Z Z' A l0 ++ sweep Z Z' B (lastV Z A l0) := by
  induction A generalizing l0 with
  | nil => simp [sweep, lastV]
  | cons x A ih =>
    simp only [List.cons_append, sweep, lastV, List.foldl_cons]
    split_ifs with h
    · rw [ih]; rfl
    · rw [ih]; simp [lastV]

theorem lastV_snoc (l : List ℕ) (z l0 : ℕ) :
    lastV Z (l ++ [z]) l0 = if gFlag Z z = 0 then gPay Z z else lastV Z l l0 := by
  simp [lastV, List.foldl_append]

theorem tRec_flag (k v : ℕ) (hv : v < 2 ^ Z) : gFlag Z (tRec Z k v) = 0 := by
  unfold gFlag tRec
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]; simp

theorem tRec_key (k v : ℕ) (hv : v < 2 ^ Z) : gKey Z (tRec Z k v) = k := by
  unfold gKey tRec
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]; omega

theorem tRec_pay (k v : ℕ) (hv : v < 2 ^ Z) : gPay Z (tRec Z k v) = v := by
  unfold gPay tRec; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem qRec_flag (k t : ℕ) (ht : t < 2 ^ Z) : gFlag Z (qRec Z k t) = 1 := by
  unfold gFlag qRec
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt ht, zero_add]; omega

theorem qRec_key (k t : ℕ) (ht : t < 2 ^ Z) : gKey Z (qRec Z k t) = k := by
  unfold gKey qRec
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt ht, zero_add]; omega

theorem qRec_pay (k t : ℕ) (ht : t < 2 ^ Z) : gPay Z (qRec Z k t) = t := by
  unfold gPay qRec; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem gKey_mono {x y : ℕ} (h : x ≤ y) : gKey Z x ≤ gKey Z y := by
  unfold gKey; exact Nat.div_le_div_right (Nat.div_le_div_right h)

/-- The last table payload is that of the largest table record. -/
theorem lastV_spec (l : List ℕ) (l0 : ℕ) (hl : l.Pairwise (· ≤ ·)) (hex : ∃ y ∈ l, gFlag Z y = 0) :
    ∃ u ∈ l, gFlag Z u = 0 ∧ lastV Z l l0 = gPay Z u ∧ ∀ y ∈ l, gFlag Z y = 0 → y ≤ u := by
  induction l using List.reverseRecOn with
  | nil => obtain ⟨y, hy, _⟩ := hex; simp at hy
  | append_singleton l z ih =>
    rw [List.pairwise_append] at hl
    rw [lastV_snoc]
    by_cases hz : gFlag Z z = 0
    · refine ⟨z, by simp, hz, by rw [if_pos hz], fun y hy _ => ?_⟩
      rcases List.mem_append.mp hy with hy | hy
      · exact hl.2.2 y hy z (by simp)
      · simp at hy; rw [hy]
    · obtain ⟨y, hy, hy0⟩ := hex
      have hyl : y ∈ l := by
        rcases List.mem_append.mp hy with hy | hy
        · exact hy
        · simp at hy; subst hy; exact absurd hy0 hz
      obtain ⟨u, hu, hu0, hlu, hmax⟩ := ih hl.1 ⟨y, hyl, hy0⟩
      refine ⟨u, List.mem_append_left _ hu, hu0, by rw [if_neg hz, hlu], fun y' hy' hy'0 => ?_⟩
      rcases List.mem_append.mp hy' with hy' | hy'
      · exact hmax y' hy' hy'0
      · simp at hy'; subst hy'; exact absurd hy'0 hz

/-- **The sweep answers every query with its key's table value.** Every flag-`0` record of `S` is a table record of
the functional table `F` (`gPay x = F (gKey x)`); every query's key has a table record that sorts before it. -/
theorem sweep_sorted (F : ℕ → ℕ) (l0 : ℕ) :
    ∀ S : List ℕ, S.Pairwise (· ≤ ·) → (∀ x ∈ S, gFlag Z x = 0 → gPay Z x = F (gKey Z x)) →
      (∀ x ∈ S, gFlag Z x ≠ 0 → ∃ y ∈ S, gFlag Z y = 0 ∧ y < x ∧ gKey Z y = gKey Z x) →
      sweep Z Z' S l0 = (S.filter fun x => gFlag Z x ≠ 0).map fun x => gPay Z x * 2 ^ Z' + F (gKey Z x) := by
  intro S
  induction S using List.reverseRecOn with
  | nil => intros; simp [sweep]
  | append_singleton S z ih =>
    intro hS hT hQ
    have hS' := (List.pairwise_append.mp hS)
    rw [sweep_append, ih hS'.1 (fun x hx => hT x (List.mem_append_left _ hx)) ?_, List.filter_append,
      List.map_append]
    · congr 1
      simp only [sweep, List.filter_cons, List.filter_nil]
      by_cases hz : gFlag Z z = 0
      · simp [hz, sweep]
      · simp only [hz, if_false, decide_true, if_true, ne_eq, not_false_eq_true, decide_eq_true_eq,
          List.map_cons, List.map_nil, sweep, List.cons.injEq, and_true]
        congr 1
        obtain ⟨y, hy, hy0, hyz, hyk⟩ := hQ z (by simp) hz
        have hyS : y ∈ S := by
          rcases List.mem_append.mp hy with h | h
          · exact h
          · simp at h; omega
        obtain ⟨u, hu, hu0, hlu, hmax⟩ := lastV_spec Z S l0 hS'.1 ⟨y, hyS, hy0⟩
        rw [hlu, hT u (List.mem_append_left _ hu) hu0]
        have h1 := gKey_mono Z (hmax y hyS hy0)
        have h2 := gKey_mono Z (hS'.2.2 u hu z (by simp))
        rw [show gKey Z u = gKey Z z by omega]
    · intro x hx hx0
      obtain ⟨y, hy, hy0, hyx, hyk⟩ := hQ x (List.mem_append_left _ hx) hx0
      refine ⟨y, ?_, hy0, hyx, hyk⟩
      rcases List.mem_append.mp hy with h | h
      · exact h
      · simp at h; subst h
        have := hS'.2.2 x hx y (by simp)
        omega

/-- The answer record of a query. -/
def aRec (F : ℕ → ℕ) (q : ℕ × ℕ) : ℕ := q.2 * 2 ^ Z' + F q.1

theorem tagged_sorted (F : ℕ → ℕ) (hF : ∀ k, F k < 2 ^ Z') :
    ∀ Qs : List (ℕ × ℕ), (Qs.map Prod.snd).Pairwise (· < ·) → (Qs.map (aRec Z' F)).Pairwise (· ≤ ·) := by
  intro Qs h
  induction Qs with
  | nil => simp
  | cons q Qs ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at h ⊢
    refine ⟨?_, ih h.2⟩
    rintro _ ⟨q', hq', rfl⟩
    have hlt := h.1 q'.2 ⟨q', hq', rfl⟩
    unfold aRec
    have h1 := hF q.1
    have : q.2 * 2 ^ Z' + 2 ^ Z' ≤ q'.2 * 2 ^ Z' := by
      have := Nat.mul_le_mul_right (2 ^ Z') (show q.2 + 1 ≤ q'.2 by omega); rw [Nat.add_mul, one_mul] at this
      exact this
    omega

/-- **Gathering by sorting.** The table `T` (key, value) is functional (`v = F k`), every query key has a table
entry, values and tags fit `Z` bits, tags increase. Sort the combined records, sweep, sort the answers: the result
is `t·2^{Z'} + F k` for every query `(k, t)`, in query order. -/
theorem gather_eq (F : ℕ → ℕ) (hF : ∀ k, F k < 2 ^ Z') (T Qs : List (ℕ × ℕ)) (l0 : ℕ)
    (hTv : ∀ e ∈ T, e.2 < 2 ^ Z ∧ e.2 = F e.1) (hQt : ∀ q ∈ Qs, q.2 < 2 ^ Z ∧ ∃ e ∈ T, e.1 = q.1)
    (hinc : (Qs.map Prod.snd).Pairwise (· < ·)) :
    (sweep Z Z' ((T.map (fun e => tRec Z e.1 e.2) ++ Qs.map (fun q => qRec Z q.1 q.2)).insertionSort (· ≤ ·))
      l0).insertionSort (· ≤ ·) = Qs.map (aRec Z' F) := by
  set X := T.map (fun e => tRec Z e.1 e.2) ++ Qs.map (fun q => qRec Z q.1 q.2) with hX
  set S := X.insertionSort (· ≤ ·) with hS
  have hperm : S.Perm X := List.perm_insertionSort _ _
  have hmem : ∀ x, x ∈ S ↔ x ∈ X := fun x => hperm.mem_iff
  have hsort : S.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hsw := sweep_sorted Z Z' F l0 S hsort (fun x hx hx0 => by
      rw [hmem, hX, List.mem_append, List.mem_map, List.mem_map] at hx
      rcases hx with ⟨e, he, rfl⟩ | ⟨q, hq, rfl⟩
      · have := hTv e he
        rw [tRec_pay Z _ _ this.1, tRec_key Z _ _ this.1]; exact this.2
      · rw [qRec_flag Z _ _ (hQt q hq).1] at hx0; omega)
    (fun x hx hx0 => by
      rw [hmem, hX, List.mem_append, List.mem_map, List.mem_map] at hx
      rcases hx with ⟨e, he, rfl⟩ | ⟨q, hq, rfl⟩
      · exact absurd (tRec_flag Z _ _ (hTv e he).1) hx0
      · obtain ⟨ht, e, he, hk⟩ := hQt q hq
        have hv := (hTv e he).1
        refine ⟨tRec Z e.1 e.2, (hmem _).2 (List.mem_append_left _ (List.mem_map_of_mem he)), tRec_flag Z _ _ hv,
          ?_, by rw [tRec_key Z _ _ hv, qRec_key Z _ _ ht, hk]⟩
        unfold tRec qRec; rw [hk]
        have : (2 * q.1) * 2 ^ Z + 2 ^ Z = (2 * q.1 + 1) * 2 ^ Z := by ring
        omega)
  have hfilt : (S.filter fun x => gFlag Z x ≠ 0).Perm (Qs.map fun q => qRec Z q.1 q.2) := by
    refine (hperm.filter _).trans ?_
    rw [hX, List.filter_append]
    have h1 : (T.map (fun e => tRec Z e.1 e.2)).filter (fun x => gFlag Z x ≠ 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      simp [tRec_flag Z _ _ (hTv e he).1]
    have h2 : (Qs.map (fun q => qRec Z q.1 q.2)).filter (fun x => gFlag Z x ≠ 0) =
        Qs.map (fun q => qRec Z q.1 q.2) := by
      rw [List.filter_eq_self]
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      simp [qRec_flag Z _ _ (hQt q hq).1]
    rw [h1, h2, List.nil_append]
  have hres : (sweep Z Z' S l0).Perm (Qs.map (aRec Z' F)) := by
    rw [hsw]
    refine (hfilt.map _).trans ?_
    rw [List.map_map]
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro q hq
    simp only [Function.comp, aRec]
    rw [qRec_pay Z _ _ (hQt q hq).1, qRec_key Z _ _ (hQt q hq).1]
  exact List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) (tagged_sorted Z' F hF Qs hinc)
    ((List.perm_insertionSort _ _).trans hres)

end Gather

end NearCubicGates.Close.Cells
