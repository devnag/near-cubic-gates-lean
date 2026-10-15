import Proof.MachineModel.OrdinaryBoundedCounter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Interp
open NearCubicWires.RepairOrdinary.RadixSemantics (value value_lt)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.RepairOrdinary.BoundedCounter (binary_of_value)

/-! ## The print -/

/-- The value of a monomial list at an assignment: the parity of its satisfied monomials (S0's `F2Poly.eval`). -/
def evalP (p : List (List ℕ)) (ρ : ℕ → Bool) : Bool := p.foldl (fun acc m => xor acc (m.all ρ)) false

/-- The point `1_T` on the coordinates `0, …, L−1`, low index first. -/
def pointOf (L : ℕ) (T : List ℕ) : List Bool := (List.range L).map fun i => decide (i ∈ T)

/-- The interpolation coefficient `c_S = ⊕_{T ⊆ S} f(1_T)`, over the sublists of `S` (bit `k` of the sub-bitmap
counter selects `S_k`). -/
def subsetX (f : List Bool → Bool) (L : ℕ) (S : List ℕ) : Bool :=
  S.sublists.foldl (fun acc T => xor acc (f (pointOf L T))) false

/-- The coordinates of a bitmap (low index first), increasing. -/
def supp (bs : List Bool) : List ℕ := (List.range bs.length).filter fun i => bs.getD i false

/-- **The supports of size `≤ d` on `Z_0, …, Z_{L−1}`**, in the printer's order: their bitmaps `X < 2^L`,
increasing. -/
def monos (L d : ℕ) : List (List ℕ) :=
  (List.range (2 ^ L)).filterMap fun X => if (supp (binary L X)).length ≤ d then some (supp (binary L X)) else none

/-- **The interpolation print** of `f`: the supports whose coefficient is one. -/
def interpPrint (f : List Bool → Bool) (L d : ℕ) : List (List ℕ) := (monos L d).filter (subsetX f L)

/-! ## Bits as `𝔽₂` values -/

/-- A bit as an element of `𝔽₂`. -/
def bz (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem bz_true : bz true = 1 := rfl
@[simp] theorem bz_false : bz false = 0 := rfl
theorem bz_xor (a b : Bool) : bz (xor a b) = bz a + bz b := by cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem foldl_xor_bz {α : Type} (l : List α) (g : α → Bool) (acc : Bool) :
    bz (l.foldl (fun a x => xor a (g x)) acc) = bz acc + (l.map fun x => bz (g x)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, bz_xor, List.map_cons, List.sum_cons]; ring

theorem bz_evalP (p : List (List ℕ)) (ρ : ℕ → Bool) : bz (evalP p ρ) = (p.map fun m => bz (m.all ρ)).sum := by
  unfold evalP; rw [foldl_xor_bz]; simp

theorem bz_subsetX (f : List Bool → Bool) (L : ℕ) (S : List ℕ) :
    bz (subsetX f L S) = (S.sublists.map fun T => bz (f (pointOf L T))).sum := by
  unfold subsetX; rw [foldl_xor_bz]; simp

theorem sum_filter_bz {α : Type} (l : List α) (P : α → Bool) (g : α → ZMod 2) :
    ((l.filter P).map g).sum = (l.map fun a => bz (P a) * g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : P a <;> simp [h, ih]

theorem sum_map_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → ZMod 2) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem sum_comm_list {α β : Type} (l₁ : List α) (l₂ : List β) (g : α → β → ZMod 2) :
    (l₁.map fun a => (l₂.map fun b => g a b).sum).sum = (l₂.map fun b => (l₁.map fun a => g a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, ← List.sum_map_add]

/-! ## The Boolean-lattice parity -/

theorem subset_insert_notin {A X : Finset ℕ} {a : ℕ} (ha : a ∉ A) : A ⊆ insert a X ↔ A ⊆ X := by
  constructor
  · intro h x hx
    rcases Finset.mem_insert.mp (h hx) with h1 | h1
    · exact absurd (h1 ▸ hx) ha
    · exact h1
  · intro h
    exact h.trans (Finset.subset_insert a X)

theorem subset_insert_erase {A X : Finset ℕ} {a : ℕ} : A ⊆ insert a X ↔ A.erase a ⊆ X := by
  constructor
  · intro h x hx
    rw [Finset.mem_erase] at hx
    rcases Finset.mem_insert.mp (h hx.2) with h1 | h1
    · exact absurd h1 hx.1
    · exact h1
  · intro h x hx
    rw [Finset.mem_insert]
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (h (Finset.mem_erase.mpr ⟨hxa, hx⟩))

theorem zmod2_add_self (y : ZMod 2) : y + y = 0 := by
  fin_cases y <;> decide

/-- **The Boolean-lattice parity**: among the sublists `T` of a duplicate-free `S`, an odd number contain `A` exactly
when `A` is all of `S` (the interval `[A, S]` has `2^{|S∖A|}` elements). -/
theorem sublists_parity : ∀ (S : List ℕ) (A : Finset ℕ), S.Nodup →
    (S.sublists.map fun T => bz (decide (A ⊆ T.toFinset))).sum = bz (decide (A = S.toFinset)) := by
  intro S
  induction S with
  | nil =>
    intro A _
    by_cases hA : A = ∅
    · subst hA; simp
    · simp [hA, Finset.subset_empty]
  | cons a l ih =>
    intro A hnd
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    have hl : l.Nodup := (List.nodup_cons.mp hnd).2
    have hsub : ∀ x ∈ l.sublists, a ∉ x := fun x hx hax =>
      ha ((List.mem_sublists.mp hx).subset hax)
    rw [List.sublists_cons, List.bind_eq_flatMap, sum_map_flatMap]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.toFinset_cons]
    by_cases haA : a ∈ A
    · have e : ∀ x ∈ l.sublists, bz (decide (A ⊆ x.toFinset)) + bz (decide (A ⊆ insert a x.toFinset)) =
          bz (decide (A.erase a ⊆ x.toFinset)) := by
        intro x hx
        have h0 : ¬ A ⊆ x.toFinset := fun h => hsub x hx (List.mem_toFinset.mp (h haA))
        simp only [h0, decide_false, bz_false, zero_add, subset_insert_erase]
      rw [List.map_congr_left e, ih (A.erase a) hl]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro h
        rw [← h, Finset.insert_erase haA]
      · intro h
        rw [h, Finset.erase_insert (fun h' => ha (List.mem_toFinset.mp h'))]
    · have e : ∀ x ∈ l.sublists, bz (decide (A ⊆ x.toFinset)) + bz (decide (A ⊆ insert a x.toFinset)) = 0 := by
        intro x _
        rw [decide_eq_decide.mpr (subset_insert_notin haA), zmod2_add_self]
      rw [List.map_congr_left e]
      have hne : A ≠ insert a l.toFinset := fun h => haA (h ▸ Finset.mem_insert_self a _)
      simp [hne]

/-! ## The enumeration -/

theorem supp_pairwise (bs : List Bool) : (supp bs).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem mem_supp {bs : List Bool} {i : ℕ} : i ∈ supp bs ↔ i < bs.length ∧ bs.getD i false = true := by
  simp [supp]

theorem supp_lt {bs : List Bool} {i : ℕ} (h : i ∈ supp bs) : i < bs.length := (mem_supp.mp h).1

/-- A bitmap is determined by its support and its length. -/
theorem getD_of_supp (bs : List Bool) {i : ℕ} (hi : i < bs.length) : bs.getD i false = decide (i ∈ supp bs) := by
  by_cases h : bs.getD i false = true
  · rw [h, decide_eq_true (mem_supp.mpr ⟨hi, h⟩)]
  · have h' : bs.getD i false = false := by simpa using h
    rw [h', decide_eq_false (fun hm => h (mem_supp.mp hm).2)]

theorem eq_of_supp_eq {bs bs' : List Bool} (hl : bs.length = bs'.length) (h : supp bs = supp bs') : bs = bs' := by
  apply List.ext_getElem hl
  intro i h1 h2
  have e1 := getD_of_supp bs h1
  have e2 := getD_of_supp bs' h2
  rw [List.getD_eq_getElem _ _ h1] at e1
  rw [List.getD_eq_getElem _ _ h2] at e2
  rw [e1, e2, h]

/-- Every printed support is strictly increasing, on the coordinates `< L`, of size `≤ d`. -/
theorem mem_monos {L d : ℕ} {S : List ℕ} (h : S ∈ monos L d) :
    S.Pairwise (· < ·) ∧ (∀ i ∈ S, i < L) ∧ S.length ≤ d := by
  obtain ⟨X, _, hX⟩ := List.mem_filterMap.mp h
  split_ifs at hX with hd
  cases hX
  exact ⟨supp_pairwise _, fun i hi => by simpa using supp_lt hi, hd⟩

/-- The bitmap of a set of coordinates `< L`. -/
def bitmapOf (L : ℕ) (A : Finset ℕ) : List Bool := (List.range L).map fun i => decide (i ∈ A)

theorem supp_bitmapOf (L : ℕ) (A : Finset ℕ) (hA : ∀ i ∈ A, i < L) : (supp (bitmapOf L A)).toFinset = A := by
  ext i
  simp only [List.mem_toFinset, mem_supp, bitmapOf, List.length_map, List.length_range]
  constructor
  · rintro ⟨hi, h⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] at h
    simpa using h
  · intro h
    have hi := hA i h
    refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    simpa using h

/-- **Every support of size `≤ d` on the coordinates `< L` is printed.** -/
theorem exists_monos {L d : ℕ} (A : Finset ℕ) (hA : ∀ i ∈ A, i < L) (hcard : A.card ≤ d) :
    ∃ S ∈ monos L d, S.toFinset = A := by
  set bl := bitmapOf L A with hbl
  have hlen : bl.length = L := by simp [hbl, bitmapOf]
  have hS := supp_bitmapOf L A hA
  have hsl : (supp bl).length ≤ d := by
    have e : (supp bl).length = A.card := by
      rw [← List.toFinset_card_of_nodup ((supp_pairwise bl).imp (fun h => Nat.ne_of_lt h)), hS]
    omega
  have hb : binary L (value bl) = bl := by
    have := binary_of_value bl
    rwa [hlen] at this
  refine ⟨supp bl, List.mem_filterMap.mpr ⟨value bl, ?_, ?_⟩, hS⟩
  · rw [List.mem_range, ← hlen]; exact value_lt bl
  · rw [hb, if_pos hsl]

/-- **Each support is printed once**: two printed supports differ. -/
theorem monos_pairwise (L d : ℕ) : (monos L d).Pairwise fun S S' => S.toFinset ≠ S'.toFinset := by
  unfold monos
  apply List.Pairwise.filterMap (R := fun X X' => X < X' ∧ X < 2 ^ L ∧ X' < 2 ^ L)
  · intro X X' ⟨hlt, hX, hX'⟩ S hS S' hS' hEq
    split_ifs at hS hS'
    cases hS
    cases hS'
    have hSS : supp (binary L X) = supp (binary L X') :=
      (supp_pairwise _).eq_of_mem_iff (supp_pairwise _) (fun a => by
        rw [← List.mem_toFinset, hEq, List.mem_toFinset])
    have hb := eq_of_supp_eq (by simp) hSS
    have := congrArg value hb
    rw [binary_value _ _ hX, binary_value _ _ hX'] at this
    omega
  · exact List.pairwise_lt_range.imp_of_mem fun ha hb h =>
      ⟨h, List.mem_range.mp ha, List.mem_range.mp hb⟩

theorem monos_nodup (L d : ℕ) : (monos L d).Nodup := by
  refine List.Pairwise.imp ?_ (monos_pairwise L d)
  intro S S' h hab
  exact h (by rw [hab])

/-- The padded coordinate vector of a support of size `≤ e` (its coordinates, then `L`). -/
def padded (L e : ℕ) (S : List ℕ) : Fin e → Fin (L + 1) := fun k => ⟨min (S.getD k L) L, by omega⟩

theorem padded_inj (L e : ℕ) {S S' : List ℕ} (hL : ∀ i ∈ S, i < L) (hd : S.length ≤ e)
    (hL' : ∀ i ∈ S', i < L) (hd' : S'.length ≤ e) (h : padded L e S = padded L e S') : S = S' := by
  have hk : ∀ k < e, S.getD k L = S'.getD k L := by
    intro k hk
    have := congrArg Fin.val (congrFun h ⟨k, hk⟩)
    simp only [padded] at this
    have h1 : S.getD k L ≤ L := by
      rw [List.getD_eq_getElem?_getD]
      cases hs : S[k]? with
      | none => simp
      | some x => simp; exact (hL x (List.mem_of_getElem? hs)).le
    have h2 : S'.getD k L ≤ L := by
      rw [List.getD_eq_getElem?_getD]
      cases hs : S'[k]? with
      | none => simp
      | some x => simp; exact (hL' x (List.mem_of_getElem? hs)).le
    omega
  have hlen : S.length = S'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hk S.length (by omega)
      rw [List.getD_eq_default _ _ (le_refl _), List.getD_eq_getElem _ _ hlt] at this
      exact absurd (this ▸ hL' _ (List.getElem_mem hlt)) (lt_irrefl L)
    · have := hk S'.length (by omega)
      rw [List.getD_eq_default _ _ (le_refl _), List.getD_eq_getElem _ _ hlt] at this
      exact absurd (this.symm ▸ hL _ (List.getElem_mem hlt)) (lt_irrefl L)
  apply List.ext_getElem hlen
  intro k h1 h2
  have := hk k (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- A duplicate-free list of supports of size `≤ e` on the coordinates `< L` has at most `(L+1)^e` members. -/
theorem length_supports_le (L e : ℕ) (l : List (List ℕ)) (hnd : l.Nodup)
    (hS : ∀ S ∈ l, (∀ i ∈ S, i < L) ∧ S.length ≤ e) : l.length ≤ (L + 1) ^ e := by
  have hnd' : (l.map (padded L e)).Nodup :=
    hnd.map_on fun S hS' S' hS'' h => padded_inj L e (hS S hS').1 (hS S hS').2 (hS S' hS'').1 (hS S' hS'').2 h
  have := hnd'.length_le_card
  simpa [Fintype.card_fun, Fintype.card_fin] using this

/-! ## Correctness -/

theorem getD_pointOf (L : ℕ) (T : List ℕ) {i : ℕ} (hi : i < L) : (pointOf L T).getD i false = decide (i ∈ T) := by
  unfold pointOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem all_pointOf (L : ℕ) (T m : List ℕ) (hm : ∀ i ∈ m, i < L) :
    m.all (fun i => (pointOf L T).getD i false) = decide (m.toFinset ⊆ T.toFinset) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, decide_eq_true_eq, Finset.subset_iff, List.mem_toFinset]
  constructor
  · intro h i hi
    have := h i hi
    rwa [getD_pointOf L T (hm i hi), decide_eq_true_eq] at this
  · intro h i hi
    rw [getD_pointOf L T (hm i hi), decide_eq_true_eq]
    exact h hi

theorem all_congr_toFinset {m S : List ℕ} (h : m.toFinset = S.toFinset) (ρ : ℕ → Bool) : m.all ρ = S.all ρ := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  have hm : ∀ x, x ∈ m ↔ x ∈ S := fun x => by rw [← List.mem_toFinset, h, List.mem_toFinset]
  constructor
  · intro h' x hx; exact h' x ((hm x).mpr hx)
  · intro h' x hx; exact h' x ((hm x).mp hx)

theorem sum_bz_eq_count (l : List (Finset ℕ)) (A : Finset ℕ) :
    (l.map fun X => bz (decide (X = A))).sum = ((l.count A : ℕ) : ZMod 2) := by
  induction l with
  | nil => simp
  | cons X l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : X = A
    · subst h; simp [add_comm]
    · simp [h]

/-- **The interpolation print is exact** (Möbius inversion over `𝔽₂`): if `f` agrees at the points `1_T` with an explicit
`p` of degree `≤ d` on `Z_0, …, Z_{L−1}`, the print has `p`'s value at EVERY assignment. -/
theorem interpPrint_eval (f : List Bool → Bool) (L d : ℕ) (p : List (List ℕ))
    (hdeg : ∀ m ∈ p, m.length ≤ d) (hat : ∀ m ∈ p, ∀ i ∈ m, i < L)
    (hf : ∀ T : List ℕ, f (pointOf L T) = evalP p fun i => (pointOf L T).getD i false) (ρ : ℕ → Bool) :
    evalP (interpPrint f L d) ρ = evalP p ρ := by
  apply bz_inj
  rw [bz_evalP, bz_evalP, interpPrint, sum_filter_bz]
  -- the coefficient of each printed monomial counts the monomials of `p` with its support
  have hcoef : ∀ S ∈ monos L d,
      bz (subsetX f L S) = (p.map fun m => bz (decide (m.toFinset = S.toFinset))).sum := by
    intro S hS
    have hnd : S.Nodup := (mem_monos hS).1.imp (fun h => Nat.ne_of_lt h)
    rw [bz_subsetX]
    have hT : ∀ T : List ℕ, bz (f (pointOf L T)) =
        (p.map fun m => bz (decide (m.toFinset ⊆ T.toFinset))).sum := by
      intro T
      rw [hf T, bz_evalP]
      congr 1
      apply List.map_congr_left
      intro m hm
      rw [all_pointOf L T m (hat m hm)]
    rw [List.map_congr_left (fun T _ => hT T), sum_comm_list]
    congr 1
    apply List.map_congr_left
    intro m _
    exact sublists_parity S m.toFinset hnd
  have e1 : ((monos L d).map fun S => bz (subsetX f L S) * bz (S.all ρ)) =
      ((monos L d).map fun S => (p.map fun m => bz (decide (m.toFinset = S.toFinset))).sum * bz (S.all ρ)) :=
    List.map_congr_left (fun S hS => by rw [hcoef S hS])
  rw [e1]
  simp only [← List.sum_map_mul_right]
  rw [sum_comm_list]
  congr 1
  apply List.map_congr_left
  intro m hm
  -- exactly one printed monomial has the support of `m`
  have hterm : ∀ S ∈ monos L d, bz (decide (m.toFinset = S.toFinset)) * bz (S.all ρ) =
      bz (decide (S.toFinset = m.toFinset)) * bz (m.all ρ) := by
    intro S _
    by_cases h : m.toFinset = S.toFinset
    · rw [all_congr_toFinset h ρ, h]
    · have h' : ¬ S.toFinset = m.toFinset := fun e => h e.symm
      simp [h, h']
  rw [List.map_congr_left hterm, List.sum_map_mul_right]
  have hone : ((monos L d).map fun S => bz (decide (S.toFinset = m.toFinset))).sum = 1 := by
    have e : ((monos L d).map fun S => bz (decide (S.toFinset = m.toFinset))) =
        (((monos L d).map List.toFinset).map fun X => bz (decide (X = m.toFinset))) := by
      rw [List.map_map]; rfl
    rw [e, sum_bz_eq_count]
    have hnd : ((monos L d).map List.toFinset).Nodup := List.pairwise_map.mpr (monos_pairwise L d)
    obtain ⟨S, hS, hSA⟩ := exists_monos m.toFinset (fun i hi => hat m hm i (List.mem_toFinset.mp hi))
      ((List.toFinset_card_le m).trans (hdeg m hm))
    rw [List.count_eq_one_of_mem hnd (List.mem_map.mpr ⟨S, hS, hSA⟩)]
    simp
  rw [hone, one_mul]

/-- The coefficient of a support counts the monomials of `p` with that support (the core of `interpPrint_eval`). -/
theorem bz_subsetX_eq (f : List Bool → Bool) (L : ℕ) (p : List (List ℕ)) (hat : ∀ m ∈ p, ∀ i ∈ m, i < L)
    (hf : ∀ T : List ℕ, f (pointOf L T) = evalP p fun i => (pointOf L T).getD i false) (S : List ℕ) (hnd : S.Nodup) :
    bz (subsetX f L S) = (p.map fun m => bz (decide (m.toFinset = S.toFinset))).sum := by
  rw [bz_subsetX]
  have hT : ∀ T : List ℕ, bz (f (pointOf L T)) =
      (p.map fun m => bz (decide (m.toFinset ⊆ T.toFinset))).sum := by
    intro T
    rw [hf T, bz_evalP]
    congr 1
    apply List.map_congr_left
    intro m hm
    rw [all_pointOf L T m (hat m hm)]
  rw [List.map_congr_left (fun T _ => hT T), sum_comm_list]
  congr 1
  apply List.map_congr_left
  intro m _
  exact sublists_parity S m.toFinset hnd

/-- **A support with coefficient one is the support of a monomial of `p`**. -/
theorem coeff_support (f : List Bool → Bool) (L : ℕ) (p : List (List ℕ)) (hat : ∀ m ∈ p, ∀ i ∈ m, i < L)
    (hf : ∀ T : List ℕ, f (pointOf L T) = evalP p fun i => (pointOf L T).getD i false) {S : List ℕ} (hnd : S.Nodup)
    (hc : subsetX f L S = true) : ∃ m ∈ p, m.toFinset = S.toFinset := by
  have h1 := bz_subsetX_eq f L p hat hf S hnd
  rw [hc, bz_true] at h1
  by_contra hno
  have hno' : ∀ m ∈ p, ¬ m.toFinset = S.toFinset := fun m hm h => hno ⟨m, hm, h⟩
  have h0 : (p.map fun m => bz (decide (m.toFinset = S.toFinset))) = p.map fun _ => 0 :=
    List.map_congr_left fun m hm => by simp [hno' m hm]
  rw [h0] at h1
  simp at h1

theorem interpPrint_support (f : List Bool → Bool) (L d : ℕ) (p : List (List ℕ)) (hat : ∀ m ∈ p, ∀ i ∈ m, i < L)
    (hf : ∀ T : List ℕ, f (pointOf L T) = evalP p fun i => (pointOf L T).getD i false) {S : List ℕ}
    (hS : S ∈ interpPrint f L d) : ∃ m ∈ p, m.toFinset = S.toFinset := by
  obtain ⟨hmem, hc⟩ := List.mem_filter.mp hS
  exact coeff_support f L p hat hf ((mem_monos hmem).1.imp (fun h => Nat.ne_of_lt h)) hc

theorem length_le_of_nodup_pairwise {S : List ℕ} (hS : S.Pairwise (· < ·)) {m : List ℕ}
    (h : m.toFinset = S.toFinset) : S.length ≤ m.length := by
  rw [← List.toFinset_card_of_nodup (hS.imp (fun h => Nat.ne_of_lt h)), ← h]
  exact List.toFinset_card_le m

theorem length_interpPrint_le (f : List Bool → Bool) (L d : ℕ) (p : List (List ℕ)) (dp : ℕ)
    (hdeg : ∀ m ∈ p, m.length ≤ dp) (hat : ∀ m ∈ p, ∀ i ∈ m, i < L)
    (hf : ∀ T : List ℕ, f (pointOf L T) = evalP p fun i => (pointOf L T).getD i false) :
    (interpPrint f L d).length ≤ (L + 1) ^ dp := by
  apply length_supports_le L dp _ ((monos_nodup L d).filter _)
  intro S hS
  obtain ⟨m, hm, hmS⟩ := interpPrint_support f L d p hat hf hS
  have hmem := (List.mem_filter.mp hS).1
  exact ⟨(mem_monos hmem).2.1, (length_le_of_nodup_pairwise (mem_monos hmem).1 hmS).trans (hdeg m hm)⟩

/-- **The print does not depend on the enumeration bound** above `p`'s degree: the printer may enumerate the supports
of size `≤ d'` for any computable `d' ≥ d_p`. -/
theorem interpPrint_congr (f : List Bool → Bool) (L d d' : ℕ) (p : List (List ℕ)) (dp : ℕ)
    (hdeg : ∀ m ∈ p, m.length ≤ dp) (hat : ∀ m ∈ p, ∀ i ∈ m, i < L)
    (hf : ∀ T : List ℕ, f (pointOf L T) = evalP p fun i => (pointOf L T).getD i false)
    (hd : dp ≤ d) (hd' : dp ≤ d') : interpPrint f L d = interpPrint f L d' := by
  have key : ∀ e, dp ≤ e → interpPrint f L e = (List.range (2 ^ L)).filterMap fun X =>
      if subsetX f L (supp (binary L X)) then some (supp (binary L X)) else none := by
    intro e he
    unfold interpPrint monos
    rw [List.filter_filterMap]
    apply List.filterMap_congr
    intro X _
    by_cases hc : subsetX f L (supp (binary L X)) = true
    · obtain ⟨m, hm, hmS⟩ := coeff_support f L p hat hf ((supp_pairwise _).imp (fun h => Nat.ne_of_lt h)) hc
      have hsz : (supp (binary L X)).length ≤ e :=
        ((length_le_of_nodup_pairwise (supp_pairwise _) hmS).trans (hdeg m hm)).trans he
      simp [hsz, hc]
    · by_cases hsz : (supp (binary L X)).length ≤ e <;> simp [hsz, hc]
  rw [key d hd, key d' hd']

end NearCubicWires.WireExponent3_5.ListMachine.Interp
