import Proof.Wire_3_5.ListMachineRowPopClass

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.LocalBitMultitape

/-! ## One-hot words -/

/-- The one-hot block of the digit `t`. -/
def ohB (K t : ℕ) : List Bool := (List.range (K + 1)).map fun i => decide (i = t)

/-- The one-hot word of a digit tuple. -/
def encT (K : ℕ) (τ : List ℕ) : List Bool := τ.flatMap (ohB K)

@[simp] theorem ohB_length (K t : ℕ) : (ohB K t).length = K + 1 := by simp [ohB]

@[simp] theorem encT_length (K : ℕ) (τ : List ℕ) : (encT K τ).length = τ.length * (K + 1) := by
  induction τ with
  | nil => simp [encT]
  | cons t τ ih =>
    simp only [encT, List.flatMap_cons, List.length_append, ohB_length, List.length_cons] at ih ⊢; rw [ih]; ring

theorem encT_append (K : ℕ) (a b : List ℕ) : encT K (a ++ b) = encT K a ++ encT K b := by simp [encT]

theorem ohB_getElem (K t i : ℕ) (hi : i < (ohB K t).length) : (ohB K t)[i] = decide (i = t) := by simp [ohB]

/-! ## The tuples and the odometer -/

/-- All tuples of `P` digits in `[0, K]`, in lexicographic order. -/
def lexT (K : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | P + 1 => (lexT K P).flatMap fun ρ => (List.range (K + 1)).map fun t => ρ ++ [t]

/-- The increment on the reversed tuple. -/
def bumpR (K : ℕ) : List ℕ → List ℕ
  | [] => []
  | t :: ρ => if t < K then (t + 1) :: ρ else 0 :: bumpR K ρ

/-- **The odometer increment**: the last position least significant. -/
def incT (K : ℕ) (τ : List ℕ) : List ℕ := (bumpR K τ.reverse).reverse

/-- Every digit is at least `K` (for digits `≤ K`: the last tuple). -/
def allK (K : ℕ) (τ : List ℕ) : Bool := τ.all fun x => decide (K ≤ x)

theorem incT_nil (K : ℕ) : incT K [] = [] := rfl

theorem incT_snoc (K : ℕ) (ρ : List ℕ) (t : ℕ) :
    incT K (ρ ++ [t]) = if t < K then ρ ++ [t + 1] else incT K ρ ++ [0] := by
  unfold incT
  rw [List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, bumpR]
  split_ifs <;> simp

theorem allK_snoc (K : ℕ) (ρ : List ℕ) (t : ℕ) : allK K (ρ ++ [t]) = (allK K ρ && decide (K ≤ t)) := by
  simp [allK, List.all_append]

@[simp] theorem length_lexT (K P : ℕ) : (lexT K P).length = (K + 1) ^ P := by
  induction P with
  | zero => rfl
  | succ P ih =>
    simp only [lexT, List.length_flatMap, List.length_map, List.length_range]
    rw [List.map_const', List.sum_replicate, ih, smul_eq_mul, pow_succ]

theorem mem_lexT {K P : ℕ} {τ : List ℕ} (h : τ ∈ lexT K P) : τ.length = P ∧ ∀ x ∈ τ, x ≤ K := by
  induction P generalizing τ with
  | zero => simp [lexT] at h; subst h; simp
  | succ P ih =>
    simp only [lexT, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨ρ, hρ, t, ht, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hρ
    refine ⟨by simp [h1], fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h2 x hx
    · omega

/-- The entries of a flat map of blocks of equal length. -/
theorem getElem?_flatMap_const {α β : Type} (L : List α) (f : α → List β) (m : ℕ) (hf : ∀ x, (f x).length = m)
    (r t : ℕ) (ht : t < m) : (L.flatMap f)[r * m + t]? = L[r]?.bind fun x => (f x)[t]? := by
  induction L generalizing r with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons]
    cases r with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by rw [hf]; exact ht)]
      simp
    | succ r =>
      rw [List.getElem?_append_right (by rw [hf, Nat.add_mul, Nat.one_mul]; omega), hf]
      have e : (r + 1) * m + t - m = r * m + t := by rw [Nat.add_mul, Nat.one_mul]; omega
      rw [e, ih r]
      simp

/-- The tuple at index `j` (all zeros past the end). -/
def tupAt (K P j : ℕ) : List ℕ := (lexT K P).getD j (List.replicate P 0)

theorem tupAt_out (K P j : ℕ) (hj : (K + 1) ^ P ≤ j) : tupAt K P j = List.replicate P 0 := by
  unfold tupAt
  rw [List.getD_eq_default _ _ (by simpa using hj)]

theorem tupAt_mem (K P j : ℕ) (hj : j < (K + 1) ^ P) : tupAt K P j ∈ lexT K P := by
  unfold tupAt
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  exact List.getElem_mem _

theorem tupAt_succ (K P r t : ℕ) (hr : r < (K + 1) ^ P) (ht : t ≤ K) :
    tupAt K (P + 1) (r * (K + 1) + t) = tupAt K P r ++ [t] := by
  have hr' : r < (lexT K P).length := by simpa using hr
  unfold tupAt
  rw [List.getD_eq_getElem?_getD, lexT, getElem?_flatMap_const _ _ (K + 1) (fun _ => by simp) r t (by omega),
    List.getElem?_eq_getElem hr', List.getD_eq_getElem _ _ hr']
  simp [List.getElem?_range (show t < K + 1 by omega)]

theorem tupAt_zero (K P : ℕ) : tupAt K P 0 = List.replicate P 0 := by
  induction P with
  | zero => rfl
  | succ P ih =>
    have e := tupAt_succ K P 0 0 (by positivity) (by omega)
    simp only [Nat.zero_mul, Nat.add_zero] at e
    rw [e, ih, List.replicate_succ']

/-- **The odometer on the enumeration**: the increment of the tuple at `j` is the tuple at `j + 1` (all zeros after
the last), and the last tuple is the one with all digits `K`. -/
theorem incT_tupAt (K P j : ℕ) (hj : j < (K + 1) ^ P) :
    incT K (tupAt K P j) = tupAt K P (j + 1) ∧ allK K (tupAt K P j) = decide (j + 1 = (K + 1) ^ P) := by
  induction P generalizing j with
  | zero =>
    have : j = 0 := by simpa using hj
    subst this
    refine ⟨?_, rfl⟩
    rw [tupAt_out K 0 1 (by simp)]
    rfl
  | succ P ih =>
    have hK : 0 < K + 1 := by omega
    obtain ⟨r, t, ht, rfl⟩ : ∃ r t, t < K + 1 ∧ j = r * (K + 1) + t :=
      ⟨j / (K + 1), j % (K + 1), Nat.mod_lt _ hK, by rw [mul_comm]; exact (Nat.div_add_mod j (K + 1)).symm⟩
    have hr : r < (K + 1) ^ P := by
      rw [pow_succ] at hj
      by_contra hc
      have := Nat.mul_le_mul_right (K + 1) (Nat.le_of_not_lt hc)
      omega
    have hN : (r + 1) * (K + 1) ≤ (K + 1) ^ (P + 1) := by
      rw [pow_succ]; exact Nat.mul_le_mul_right (K + 1) hr
    rw [tupAt_succ K P r t hr (by omega), incT_snoc, allK_snoc]
    by_cases htK : t < K
    · rw [if_pos htK]
      refine ⟨?_, ?_⟩
      · rw [show r * (K + 1) + t + 1 = r * (K + 1) + (t + 1) by ring, tupAt_succ K P r (t + 1) hr (by omega)]
      · have h1 : ¬ (K ≤ t) := by omega
        simp only [h1, decide_false, Bool.and_false]
        symm
        rw [decide_eq_false_iff_not]
        rw [Nat.add_mul, Nat.one_mul] at hN
        omega
    · have htK' : t = K := by omega
      subst htK'
      rw [if_neg htK]
      obtain ⟨ih1, ih2⟩ := ih r hr
      rw [ih1, ih2]
      simp only [le_refl, decide_true, Bool.and_true]
      have ej : r * (t + 1) + t + 1 = (r + 1) * (t + 1) := by ring
      rw [ej]
      by_cases hn : r + 1 < (t + 1) ^ P
      · refine ⟨?_, ?_⟩
        · have e := tupAt_succ t P (r + 1) 0 hn (by omega)
          simpa using e.symm
        · have hne : ¬ (r + 1 = (t + 1) ^ P) := by omega
          have hne' : ¬ ((r + 1) * (t + 1) = (t + 1) ^ (P + 1)) := by
            rw [pow_succ]
            intro h
            exact hne (Nat.eq_of_mul_eq_mul_right (by omega) h)
          simp [hne, hne']
      · have hr1 : r + 1 = (t + 1) ^ P := by omega
        refine ⟨?_, ?_⟩
        · rw [tupAt_out t P (r + 1) (by omega), tupAt_out t (P + 1) _ (by rw [hr1, pow_succ]),
            List.replicate_succ']
        · simp [hr1, pow_succ]

/-! ## With pairs flattened, `lexT` is `allTuples` -/

theorem lexT_cons (K P : ℕ) :
    lexT K (P + 1) = (List.range (K + 1)).flatMap fun a => (lexT K P).map (a :: ·) := by
  induction P with
  | zero =>
    simp only [lexT, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.map_cons,
      List.map_nil]
    generalize List.range (K + 1) = l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  | succ P ih =>
    conv_lhs => rw [lexT, ih]
    rw [List.flatMap_assoc]
    conv_rhs => rw [lexT]
    refine congrArg (fun g => (List.range (K + 1)).flatMap g) (funext fun a => ?_)
    rw [List.flatMap_map, List.map_flatMap]
    refine congrArg (fun g => (lexT K P).flatMap g) (funext fun ρ => ?_)
    simp

/-- A tuple of pairs, flattened. -/
def flatP (tup : List (ℕ × ℕ)) : List ℕ := tup.flatMap fun ab => [ab.1, ab.2]

theorem allTuples_flat (K n : ℕ) : (allTuples K n).map flatP = lexT K (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, lexT_cons, lexT_cons, allTuples, List.map_flatMap]
    unfold pairsUpTo
    rw [List.flatMap_assoc]
    refine congrArg (fun g => (List.range (K + 1)).flatMap g) (funext fun a => ?_)
    rw [List.flatMap_map, List.map_flatMap]
    refine congrArg (fun g => (List.range (K + 1)).flatMap g) (funext fun b => ?_)
    rw [← ih, List.map_map, List.map_map, List.map_map]
    rfl

/-! ## Unary contribution fields and the masked sum -/

/-- Unary fields `1^c 0`. -/
def fieldsU (cs : List ℕ) : List Bool := cs.flatMap fun c => List.replicate c true ++ [false]

/-- The masked sum `Σ_j b_j c_j`. -/
def dotB : List Bool → List ℕ → ℕ
  | b :: bs, c :: cs => (if b then c else 0) + dotB bs cs
  | _, _ => 0

theorem dotB_append (b1 b2 : List Bool) (c1 c2 : List ℕ) (h : b1.length = c1.length) :
    dotB (b1 ++ b2) (c1 ++ c2) = dotB b1 c1 + dotB b2 c2 := by
  induction b1 generalizing c1 with
  | nil => cases c1 with
    | nil => simp [dotB]
    | cons _ _ => simp at h
  | cons b b1 ih => cases c1 with
    | nil => simp at h
    | cons c c1 => simp only [List.cons_append, dotB]; rw [ih c1 (by simpa using h)]; ring

theorem dotB_ohB (K t : ℕ) (g : ℕ → ℕ) (ht : t ≤ K) : dotB (ohB K t) ((List.range (K + 1)).map g) = g t := by
  unfold ohB
  suffices key : ∀ a n, t < a + n + 1 → a ≤ t → dotB ((List.range' a (n + 1)).map fun i => decide (i = t))
      ((List.range' a (n + 1)).map g) = g t by
    have := key 0 K (by omega) (Nat.zero_le _)
    simpa [List.range_eq_range'] using this
  intro a n
  induction n generalizing a with
  | zero =>
    intro h1 h2
    have : a = t := by omega
    subst this; simp [List.range'_succ, dotB]
  | succ n ih =>
    intro h1 h2
    rw [List.range'_succ, List.map_cons, List.map_cons, dotB]
    by_cases ha : a = t
    · subst ha
      simp only [decide_true, if_true]
      suffices z : ∀ a' m, a < a' → dotB ((List.range' a' m).map fun i => decide (i = a)) ((List.range' a' m).map g) = 0 by
        rw [z (a + 1) (n + 1) (by omega)]; rfl
      intro a' m ha'
      induction m generalizing a' with
      | zero => simp [dotB]
      | succ m ihm =>
        rw [List.range'_succ, List.map_cons, List.map_cons, dotB, ihm (a' + 1) (by omega)]
        simp; omega
    · simp only [ha, decide_false, Bool.false_eq_true, if_false, Nat.zero_add]
      exact ih (a + 1) (by omega) (by omega)

/-- **The masked sum of a tuple's one-hot word** over per-position contribution blocks. -/
theorem dotB_encT (K : ℕ) (con : ℕ → ℕ → ℕ) : ∀ (τ : List ℕ) (o : ℕ), (∀ x ∈ τ, x ≤ K) →
    dotB (encT K τ) ((List.range τ.length).flatMap fun i => (List.range (K + 1)).map (con (o + i))) =
      ((List.range τ.length).map fun i => con (o + i) (τ.getD i 0)).sum
  | [], _, _ => by simp [encT, dotB]
  | t :: τ, o, h => by
    have ht : t ≤ K := h t (by simp)
    have hr : List.range (τ.length + 1) = 0 :: (List.range τ.length).map Nat.succ := List.range_succ_eq_map
    rw [List.length_cons, hr, List.flatMap_cons, List.map_cons, List.sum_cons]
    simp only [encT, List.flatMap_cons]
    rw [dotB_append _ _ _ _ (by simp), Nat.add_zero, dotB_ohB K t _ ht]
    have ih := dotB_encT K con τ (o + 1) (fun x hx => h x (by simp [hx]))
    simp only [encT] at ih
    rw [List.flatMap_map, List.map_map]
    have e1 : (fun i => (List.range (K + 1)).map (con (o + (i + 1)))) = fun i => (List.range (K + 1)).map (con (o + 1 + i)) := by
      funext i; rw [show o + (i + 1) = o + 1 + i by ring]
    rw [show (fun i => (List.range (K + 1)).map (con (o + (i + 1)))) = _ from e1, ih]
    simp only [List.getD_cons_zero]
    congr 2
    apply List.map_congr_left
    intro i _
    simp [Function.comp, show o + (i + 1) = o + 1 + i by ring]

/-! ## The words the odometer and the residue test read -/

/-- The increment's position word: cell `2j` is `[j = 0]`, cell `2j + 1` is `[j` starts a block`]`. -/
def zW (K N : ℕ) : List Bool :=
  (List.range (2 * N)).map fun q => if q % 2 = 0 then decide (q / 2 = 0) else decide (q / 2 % (K + 1) = 0)

theorem zW_mark (K N j : ℕ) (hj : j < N) : readTapeBit (zW K N) (2 * j) = decide (j = 0) := by
  unfold readTapeBit zW
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]

theorem zW_bit (K N j : ℕ) (hj : j < N) : readTapeBit (zW K N) (2 * j + 1) = decide (j % (K + 1) = 0) := by
  unfold readTapeBit zW
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [h1, h2]

@[simp] theorem zW_length (K N : ℕ) : (zW K N).length = 2 * N := by simp [zW]

/-- The residue pattern: cell `k` is `[k ≡ s (mod p)]`. -/
def patT (p s len : ℕ) : List Bool := (List.range len).map fun k => decide (k % p = s)

theorem patT_read (p s len k : ℕ) (hk : k < len) : readTapeBit (patT p s len) k = decide (k % p = s) := by
  unfold readTapeBit patT
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

end NearCubicWires.WireExponent3_5.ListMachine.Row
