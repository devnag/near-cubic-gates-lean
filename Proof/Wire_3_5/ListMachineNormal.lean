import Proof.Wire_3_5.ListMachineRefs

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists Finset NearCubicWires.WireExponent3_5.ListMachine.Ref

/-! ## Squarefree multilinear reduction over `𝔽₂` -/

/-- A monomial with repeated coordinates merged, sorted. -/
def normMono (m : List ℕ) : List ℕ := (m.dedup).insertionSort (· ≤ ·)

/-- Add one monomial over `𝔽₂`: a second copy cancels the first. -/
def toggle (m : List ℕ) (acc : Poly) : Poly := if m ∈ acc then acc.erase m else m :: acc

/-- **The squarefree multilinear reduction** of an explicit `𝔽₂` polynomial. -/
def normalize (p : Poly) : Poly := (p.map normMono).foldr toggle []

theorem mem_normMono (m : List ℕ) (i : ℕ) : i ∈ normMono m ↔ i ∈ m := by
  unfold normMono
  rw [(List.perm_insertionSort _ _).mem_iff, List.mem_dedup]

theorem all_normMono (m : List ℕ) (ρ : ℕ → Bool) : (normMono m).all ρ = m.all ρ := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h i hi => h i ((mem_normMono m i).mpr hi), fun h i hi => h i ((mem_normMono m i).mp hi)⟩

theorem length_normMono (m : List ℕ) : (normMono m).length ≤ m.length := by
  unfold normMono
  rw [List.length_insertionSort]
  exact (List.dedup_sublist m).length_le

theorem nodup_normMono (m : List ℕ) : (normMono m).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_dedup m)

theorem sorted_normMono (m : List ℕ) : (normMono m).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _

theorem eval_perm {p q : Poly} (h : p.Perm q) (ρ : ℕ → Bool) : F2Poly.eval p ρ = F2Poly.eval q ρ := by
  induction h with
  | nil => rfl
  | cons m _ ih => rw [eval_cons, eval_cons, ih]
  | swap m m' l => rw [eval_cons, eval_cons, eval_cons, eval_cons, ← Bool.xor_assoc, ← Bool.xor_assoc,
      Bool.xor_comm (m'.all ρ)]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem eval_toggle (m : List ℕ) (acc : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (toggle m acc) ρ = xor (m.all ρ) (F2Poly.eval acc ρ) := by
  unfold toggle
  split_ifs with h
  · rw [eval_perm (List.perm_cons_erase h) ρ, eval_cons, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  · rw [eval_cons]

/-- **Reduction never changes the value** on any Boolean input. -/
theorem eval_normalize (p : Poly) (ρ : ℕ → Bool) : F2Poly.eval (normalize p) ρ = F2Poly.eval p ρ := by
  unfold normalize
  induction p with
  | nil => rfl
  | cons m p ih => rw [List.map_cons, List.foldr_cons, eval_toggle, ih, all_normMono, eval_cons]

theorem nodup_normalize (p : Poly) : (normalize p).Nodup := by
  unfold normalize
  induction p with
  | nil => exact List.nodup_nil
  | cons m p ih =>
    rw [List.map_cons, List.foldr_cons]
    unfold toggle
    split_ifs with h
    · exact ih.erase _
    · exact List.nodup_cons.mpr ⟨h, ih⟩

theorem mem_normalize {p : Poly} {m : List ℕ} (hm : m ∈ normalize p) : ∃ m' ∈ p, m = normMono m' := by
  unfold normalize at hm
  induction p with
  | nil => simp at hm
  | cons a p ih =>
    rw [List.map_cons, List.foldr_cons] at hm
    unfold toggle at hm
    split_ifs at hm with h
    · obtain ⟨m', hm', rfl⟩ := ih (List.mem_of_mem_erase hm)
      exact ⟨m', List.mem_cons_of_mem _ hm', rfl⟩
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨a, List.mem_cons_self .., rfl⟩
      · obtain ⟨m', hm', rfl⟩ := ih hm
        exact ⟨m', List.mem_cons_of_mem _ hm', rfl⟩

theorem degLe_normalize {p : Poly} {e : ℕ} (h : DegLe p e) : DegLe (normalize p) e := by
  intro m hm
  obtain ⟨m', hm', rfl⟩ := mem_normalize hm
  exact (length_normMono m').trans (h m' hm')

theorem atomsLt_normalize {p : Poly} {L : ℕ} (h : AtomsLt p L) : AtomsLt (normalize p) L := by
  intro m hm i hi
  obtain ⟨m', hm', rfl⟩ := mem_normalize hm
  exact h m' hm' i ((mem_normMono m' i).mp hi)

/-- `Σ_{k≤D} C(L,k) ≤ (L+1)^D`. -/
theorem card_small_subsets_le (L D : ℕ) :
    ((range L).powerset.filter fun S => S.card ≤ D).card ≤ (L + 1) ^ D := by
  have hsplit : ((range L).powerset.filter fun S => S.card ≤ D) =
      (range (D + 1)).biUnion fun k => Finset.powersetCard k (range L) := by
    ext S; simp [Finset.mem_powersetCard, and_comm]
  rw [hsplit]
  clear hsplit
  refine (Finset.card_biUnion_le).trans ?_
  simp only [Finset.card_powersetCard, Finset.card_range]
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ]
    have hk : L.choose (D + 1) ≤ L ^ (D + 1) := Nat.choose_le_pow L (D + 1)
    have h1 : L ^ (D + 1) ≤ L * (L + 1) ^ D := by
      rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) D)
    calc ∑ k ∈ range (D + 1), L.choose k + L.choose (D + 1) ≤ (L + 1) ^ D + L * (L + 1) ^ D := by omega
      _ = (L + 1) ^ (D + 1) := by ring

/-- A reduced list: distinct monomials, each squarefree and sorted. -/
def IsNormal (p : Poly) : Prop := p.Nodup ∧ ∀ m ∈ p, normMono m = m

theorem normMono_normMono (m : List ℕ) : normMono (normMono m) = normMono m := by
  show ((normMono m).dedup).insertionSort (· ≤ ·) = normMono m
  rw [List.Nodup.dedup (nodup_normMono m)]
  exact List.Pairwise.insertionSort_eq (sorted_normMono m)

theorem normalize_normal (p : Poly) : IsNormal (normalize p) :=
  ⟨nodup_normalize p, fun m hm => by obtain ⟨m', _, rfl⟩ := mem_normalize hm; exact normMono_normMono m'⟩

theorem normal_length_le (p : Poly) (L D : ℕ) (hn : IsNormal p) (hd : DegLe p D) (ha : AtomsLt p L) :
    p.length ≤ (L + 1) ^ D := by
  have hsort : ∀ m ∈ p, m.toFinset.sort (· ≤ ·) = m := by
    intro m hm
    have hm' := hn.2 m hm
    have hnd : m.Nodup := hm' ▸ nodup_normMono m
    have hs : m.Pairwise (· ≤ ·) := hm' ▸ sorted_normMono m
    exact (List.toFinset_sort (r := (· ≤ ·)) hnd).mpr hs
  have hinj : Set.InjOn List.toFinset {m | m ∈ p} := by
    intro m hm m' hm' heq
    rw [← hsort m hm, ← hsort m' hm', heq]
  have hcard : p.toFinset.card = p.length := List.toFinset_card_of_nodup hn.1
  rw [← hcard, ← Finset.card_image_of_injOn (f := List.toFinset) (by simpa using hinj)]
  refine le_trans (Finset.card_le_card ?_) (card_small_subsets_le L D)
  intro S hS
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
  rw [List.mem_toFinset] at hm
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun i hi => Finset.mem_range.mpr (ha m hm i (List.mem_toFinset.mp hi)), ?_⟩
  exact (List.toFinset_card_le m).trans (hd m hm)

theorem normalize_length_le (p : Poly) (L D : ℕ) (hd : DegLe p D) (ha : AtomsLt p L) :
    (normalize p).length ≤ (L + 1) ^ D :=
  normal_length_le _ L D (normalize_normal p) (degLe_normalize hd) (atomsLt_normalize ha)

theorem pone_normal : IsNormal pone := ⟨by simp [pone], by intro m hm; simp [pone] at hm; subst hm; rfl⟩
theorem pzero_normal : IsNormal pzero := ⟨List.nodup_nil, by intro m hm; simp [pzero] at hm⟩

/-! ## The reduced refs -/

def nadd (p q : Poly) : Poly := normalize (padd p q)
def nmul (p q : Poly) : Poly := normalize (pmul p q)
def nnot (p : Poly) : Poly := normalize (pnot p)
def nsum (ps : List Poly) : Poly := normalize (psum ps)

@[simp] theorem eval_nadd (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (nadd p q) ρ = xor (F2Poly.eval p ρ) (F2Poly.eval q ρ) := by simp [nadd, eval_normalize]
@[simp] theorem eval_nmul (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (nmul p q) ρ = (F2Poly.eval p ρ && F2Poly.eval q ρ) := by simp [nmul, eval_normalize]
@[simp] theorem eval_nnot (p : Poly) (ρ : ℕ → Bool) : F2Poly.eval (nnot p) ρ = !F2Poly.eval p ρ := by
  simp [nnot, eval_normalize]
theorem eval_nsum (ps : List Poly) (ρ : ℕ → Bool) : F2Poly.eval (nsum ps) ρ = F2Poly.eval (psum ps) ρ := by
  simp [nsum, eval_normalize]

/-- `binom(S + a, t) mod 2`, reduced after each step. -/
def binomRefN : List Poly → ℤ → ℕ → Poly
  | [], a, t => pconst (chooseMod2 a t)
  | _ :: _, _, 0 => pone
  | ℓ :: ls, a, t + 1 => nadd (binomRefN ls a (t + 1)) (nmul ℓ (binomRefN ls a t))

theorem eval_binomRefN (ls : List Poly) (a : ℤ) (t : ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (binomRefN ls a t) ρ = F2Poly.eval (binomRef ls a t) ρ := by
  induction ls generalizing t with
  | nil => rfl
  | cons ℓ ls ih =>
    cases t with
    | zero => rfl
    | succ t => simp only [binomRefN, binomRef, eval_nadd, eval_padd, eval_nmul, eval_pmul, ih]

theorem binomRefN_size (ls : List Poly) (L : ℕ) (hd : ∀ ℓ ∈ ls, DegLe ℓ 1) (ha : ∀ ℓ ∈ ls, AtomsLt ℓ L)
    (a : ℤ) (t : ℕ) : DegLe (binomRefN ls a t) t ∧ AtomsLt (binomRefN ls a t) L := by
  induction ls generalizing t with
  | nil => exact ⟨degLe_pconst _ _, atomsLt_pconst _ _⟩
  | cons ℓ ls ih =>
    have hd' : ∀ ℓ' ∈ ls, DegLe ℓ' 1 := fun ℓ' h => hd ℓ' (List.mem_cons_of_mem _ h)
    have ha' : ∀ ℓ' ∈ ls, AtomsLt ℓ' L := fun ℓ' h => ha ℓ' (List.mem_cons_of_mem _ h)
    cases t with
    | zero => exact ⟨degLe_pone 0, atomsLt_pone L⟩
    | succ t =>
      have hm := degLe_pmul (hd ℓ (List.mem_cons_self ..)) (ih hd' ha' t).1
      refine ⟨degLe_normalize (degLe_padd (ih hd' ha' (t + 1)).1 (degLe_normalize (hm.mono (by omega)))),
        atomsLt_normalize (atomsLt_padd (ih hd' ha' (t + 1)).2
          (atomsLt_normalize (atomsLt_pmul (ha ℓ (List.mem_cons_self ..)) (ih hd' ha' t).2)))⟩

namespace Ref
variable (D : ListData)

def bitRefN (L j h : ℕ) : Poly := binomRefN (litsRef D j L) (D.levelOffset j L) (2 ^ h)

def factorRefN (L j : ℕ) (d : ℤ) (h : ℕ) : Poly :=
  if (d + D.W j).toNat.testBit h then bitRefN D L j h else nnot (bitRefN D L j h)

/-- **The binary residue decoder, reduced**: what the machine prints for `A_{j,d}`. -/
def decoderRefN (L j : ℕ) (d : ℤ) : Poly :=
  if 0 ≤ d + D.W j ∧ d + D.W j < 2 ^ D.ell j then
    (List.range (D.ell j)).foldr (fun h acc => nmul (factorRefN D L j d h) acc) pone
  else pzero

theorem eval_decoderRefN (L j : ℕ) (d : ℤ) (ρ : ℕ → Bool) :
    F2Poly.eval (decoderRefN D L j d) ρ = F2Poly.eval (decoderRef D L j d) ρ := by
  unfold decoderRefN decoderRef
  split_ifs
  · generalize List.range (D.ell j) = l
    induction l with
    | nil => rfl
    | cons h l ih =>
      simp only [List.foldr_cons, eval_nmul, eval_pmul, ih]
      unfold factorRefN factorRef bitRefN bitRef
      split_ifs <;> simp [eval_binomRefN]
  · rfl

def recurRefN (M : ℕ) : List (ℤ → Poly) → ℕ → Poly
  | [] => fun s => if s = 0 then pone else pzero
  | A :: rest => fun s => nsum ((List.range (M + 1)).map fun t => nmul (recurRefN M rest t) (A ((s : ℤ) - 2 * t)))

theorem eval_recurRefN (M : ℕ) (l : List ℕ) (f g : ℕ → ℤ → Poly)
    (hfg : ∀ j d ρ, F2Poly.eval (f j d) ρ = F2Poly.eval (g j d) ρ) (s : ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (recurRefN M (l.map f) s) ρ = F2Poly.eval (recurRef M (l.map g) s) ρ := by
  induction l generalizing s with
  | nil => simp only [List.map_nil, recurRefN, recurRef]
  | cons j l ih =>
    simp only [List.map_cons, recurRefN, recurRef, eval_nsum, eval_psum, List.foldr_map]
    congr 1
    funext t b
    rw [eval_nmul, eval_pmul, ih, hfg]

def repairRefN (M : ℕ) (P : ℕ → Poly) (s : ℕ) : Poly :=
  if s = 0 then nnot (nsum ((List.range M).map fun i => P (i + 1))) else P s

/-- **The repaired states, reduced**: what the C2 list machine prints for `P_0, …, P_M`. -/
def stateRefN (L s : ℕ) : Poly :=
  repairRefN D.M (recurRefN D.M ((List.range D.J).map fun j d => decoderRefN D L j d)) s

theorem eval_stateRefN (L s : ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (stateRefN D L s) ρ = F2Poly.eval (stateRef D L s) ρ := by
  unfold stateRefN stateRef repairRefN repairRef
  have hrec : ∀ s', F2Poly.eval (recurRefN D.M ((List.range D.J).map fun j d => decoderRefN D L j d) s') ρ =
      F2Poly.eval (recurRef D.M ((List.range D.J).map fun j d => decoderRef D L j d) s') ρ :=
    fun s' => eval_recurRefN D.M _ _ _ (fun j d ρ => eval_decoderRefN D L j d ρ) s' ρ
  split_ifs
  · rw [eval_nnot, eval_pnot, eval_nsum, eval_psum, eval_psum, List.foldr_map, List.foldr_map]
    congr 1
    congr 1
    funext i b
    rw [hrec]
  · exact hrec s

theorem stateRefN_eval (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ)
    (z : Fin L → Bool) : bitF2 (F2Poly.eval (stateRefN D L s) (ext z)) = D.listStates (List.ofFn z) s := by
  rw [eval_stateRefN]
  exact stateRef_eval D hnest L s z

theorem bitRefN_size (L j h : ℕ) : DegLe (bitRefN D L j h) (2 ^ h) ∧ AtomsLt (bitRefN D L j h) L :=
  binomRefN_size _ L (litsRef_size D j L).1 (litsRef_size D j L).2 _ _

theorem factorRefN_size (L j : ℕ) (d : ℤ) (h : ℕ) :
    DegLe (factorRefN D L j d h) (2 ^ h) ∧ AtomsLt (factorRefN D L j d h) L := by
  unfold factorRefN
  split_ifs
  · exact bitRefN_size D L j h
  · exact ⟨degLe_normalize (degLe_pnot (bitRefN_size D L j h).1),
      atomsLt_normalize (atomsLt_pnot (bitRefN_size D L j h).2)⟩

theorem decoderRefN_size (L j : ℕ) (d : ℤ) :
    DegLe (decoderRefN D L j d) (2 ^ D.ell j - 1) ∧ AtomsLt (decoderRefN D L j d) L := by
  unfold decoderRefN
  split_ifs
  · have hgen : ∀ (l : List ℕ), DegLe (l.foldr (fun h acc => nmul (factorRefN D L j d h) acc) pone)
        (l.map (2 ^ ·)).sum ∧ AtomsLt (l.foldr (fun h acc => nmul (factorRefN D L j d h) acc) pone) L := by
      intro l
      induction l with
      | nil => exact ⟨degLe_pone _, atomsLt_pone L⟩
      | cons h l ih =>
        simp only [List.foldr_cons, List.map_cons, List.sum_cons]
        exact ⟨degLe_normalize (degLe_pmul (factorRefN_size D L j d h).1 ih.1),
          atomsLt_normalize (atomsLt_pmul (factorRefN_size D L j d h).2 ih.2)⟩
    obtain ⟨h1, h2⟩ := hgen (List.range (D.ell j))
    rw [sum_range_list (f := fun h => 2 ^ h)] at h1
    refine ⟨h1.mono ?_, h2⟩
    have := sum_two_pow_range (D.ell j)
    omega
  · exact ⟨degLe_pzero _, atomsLt_pzero L⟩

theorem recurRefN_size (L M : ℕ) (As : List ((ℤ → Poly) × ℕ))
    (hAs : ∀ p ∈ As, ∀ d, DegLe (p.1 d) p.2 ∧ AtomsLt (p.1 d) L) (s : ℕ) :
    DegLe (recurRefN M (As.map Prod.fst) s) (As.map Prod.snd).sum ∧
      AtomsLt (recurRefN M (As.map Prod.fst) s) L := by
  induction As generalizing s with
  | nil =>
    simp only [List.map_nil, recurRefN, List.sum_nil]
    split_ifs
    · exact ⟨degLe_pone 0, atomsLt_pone L⟩
    · exact ⟨degLe_pzero 0, atomsLt_pzero L⟩
  | cons p rest ih =>
    simp only [List.map_cons, recurRefN, List.sum_cons]
    have ih' := fun t => ih (fun q hq => hAs q (List.mem_cons_of_mem _ hq)) t
    refine ⟨degLe_normalize (degLe_psum ?_), atomsLt_normalize (atomsLt_psum ?_)⟩ <;> intro q hq <;>
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
    · have h2 := (hAs p (List.mem_cons_self ..) ((s : ℤ) - 2 * t)).1
      exact degLe_normalize ((degLe_pmul (ih' t).1 h2).mono (by omega))
    · exact atomsLt_normalize (atomsLt_pmul (ih' t).2 (hAs p (List.mem_cons_self ..) ((s : ℤ) - 2 * t)).2)

theorem recurRefN_normal (M : ℕ) (As : List (ℤ → Poly)) (s : ℕ) : IsNormal (recurRefN M As s) := by
  cases As with
  | nil => simp only [recurRefN]; split_ifs; exacts [pone_normal, pzero_normal]
  | cons A rest => exact normalize_normal _

theorem stateRefN_normal (L s : ℕ) : IsNormal (stateRefN D L s) := by
  unfold stateRefN repairRefN
  split_ifs
  · exact normalize_normal _
  · exact recurRefN_normal _ _ _

theorem stateRefN_size (L s : ℕ) :
    DegLe (stateRefN D L s) (∑ j ∈ range D.J, (2 ^ D.ell j - 1)) ∧ AtomsLt (stateRefN D L s) L ∧
      (stateRefN D L s).length ≤ (L + 1) ^ (∑ j ∈ range D.J, (2 ^ D.ell j - 1)) := by
  have hrec : ∀ s', DegLe (recurRefN D.M ((List.range D.J).map fun j d => decoderRefN D L j d) s')
      (∑ j ∈ range D.J, (2 ^ D.ell j - 1)) ∧
      AtomsLt (recurRefN D.M ((List.range D.J).map fun j d => decoderRefN D L j d) s') L := by
    intro s'
    have := recurRefN_size L D.M ((List.range D.J).map fun j => ((fun d => decoderRefN D L j d), 2 ^ D.ell j - 1))
      (by
        intro p hp d
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
        exact decoderRefN_size D L j d) s'
    rw [List.map_map, List.map_map] at this
    rw [← sum_range_list]
    exact this
  have hsz : DegLe (stateRefN D L s) (∑ j ∈ range D.J, (2 ^ D.ell j - 1)) ∧ AtomsLt (stateRefN D L s) L := by
    unfold stateRefN repairRefN
    split_ifs
    · refine ⟨degLe_normalize (degLe_pnot (degLe_normalize (degLe_psum ?_))),
        atomsLt_normalize (atomsLt_pnot (atomsLt_normalize (atomsLt_psum ?_)))⟩ <;> intro q hq <;>
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
      · exact (hrec (i + 1)).1
      · exact (hrec (i + 1)).2
    · exact hrec s
  refine ⟨hsz.1, hsz.2, normal_length_le _ L _ (stateRefN_normal D L s) hsz.1 hsz.2⟩

end Ref

end NearCubicWires.WireExponent3_5.ListMachine
