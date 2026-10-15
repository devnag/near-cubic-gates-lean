import Proof.Wire_3_5.CompilerPolarization
import Proof.CaseAnalysis.FinalPrinterMonomials

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

variable {α : Type}

/-- The monomial of a support: all its children hold. -/
def monoVal (x : ℕ → Bool) (S : Finset ℕ) : Bool := decide (∀ c ∈ S, x c = true)

/-- A child polynomial: the supports of odd multiplicity. -/
abbrev ChildPoly := Finset (Finset ℕ)

/-- Its value: the parity of the true monomials. -/
def ChildPoly.eval (P : ChildPoly) (x : ℕ → Bool) : Bool := decide ((P.filter fun S => monoVal x S).card % 2 = 1)

def monoSupports (children : α → List ℕ) : List α → List (Finset ℕ)
  | [] => [∅]
  | a :: as => (children a).flatMap fun c => (monoSupports children as).map (insert c)

/-- Cancellation of repeated monomials: the symmetric-difference accumulation of a list of supports. -/
def xorCanon (L : List (Finset ℕ)) : ChildPoly := L.foldl (fun P S => symmDiff P {S}) ∅

def substitute (children : α → List ℕ) (p : F2Poly α) : ChildPoly :=
  xorCanon (p.flatMap (monoSupports children))

/-! ## Exactness -/

theorem eval_symmDiff (P : ChildPoly) (S : Finset ℕ) (x : ℕ → Bool) :
    ChildPoly.eval (symmDiff P {S}) x = xor (ChildPoly.eval P x) (monoVal x S) := by
  unfold ChildPoly.eval
  by_cases hS : S ∈ P
  · have hsd : symmDiff P {S} = P.erase S := by
      ext T; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h2, h1⟩
        · subst h1; exact absurd hS h2
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h2, h1⟩
    rw [hsd, Finset.filter_erase]
    by_cases hm : monoVal x S = true
    · have hmem : S ∈ P.filter fun S => monoVal x S := Finset.mem_filter.mpr ⟨hS, hm⟩
      rw [Finset.card_erase_of_mem hmem, hm]
      have hpos : 0 < (P.filter fun S => monoVal x S).card := Finset.card_pos.mpr ⟨S, hmem⟩
      by_cases hc : (P.filter fun S => monoVal x S).card % 2 = 1
      · have h2 : ¬ (((P.filter fun S => monoVal x S).card - 1) % 2 = 1) := by omega
        simp [hc, h2]
      · have h2 : ((P.filter fun S => monoVal x S).card - 1) % 2 = 1 := by omega
        simp [hc, h2]
    · have hnot : S ∉ P.filter fun S => monoVal x S := by simp [hm]
      rw [Finset.erase_eq_of_notMem hnot]
      simp at hm; simp [hm]
  · have hsd : symmDiff P {S} = insert S P := by
      ext T; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inr h1
        · exact Or.inl h1
      · rintro (h | h)
        · subst h; exact Or.inr ⟨rfl, hS⟩
        · exact Or.inl ⟨h, fun h' => hS (h' ▸ h)⟩
    rw [hsd, Finset.filter_insert]
    by_cases hm : monoVal x S = true
    · rw [if_pos hm, Finset.card_insert_of_notMem (by simp [hS]), hm]
      by_cases hc : (P.filter fun S => monoVal x S).card % 2 = 1
      · have h2 : ¬ (((P.filter fun S => monoVal x S).card + 1) % 2 = 1) := by omega
        simp [hc, h2]
      · have h2 : ((P.filter fun S => monoVal x S).card + 1) % 2 = 1 := by omega
        simp [hc, h2]
    · simp at hm; simp [hm]

theorem xorCanon_eval (L : List (Finset ℕ)) (x : ℕ → Bool) :
    ChildPoly.eval (xorCanon L) x = xorAll (L.map (monoVal x)) := by
  have gen : ∀ (P : ChildPoly), ChildPoly.eval (L.foldl (fun P S => symmDiff P {S}) P) x =
      xor (ChildPoly.eval P x) (xorAll (L.map (monoVal x))) := by
    induction L with
    | nil => intro P; simp [xorAll]
    | cons S L ih =>
      intro P
      rw [List.foldl_cons, ih, eval_symmDiff]
      simp only [List.map_cons, xorAll, Bool.xor_assoc]
  unfold xorCanon
  rw [gen]
  simp [ChildPoly.eval]

theorem xorAll_append (l l' : List Bool) : xorAll (l ++ l') = xor (xorAll l) (xorAll l') := by
  induction l with
  | nil => simp [xorAll]
  | cons b l ih => simp [xorAll, ih]

theorem xorAll_flatMap {β : Type} (l : List β) (f : β → List Bool) :
    xorAll (l.flatMap f) = xorAll (l.map fun b => xorAll (f b)) := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, xorAll_append, ih]; rfl

theorem xorAll_map_and {β : Type} (l : List β) (f : β → Bool) (y : Bool) :
    xorAll (l.map fun b => f b && y) = (xorAll (l.map f) && y) := by
  induction l with
  | nil => simp [xorAll]
  | cons b l ih => simp only [List.map_cons, xorAll, ih]; cases f b <;> cases y <;> simp

theorem monoVal_insert (x : ℕ → Bool) (c : ℕ) (S : Finset ℕ) : monoVal x (insert c S) = (x c && monoVal x S) := by
  simp [monoVal]

/-- A child list is exact for an atom value when the bits of its children sum to the atom's bit (`alg:disjoint`:
disjoint, so at most one child holds). -/
def ExactChildren (children : α → List ℕ) (x : ℕ → Bool) (ρ : α → Bool) : Prop :=
  ∀ a, bitZ (ρ a) = ((children a).map fun c => bitZ (x c)).sum

theorem bitZ_xor (a b : Bool) : bitZ (xor a b) = (bitZ a + bitZ b) % 2 := by
  cases a <;> cases b <;> decide

theorem bitZ_xorAll_map (l : List ℕ) (x : ℕ → Bool) :
    bitZ (xorAll (l.map x)) = (l.map fun c => bitZ (x c)).sum % 2 := by
  induction l with
  | nil => simp [xorAll, bitZ]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, xorAll]
    rw [bitZ_xor, ih, Int.add_emod_emod]

/-- For exact children, the parity of the children is the atom's value (the sum is `0` or `1`). -/
theorem xorAll_children (children : α → List ℕ) (x : ℕ → Bool) (ρ : α → Bool)
    (h : ExactChildren children x ρ) (a : α) : xorAll ((children a).map x) = ρ a := by
  have h1 := bitZ_xorAll_map (children a) x
  rw [← h a] at h1
  cases hρ : ρ a <;> cases hx : xorAll ((children a).map x) <;> simp only [bitZ, hρ, hx] at h1 ⊢ <;> simp at h1

theorem monoSupports_eval (children : α → List ℕ) (x : ℕ → Bool) (ρ : α → Bool)
    (h : ExactChildren children x ρ) (mono : List α) :
    xorAll ((monoSupports children mono).map (monoVal x)) = mono.all ρ := by
  induction mono with
  | nil => simp [monoSupports, xorAll, monoVal]
  | cons a as ih =>
    simp only [monoSupports, List.map_flatMap, List.all_cons]
    rw [show ((children a).flatMap fun c => ((monoSupports children as).map (insert c)).map (monoVal x)) =
        (children a).flatMap fun c => (monoSupports children as).map fun S => (x c && monoVal x S) by
      congr 1; funext c; rw [List.map_map]; congr 1; funext S; exact monoVal_insert x c S]
    rw [xorAll_flatMap]
    have : ((children a).map fun c => xorAll ((monoSupports children as).map fun S => (x c && monoVal x S))) =
        (children a).map fun c => (x c && as.all ρ) := by
      congr 1; funext c
      rw [show ((monoSupports children as).map fun S => (x c && monoVal x S)) =
          ((monoSupports children as).map fun S => (monoVal x S && x c)) by congr 1; funext S; exact Bool.and_comm _ _]
      rw [xorAll_map_and, ih, Bool.and_comm]
    rw [this, xorAll_map_and, xorAll_children children x ρ h a]

theorem F2Poly.eval_eq_xorAll (p : F2Poly α) (ρ : α → Bool) :
    F2Poly.eval p ρ = xorAll (p.map fun m => m.all ρ) := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    have := F2Poly.eval_append [m] p ρ
    simp only [List.singleton_append] at this
    rw [this, ih]
    simp [F2Poly.eval, xorAll]

theorem substitute_eval (children : α → List ℕ) (x : ℕ → Bool) (ρ : α → Bool) (h : ExactChildren children x ρ)
    (p : F2Poly α) : ChildPoly.eval (substitute children p) x = F2Poly.eval p ρ := by
  unfold substitute
  rw [xorCanon_eval, List.map_flatMap, xorAll_flatMap, F2Poly.eval_eq_xorAll]
  congr 1
  apply List.map_congr_left
  intro m _
  exact monoSupports_eval children x ρ h m

/-! ## The monomial count -/

theorem mem_monoSupports (children : α → List ℕ) (mono : List α) (S : Finset ℕ)
    (hS : S ∈ monoSupports children mono) :
    S.card ≤ mono.length ∧ ∀ c ∈ S, ∃ a ∈ mono, c ∈ children a := by
  induction mono generalizing S with
  | nil => simp [monoSupports] at hS; subst hS; simp
  | cons a as ih =>
    simp only [monoSupports, List.mem_flatMap, List.mem_map] at hS
    obtain ⟨c, hc, T, hT, rfl⟩ := hS
    obtain ⟨h1, h2⟩ := ih T hT
    refine ⟨(Finset.card_insert_le c T).trans (by simp; omega), fun c' hc' => ?_⟩
    rcases Finset.mem_insert.mp hc' with rfl | hc'
    · exact ⟨a, List.mem_cons_self, hc⟩
    · obtain ⟨b, hb, hb'⟩ := h2 c' hc'
      exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

theorem xorCanon_subset (L : List (Finset ℕ)) : xorCanon L ⊆ L.toFinset := by
  have gen : ∀ (P : ChildPoly), (L.foldl (fun P S => symmDiff P {S}) P) ⊆ P ∪ L.toFinset := by
    induction L with
    | nil => intro P; simp
    | cons S L ih =>
      intro P
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      intro T hT
      simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_singleton, List.toFinset_cons,
        Finset.mem_insert, List.mem_toFinset] at hT ⊢
      tauto
  unfold xorCanon
  exact (gen ∅).trans (by simp)

/-- Every support of a substituted polynomial lies in the child pool and has at most `d` labels. -/
theorem substitute_subset (children : α → List ℕ) (p : F2Poly α) (pool : Finset ℕ) (d : ℕ)
    (hpool : ∀ m ∈ p, ∀ a ∈ m, ∀ c ∈ children a, c ∈ pool) (hd : ∀ m ∈ p, m.length ≤ d) :
    substitute children p ⊆ (pool.powerset.filter fun S => S.card ≤ d) := by
  intro S hS
  have hS' := xorCanon_subset _ hS
  simp only [List.mem_toFinset, List.mem_flatMap] at hS'
  obtain ⟨m, hm, hSm⟩ := hS'
  obtain ⟨hcard, hsub⟩ := mem_monoSupports children m S hSm
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun c hc => ?_, hcard.trans (hd m hm)⟩
  obtain ⟨a, ha, hca⟩ := hsub c hc
  exact hpool m hm a ha c hca

theorem card_powerset_filter_le (pool : Finset ℕ) (d : ℕ) :
    (pool.powerset.filter fun S => S.card ≤ d).card ≤ (pool.card + 1) ^ d := by
  calc (pool.powerset.filter fun S => S.card ≤ d).card
      ≤ ((Finset.range (d + 1)).biUnion fun j => pool.powersetCard j).card := by
        apply Finset.card_le_card
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
        exact ⟨S.card, by omega, hS.1, rfl⟩
    _ ≤ ∑ j ∈ Finset.range (d + 1), (pool.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (d + 1), pool.card.choose j := by simp [Finset.card_powersetCard]
    _ ≤ (pool.card + 1) ^ d := RepairSource.CloseoutFinal.C10PrinterMonomials.sum_choose_le_succ_pow _ _

theorem substitute_card_le (children : α → List ℕ) (p : F2Poly α) (pool : Finset ℕ) (d : ℕ)
    (hpool : ∀ m ∈ p, ∀ a ∈ m, ∀ c ∈ children a, c ∈ pool) (hd : ∀ m ∈ p, m.length ≤ d) :
    (substitute children p).card ≤ (pool.card + 1) ^ d :=
  (Finset.card_le_card (substitute_subset children p pool d hpool hd)).trans (card_powerset_filter_le pool d)

/-! ## A canonical listing -/

/-- The supports of a child polynomial, listed in the order of `Σ_{c∈S} 2^c` (computable). -/
def listSupports (P : ChildPoly) : List (Finset ℕ) :=
  ((P.image Finset.equivBitIndices.symm).sort (· ≤ ·)).map Finset.equivBitIndices

theorem mem_listSupports (P : ChildPoly) (S : Finset ℕ) : S ∈ listSupports P ↔ S ∈ P := by
  simp only [listSupports, List.mem_map, Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨n, ⟨T, hT, rfl⟩, rfl⟩; simpa using hT
  · intro hS; exact ⟨_, ⟨S, hS, rfl⟩, by simp⟩

theorem listSupports_nodup (P : ChildPoly) : (listSupports P).Nodup :=
  (Finset.sort_nodup _ _).map Finset.equivBitIndices.injective

theorem listSupports_length (P : ChildPoly) : (listSupports P).length = P.card := by
  rw [← List.toFinset_card_of_nodup (listSupports_nodup P)]
  congr 1; ext S; simp [mem_listSupports]

/-- The parity of the true supports in the listing is the child polynomial's value. -/
theorem listSupports_filter_length (P : ChildPoly) (x : ℕ → Bool) :
    ((listSupports P).filter (monoVal x)).length = (P.filter fun S => monoVal x S).card := by
  rw [← List.toFinset_card_of_nodup ((listSupports_nodup P).filter _)]
  congr 1; ext S; simp [mem_listSupports]

end NearCubicWires.WireExponent3_5.Compiler
