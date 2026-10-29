import SourceAdapters.ShortPCP.Machines.FLangAns

/-!
# Single-run time, reference layer 11: proof-bit addresses in blocks

proof of `thm:short-pcp-ours` ("five tables of elements of F, which we encode in binary with f bits per element") and proof of `thm:short-pcp-ours`
("its proof bits are read at addresses below L_π"): every query of `V1` reads one element, i.e. one block of `f`
consecutive oracle bits `k·f, …, k·f + f − 1` (`Request.wordAt`). The address list of the query half is a list of
such blocks; the decision half reads the answer bits of block `bi` as the word `bitsValue (…) / 2^(bi·f) % 2^f`
(`block_word`). `wordOf_elt`: the join's `wordOf` inverts `elt` on reduced words.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicWires NearCubicWires.CanonicalBinary NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun NearCubicWires.WireExponent3_5
open NearCubicGates.Published.BCGT13

theorem bv_append (u w : List Bool) : bitsValue (u ++ w) = bitsValue u + 2 ^ u.length * bitsValue w := by
  induction u with
  | nil => simp [bitsValue]
  | cons b u ih => simp only [List.cons_append, bitsValue, ih, List.length_cons, pow_succ]; ring

/-- The bits of one block: element `k`, `f` bits, least significant first. -/
def blockBits (o : ℕ → Bool) (f k : ℕ) : List Bool := (List.range f).map fun b => o (k * f + b)

/-- The addresses of a list of blocks. -/
def blockAddrs (f : ℕ) (L : List ℕ) : List ℕ := L.flatMap fun k => (List.range f).map fun b => k * f + b

theorem blockAddrs_map (o : ℕ → Bool) (f : ℕ) (L : List ℕ) :
    (blockAddrs f L).map o = L.flatMap (blockBits o f) := by
  simp [blockAddrs, List.map_flatMap]; rfl

theorem bv_blocks (o : ℕ → Bool) (f : ℕ) :
    ∀ L : List ℕ, bitsValue (L.flatMap (blockBits o f)) = packW f (L.map fun k => bitsValue (blockBits o f k))
  | [] => rfl
  | k :: L => by
    rw [List.flatMap_cons, bv_append, bv_blocks o f L, List.map_cons, packW]
    simp [blockBits]

/-- **The word of block `bi`.** -/
theorem block_word (o : ℕ → Bool) (f : ℕ) (L : List ℕ) (bi : ℕ) (hbi : bi < L.length) :
    bitsValue ((blockAddrs f L).map o) / 2 ^ (bi * f) % 2 ^ f = bitsValue (blockBits o f (L[bi])) := by
  rw [blockAddrs_map, bv_blocks, packW_get f _ (by
    intro a ha; simp only [List.mem_map] at ha; obtain ⟨k, -, rfl⟩ := ha
    have := bv_lt (blockBits o f k); simpa [blockBits] using this)]
  rw [List.getD_eq_getElem _ _ (by simpa using hbi)]; simp

theorem wordAt_eq (q : Request) (o : ℕ → Bool) (k : ℕ) : q.wordAt o k = bitsValue (blockBits o q.code.f k) := rfl

/-- `wordOf` inverts `elt` on reduced words. -/
theorem wordOf_elt (q : Request) {F : Type} [Field F] [DecidableEq F] (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (hφ : Function.Bijective φ) (hmod : GF.ModulusOk q.code.irr q.code.f) (w : ℕ) (hw : w < 2 ^ q.code.f) :
    q.wordOf φ (q.elt φ w) = w := by
  classical
  have hex : ∃ w', w' < 2 ^ q.code.f ∧ q.elt φ w' = q.elt φ w := ⟨w, hw, rfl⟩
  unfold Request.wordOf
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  exact GF.rep_injOn q.code.irr q.code.f _ _ hmod h1 hw (hφ.1 h2)

/-- The domain's element of index `j` is the element of word `j − 1`. -/
theorem dom_eltWithIndex (q : Request) {F : Type} [Field F] (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (hφ : Function.Bijective φ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2 ^ q.code.f) :
    eltWithIndex (q.domBasis φ) 0 j = q.elt φ (j - 1) := by
  rw [eltWithIndex_eq, add_zero]
  unfold Request.domBasis
  rw [sel_domList q φ hφ, Nat.mod_eq_of_lt (by omega)]

/-- **An answer read from its block is the join's answer** (`answersN` on the decoded tables): the implicit input
`p a = elt (wordAt o (pB + wordOf a)) + pxF a`, the proof `πN t = elt (wordAt o (πB + t))`. -/
theorem ansVal_eq_answersN (q : Request) {F : Type} [Field F] [DecidableEq F]
    (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (hφ : Function.Bijective φ)
    (hmod : GF.ModulusOk q.code.irr q.code.f) (X : NearCubicGates.Published.BCGT13.FlatVerifier F) (o : ℕ → Bool)
    (u : List Bool) (i pB πB : ℕ) (pxF : F → F) (px : Bool)
    (hpx : px = false → ∀ a, pxF a = 0) :
    ansVal (X.Q u i) (2 ^ q.code.f) X.length
        (q.elt φ (q.wordAt o (elemOf (X.Q u i) (2 ^ q.code.f) X.length pB πB)))
        (fun x => pxF (q.elt φ x)) px =
      answersN X (q.domBasis φ) 0 (fun a => q.elt φ (q.wordAt o (pB + q.wordOf φ a)) + pxF a)
        (fun t => q.elt φ (q.wordAt o (πB + t))) u i := by
  have hB : (q.domBasis φ).length = q.code.f := by simp [Request.domBasis]
  unfold answersN
  rw [hB]
  cases X.Q u i with
  | none => rfl
  | some j =>
    simp only [ansVal, elemOf]
    by_cases h1 : 1 ≤ j ∧ j ≤ 2 ^ q.code.f
    · rw [if_pos h1, if_pos h1, if_pos h1, dom_eltWithIndex q φ hφ j h1.1 h1.2,
        wordOf_elt q φ hφ hmod _ (by omega)]
      cases px
      · simp [hpx rfl]
      · rfl
    · rw [if_neg h1, if_neg h1, if_neg h1]
      by_cases h2 : j - 2 ^ q.code.f - 1 < X.length ∧ 2 ^ q.code.f < j
      · rw [if_pos h2, if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]

end NearCubicGates.Adapters.ShortPCP.Time
