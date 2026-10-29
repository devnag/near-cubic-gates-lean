import SourceAdapters.ShortPCP.TimeAddr
import SourceAdapters.ShortPCP.VerifierSize

/-!
# Single-run time, reference layer 12: the block list of `V1`

proof of `thm:short-pcp-ours` ("The queries of V0 are computed from the random string alone"), proof of `thm:short-pcp-ours` (five tables, `f`
bits per element) and proof of `thm:short-pcp-ours` (`V1` runs `V0` on `R ⊕ σ` for every `σ ∈ S`): the proof elements `V1` reads on
coins `R`, in reading order. For each mask `σ` (coins `c = R ⊕ σ`): the effective queries of `V_RS` on `p0`
(`TimeBlocks.idxO`), of `V_VRS` on `p1`, the consistency test's `cN` neighbours `p0(N_i(α))` and `p1(α)`
(`α` = first `f` coins), and the effective queries of `V_VRS` on `p0 − p_x` (`blkS`). The list is defined over the
canonical field `𝔽₂[X]/(irr)` (`blocks`), so it does not depend on the field the join quantifies over; the machine
specs show the queries agree for every field (`FLangSub`). Each mask contributes the same number `T q` of blocks.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicWires NearCubicWires.CanonicalBinary NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun NearCubicWires.WireExponent3_5
open NearCubicGates.Published.BCGT13

/-! ## Coins -/

theorem div_two_pow_mod_two (x i : ℕ) : x / 2 ^ i % 2 = (x.testBit i).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

/-- The coin number `bitsValue R ⊕ bitsValue σ` has the masked coins as its bits. -/
theorem maskedCoins_bits (R σ : List Bool) (i : ℕ) :
    (bitsValue R ^^^ bitsValue σ) / 2 ^ i % 2 = (Request.maskedCoins R σ i).toNat := by
  have hR := testBit_bitsValue R i
  have hσ := testBit_bitsValue σ i
  rw [div_two_pow_mod_two] at hR hσ ⊢
  rw [Nat.testBit_xor, Request.maskedCoins]
  have e1 : (bitsValue R).testBit i = R.getD i false := by
    cases h1 : (bitsValue R).testBit i <;> cases h2 : R.getD i false <;> simp_all
  have e2 : (bitsValue σ).testBit i = σ.getD i false := by
    cases h1 : (bitsValue σ).testBit i <;> cases h2 : σ.getD i false <;> simp_all
  rw [e1, e2]

/-- The coin prefix of length `r` as a number. -/
theorem bv_coins (c : ℕ → Bool) (x r : ℕ) (hx : ∀ i, x / 2 ^ i % 2 = (c i).toNat) :
    bitsValue ((List.range r).map c) = x % 2 ^ r :=
  bitsValue_range_mod c x r (fun i _ => hx i)

/-! ## The number of effective queries is bounded -/

theorem qcO_le (v : Bool) (f d : ℕ) : qcO v f d ≤ 103 := by
  have hq := queryEq_le16 f
  unfold qcO qcI
  by_cases ht : trivB f d = true
  · rw [if_pos ht]; cases v <;> simp
  · rw [if_neg ht]
    have hq' : qRS f d ≤ 101 := by
      unfold qRS
      by_cases h2 : f ≤ 2
      · rw [if_pos h2]
        have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
        omega
      rw [if_neg h2]
      split_ifs with h3 h4 h5
      · omega
      · omega
      · have hd : d < 2 ^ f := by simp only [trivB, decide_eq_true_eq, not_and, not_le] at ht; exact ht (by omega)
        have hm := NearCubicGates.Adapters.ShortPCP.mKED_le f 2 d (by omega) hd
        have : mKED f 2 d * queryEq T0 f ≤ 4 * 16 := Nat.mul_le_mul hm hq
        omega
      · have hd : d < 2 ^ f := by simp only [trivB, decide_eq_true_eq, not_and, not_le] at ht; exact ht (by omega)
        have hm := NearCubicGates.Adapters.ShortPCP.mKED_le f 2 d (by omega) hd
        have : mKED f 2 d * queryEq T0 f ≤ 4 * 16 := Nat.mul_le_mul hm hq
        omega
    cases v <;> simp <;> omega

/-! ## The blocks of one sub-verifier run -/

section Blocks

variable {F : Type} [Field F] [DecidableEq F]

/-- The elements read by the effective queries of the outer verifier `outV v B 0 BH OH d` on coins `u`
(implicit input at element `pB + j − 1`, proof at `πB + t`). -/
def blkX (v : Bool) (B BH : List F) (OH : F) (d len pB πB : ℕ) (u : List Bool) : List ℕ :=
  (List.range (qcO v B.length (innD v BH.length d))).map fun k =>
    elemOf ((outV v B 0 BH OH d).Q u (idxO B.length (innD v BH.length d) (k + 1))) (2 ^ B.length) len pB πB

theorem blkX_length (v : Bool) (B BH : List F) (OH : F) (d len pB πB : ℕ) (u : List Bool) :
    (blkX v B BH OH d len pB πB u).length = qcO v B.length (innD v BH.length d) := by
  simp [blkX]

theorem blkX_getD (v : Bool) (B BH : List F) (OH : F) (d len pB πB : ℕ) (u : List Bool) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ qcO v B.length (innD v BH.length d)) :
    (blkX v B BH OH d len pB πB u).getD (k - 1) 0 =
      elemOf ((outV v B 0 BH OH d).Q u (idxO B.length (innD v BH.length d) k)) (2 ^ B.length) len pB πB := by
  rw [blkX, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.sub_add_cancel hk1]

variable (q : Request) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)

/-- The inner degree of `V_H` and of `V_I`. -/
def dH (q : Request) : ℕ := innD true q.code.hBasis.length q.dB
def dI (q : Request) : ℕ := innD true (iBw q).length q.dA

/-- The table lengths `|π0|`, `|π1|`, `|πc|` (closed forms). -/
def lenR (q : Request) : ℕ := outLen false q.code.f q.dA
def lenH (q : Request) : ℕ := outLen true q.code.f (dH q)
def lenI (q : Request) : ℕ := outLen true q.code.f (dI q)

/-- The coin lengths of the three runs. -/
def randR (q : Request) : ℕ := outRand false q.code.f q.dA
def randH (q : Request) : ℕ := outRand true q.code.f (dH q)
def randI (q : Request) : ℕ := outRand true q.code.f (dI q)

/-- The consistency point's word: the first `f` coins. -/
def alphaW (q : Request) (c : ℕ → Bool) : ℕ := bitsValue ((List.range q.code.f).map c)

/-- The blocks of the consistency test: `p0` at the neighbours, then `p1` at `α`. -/
def blkC (q : Request) (c : ℕ → Bool) : List ℕ :=
  (List.range q.code.cN).map (fun i => nbW q q.code.irr (alphaW q c) i) ++
    [2 ^ q.code.f + lenR q + alphaW q c]

/-- **The blocks of `V0` on coins `c`** (Construction 8.5 Steps 2–5, in the order of `runVerdict`). -/
def blkS (c : ℕ → Bool) : List ℕ :=
  blkX false (q.domBasis φ) [] 0 q.dA (lenR q) 0 (2 ^ q.code.f) ((List.range (randR q)).map c) ++
  blkX true (q.domBasis φ) (q.hB φ) (q.hO φ) q.dB (lenH q) (2 ^ q.code.f + lenR q) (2 * 2 ^ q.code.f + lenR q)
    ((List.range (randH q)).map c) ++
  blkC q c ++
  blkX true (q.domBasis φ) (q.iB φ) (q.iO φ) q.dA (lenI q) 0 (2 * 2 ^ q.code.f + lenR q + lenH q)
    ((List.range (randI q)).map c)

/-- The number of blocks per mask. -/
def qcR (q : Request) : ℕ := qcO false q.code.f q.dA
def qcH (q : Request) : ℕ := qcO true q.code.f (dH q)
def qcIo (q : Request) : ℕ := qcO true q.code.f (dI q)
def nT (q : Request) : ℕ := qcR q + qcH q + (q.code.cN + 1) + qcIo q

omit [DecidableEq F] in
theorem domBasis_length : (q.domBasis φ).length = q.code.f := by simp [Request.domBasis]

theorem blkS_length (c : ℕ → Bool) : (blkS q φ c).length = nT q := by
  simp only [blkS, List.length_append, blkX_length, domBasis_length, blkC, List.length_map, List.length_range,
    List.length_singleton, Request.hB, Request.iB, nT, qcR, qcH, qcIo, dH, dI, innD, List.length_nil, iBw]
  simp only [Bool.false_eq_true, ↓reduceIte]

end Blocks

/-! ## The blocks of `V1` over the canonical field -/

/-- The blocks of all masks for one field. -/
def blkAll {F : Type} [Field F] [DecidableEq F] (q : Request) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (R : List Bool) : List ℕ :=
  q.masks.flatMap fun σ => blkS q φ (Request.maskedCoins R σ)

/-- **The blocks of `V1` on coins `R`**, over `𝔽₂[X]/(irr)` (empty if `irr` is reducible). -/
def blocks (q : Request) (R : List Bool) : List ℕ :=
  open Classical in
  if h : Irreducible (GF.toPoly q.code.irr) then
    letI : Fact (Irreducible (GF.toPoly q.code.irr)) := ⟨h⟩
    letI : DecidableEq (AdjoinRoot (GF.toPoly q.code.irr)) := Classical.decEq _
    blkAll q (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr))) R
  else []

/-- **The proof-bit addresses of `V1` on coins `R`** (`f` bits per block). -/
def xsOf (q : Request) (R : List Bool) : List ℕ := blockAddrs q.code.f (blocks q R)

theorem flatMap_getD_const {α : Type} (L : List α) (g : α → List ℕ) (T : ℕ) (hg : ∀ x ∈ L, (g x).length = T)
    (i j : ℕ) (hi : i < L.length) (hj : j < T) :
    (L.flatMap g).getD (i * T + j) 0 = (g L[i]).getD j 0 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    rw [List.flatMap_cons]
    rcases i with _ | i
    · rw [List.getD_append _ _ _ _ (by rw [hg x (by simp)]; omega)]; simp
    · have hiT : T ≤ (i + 1) * T + j := by nlinarith
      rw [List.getD_append_right _ _ _ _ (by rw [hg x (by simp)]; exact hiT), hg x (by simp),
        show (i + 1) * T + j - T = i * T + j by rw [add_mul, one_mul]; omega,
        ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) i (by simp at hi; omega)]
      simp

theorem flatMap_length_const {α : Type} (L : List α) (g : α → List ℕ) (T : ℕ) (hg : ∀ x ∈ L, (g x).length = T) :
    (L.flatMap g).length = L.length * T := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, hg x (by simp), ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))]
    simp [add_mul, add_comm]

theorem blkAll_length {F : Type} [Field F] [DecidableEq F] (q : Request) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (R : List Bool) : (blkAll q φ R).length = q.masks.length * nT q :=
  flatMap_length_const _ _ _ (fun _ _ => blkS_length q φ _)

/-- Block `i·T + j` of all masks is block `j` of mask `i`. -/
theorem blkAll_getD {F : Type} [Field F] [DecidableEq F] (q : Request) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (R : List Bool) (i j : ℕ) (hi : i < q.masks.length) (hj : j < nT q) :
    (blkAll q φ R).getD (i * nT q + j) 0 = (blkS q φ (Request.maskedCoins R q.masks[i])).getD j 0 := by
  rw [blkAll, flatMap_getD_const _ _ _ (fun _ _ => blkS_length q φ _) i j hi hj]

/-- The word of block `bi` of the answer bits. -/
theorem block_wordD (q : Request) (o : ℕ → Bool) (L : List ℕ) (bi : ℕ) (hbi : bi < L.length) :
    bitsValue ((blockAddrs q.code.f L).map o) / 2 ^ (bi * q.code.f) % 2 ^ q.code.f = q.wordAt o (L.getD bi 0) := by
  rw [block_word o q.code.f L bi hbi, List.getD_eq_getElem _ _ hbi]; rfl

end NearCubicGates.Adapters.ShortPCP.Time
