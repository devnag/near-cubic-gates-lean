import Proof.Wire_3_5.CompilerMachineKit2
import Proof.Wire_3_5.CompilerMachineStream

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-! ## Entries as words -/

/-- The size field: `k` ones, then `Q - k` zeros. -/
def thermo (Q k : ℕ) : List Bool := List.replicate k true ++ List.replicate (Q - k) false

/-- A union entry `(k, U)` as a word: the size field, a marker, the mask bits (low label first). -/
def entryWord (Q W k U : ℕ) : List Bool := thermo Q k ++ (true :: binary W U)

@[simp] theorem thermo_length (Q k : ℕ) (hk : k ≤ Q) : (thermo Q k).length = Q := by
  simp [thermo]; omega

@[simp] theorem entryWord_length (Q W k U : ℕ) (hk : k ≤ Q) : (entryWord Q W k U).length = Q + W + 1 := by
  simp [entryWord, hk]; omega

theorem thermo_getElem (Q k i : ℕ) (hi : i < (thermo Q k).length) : (thermo Q k)[i] = decide (i < k) := by
  unfold thermo
  by_cases h : i < k
  · rw [List.getElem_append_left (by simp; omega)]; simp [h]
  · rw [List.getElem_append_right (by simp; omega)]; simp [h]

theorem entryWord_getElem (Q W k U i : ℕ) (hk : k ≤ Q) (hi : i < (entryWord Q W k U).length) :
    (entryWord Q W k U)[i] = if i < Q then decide (i < k) else if i = Q then true else U.testBit (i - Q - 1) := by
  unfold entryWord
  by_cases h1 : i < Q
  · rw [List.getElem_append_left (by rw [thermo_length Q k hk]; exact h1), thermo_getElem Q k i, if_pos h1]
  · rw [List.getElem_append_right (by rw [thermo_length Q k hk]; omega), if_neg h1]
    simp only [thermo_length Q k hk]
    by_cases h2 : i = Q
    · rw [if_pos h2]
      simp only [h2, Nat.sub_self, List.getElem_cons_zero]
    · rw [if_neg h2, List.getElem_cons, dif_neg (by omega), binary_getElem]

theorem entryWord_inj (Q W k k' U U' : ℕ) (hk : k ≤ Q) (hk' : k' ≤ Q) (hU : U < 2 ^ W) (hU' : U' < 2 ^ W)
    (h : entryWord Q W k U = entryWord Q W k' U') : k = k' ∧ U = U' := by
  unfold entryWord at h
  have hl : (thermo Q k).length = (thermo Q k').length := by rw [thermo_length Q k hk, thermo_length Q k' hk']
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  refine ⟨?_, ?_⟩
  · have := congrArg (fun l => l.count true) h1
    simpa [thermo, List.count_replicate] using this
  · have h3 : binary W U = binary W U' := (List.cons.inj h2).2
    have h4 := congrArg RadixSemantics.value h3
    rwa [binary_value W U hU, binary_value W U' hU'] at h4

/-! ## The templates and the three word operations -/

/-- The template of the last size bit. -/
def lastT (Q W : ℕ) : List Bool := List.replicate (Q - 1) false ++ [true] ++ List.replicate (W + 1) false

/-- The template of the size field. -/
def levelT (Q W : ℕ) : List Bool := List.replicate Q true ++ List.replicate (W + 1) false

/-- The zero word of an entry's width. -/
def zeroT (Q W : ℕ) : List Bool := List.replicate (Q + W + 1) false

/-- The shifted copy: under the template, the previous input bit (the state); elsewhere the input bit. -/
def incrOut (a b st : Bool) : Bool := if b then st else a

/-- The state of the shifted copy is the input bit just read. -/
def incrNxt (a _ _ : Bool) : Bool := a

/-- Is the size below `Q`: the masked last size bit is zero. -/
def testW (Q W : ℕ) (r : List Bool) : Bool := decide (ZipMap.map andOut keep r (lastT Q W) false = zeroT Q W)

/-- The size plus one. -/
def incrW (Q W : ℕ) (r : List Bool) : List Bool := ZipMap.map incrOut incrNxt r (levelT Q W) true

/-- The union of the masks. -/
def orW (r g : List Bool) : List Bool := ZipMap.map orOut keep r g false

/-- **One lift step on words**: the old entries, the extensions of those below size `Q` by `g`, and `g`'s entry. -/
def liftStepW (Q W : ℕ) (E : List (List Bool)) (g : List Bool) : List (List Bool) :=
  E ++ (E.filter (testW Q W)).map (fun r => orW (incrW Q W r) g) ++ [incrW Q W g]

theorem map_keep_getElem (out : Bool → Bool → Bool → Bool) (st : Bool) :
    ∀ (l r : List Bool) (hl : l.length = r.length) (i : ℕ) (hi : i < (ZipMap.map out keep l r st).length),
      (ZipMap.map out keep l r st)[i] = out (l[i]'(by rw [ZipMap.map_length out keep l r st hl] at hi; exact hi))
        (r[i]'(by rw [ZipMap.map_length out keep l r st hl] at hi; omega)) st
  | [], _, _, i, hi => by simp [ZipMap.map] at hi
  | a :: l, [], hl, _, _ => by simp at hl
  | a :: l, b :: r, hl, 0, _ => by simp [ZipMap.map, keep]
  | a :: l, b :: r, hl, i + 1, hi => by
    simp only [ZipMap.map, keep, List.getElem_cons_succ]
    exact map_keep_getElem out st l r (by simpa using hl) i _

theorem map_incr_getElem : ∀ (l r : List Bool) (st : Bool) (hl : l.length = r.length) (i : ℕ)
    (hi : i < (ZipMap.map incrOut incrNxt l r st).length),
    (ZipMap.map incrOut incrNxt l r st)[i] =
      if r[i]'(by rw [ZipMap.map_length _ _ l r st hl] at hi; omega) then
        (if h : i = 0 then st else l[i - 1]'(by rw [ZipMap.map_length _ _ l r st hl] at hi; omega))
      else l[i]'(by rw [ZipMap.map_length _ _ l r st hl] at hi; exact hi)
  | [], _, _, _, i, hi => by simp [ZipMap.map] at hi
  | a :: l, [], _, hl, _, _ => by simp at hl
  | a :: l, b :: r, st, hl, 0, _ => by simp [ZipMap.map, incrOut]
  | a :: l, b :: r, st, hl, i + 1, hi => by
    simp only [ZipMap.map, List.getElem_cons_succ, incrNxt]
    rw [map_incr_getElem l r a (by simpa using hl) i]
    cases i with
    | zero => simp
    | succ i => simp

theorem lastT_length (Q W : ℕ) (hQ : 1 ≤ Q) : (lastT Q W).length = Q + W + 1 := by simp [lastT]; omega

theorem levelT_length (Q W : ℕ) : (levelT Q W).length = Q + W + 1 := by simp [levelT]; omega

theorem lastT_getElem (Q W i : ℕ) (hQ : 1 ≤ Q) (hi : i < (lastT Q W).length) : (lastT Q W)[i] = decide (i = Q - 1) := by
  unfold lastT
  by_cases h1 : i < Q - 1
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp; omega
  · by_cases h2 : i = Q - 1
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp [h2]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [h2]

theorem levelT_getElem (Q W i : ℕ) (hi : i < (levelT Q W).length) : (levelT Q W)[i] = decide (i < Q) := by
  unfold levelT
  by_cases h1 : i < Q
  · rw [List.getElem_append_left (by simp; omega)]; simp [h1]
  · rw [List.getElem_append_right (by simp; omega)]; simp [h1]

/-- **The size test on an entry**: below `Q` exactly when `k < Q`. -/
theorem testW_entry (Q W k U : ℕ) (hQ : 1 ≤ Q) (hk : k ≤ Q) : testW Q W (entryWord Q W k U) = decide (k < Q) := by
  have hl : (entryWord Q W k U).length = (lastT Q W).length := by rw [entryWord_length Q W k U hk, lastT_length Q W hQ]
  unfold testW
  refine decide_eq_decide.mpr ?_
  have hlen : (ZipMap.map andOut keep (entryWord Q W k U) (lastT Q W) false).length = Q + W + 1 := by
    rw [ZipMap.map_length _ _ _ _ _ hl, entryWord_length Q W k U hk]
  constructor
  · intro h
    have hQ1 : Q - 1 < (ZipMap.map andOut keep (entryWord Q W k U) (lastT Q W) false).length := by omega
    have h1 : (ZipMap.map andOut keep (entryWord Q W k U) (lastT Q W) false)[Q - 1]? = (zeroT Q W)[Q - 1]? := by
      rw [h]
    rw [List.getElem?_eq_getElem hQ1, map_keep_getElem _ _ _ _ hl, entryWord_getElem Q W k U (Q - 1) hk,
      lastT_getElem Q W (Q - 1) hQ] at h1
    simp only [zeroT, List.getElem?_replicate] at h1
    rw [if_pos (by omega)] at h1
    by_contra hc
    have : Q - 1 < k := by omega
    simp [andOut, this] at h1
  · intro hkQ
    apply List.ext_getElem
    · rw [hlen]; simp [zeroT]
    · intro i h1 h2
      rw [map_keep_getElem _ _ _ _ hl, entryWord_getElem Q W k U i hk, lastT_getElem Q W i hQ]
      simp only [zeroT, List.getElem_replicate, andOut]
      by_cases hi : i = Q - 1
      · subst hi
        rw [if_pos (by omega)]
        simp; omega
      · simp [hi]

/-- **The size increment on an entry below size `Q`.** -/
theorem incrW_entry (Q W k U : ℕ) (hk : k < Q) : incrW Q W (entryWord Q W k U) = entryWord Q W (k + 1) U := by
  have hl : (entryWord Q W k U).length = (levelT Q W).length := by
    rw [entryWord_length Q W k U (by omega), levelT_length]
  apply List.ext_getElem
  · unfold incrW
    rw [ZipMap.map_length _ _ _ _ _ hl, entryWord_length Q W k U (by omega), entryWord_length Q W (k + 1) U hk]
  · intro i h1 h2
    unfold incrW
    rw [map_incr_getElem _ _ _ hl, levelT_getElem, entryWord_getElem Q W (k + 1) U i hk]
    by_cases hi : i < Q
    · rw [if_pos (decide_eq_true hi), if_pos hi]
      by_cases h0 : i = 0
      · rw [dif_pos h0]; simp [h0]
      · rw [dif_neg h0, entryWord_getElem Q W k U (i - 1) (by omega), if_pos (by omega)]
        simp; omega
    · rw [if_neg (by simpa using hi), if_neg hi, entryWord_getElem Q W k U i (by omega), if_neg hi]

/-- **The union of an entry with a monomial.** -/
theorem orW_entry (Q W k U g : ℕ) (hk : k ≤ Q) :
    orW (entryWord Q W k U) (entryWord Q W 0 g) = entryWord Q W k (U ||| g) := by
  have hl : (entryWord Q W k U).length = (entryWord Q W 0 g).length := by
    rw [entryWord_length Q W k U hk, entryWord_length Q W 0 g (by omega)]
  apply List.ext_getElem
  · unfold orW
    rw [ZipMap.map_length _ _ _ _ _ hl, entryWord_length Q W k U hk, entryWord_length Q W k (U ||| g) hk]
  · intro i h1 h2
    unfold orW
    rw [map_keep_getElem _ _ _ _ hl, entryWord_getElem Q W k U i hk, entryWord_getElem Q W 0 g i (by omega),
      entryWord_getElem Q W k (U ||| g) i hk]
    simp only [orOut]
    by_cases hi : i < Q
    · simp [hi]
    · by_cases hq : i = Q
      · simp [hq]
      · simp [hi, hq, Nat.testBit_or]

/-- An entry as a word. -/
def ew (Q W : ℕ) (e : ℕ × ℕ) : List Bool := entryWord Q W e.1 e.2

/-- **One lift step on words is `liftStep` read through the entry words** (sizes at most `Q`, `Q ≥ 1`). -/
theorem liftStepW_map (Q W : ℕ) (hQ : 1 ≤ Q) (E : List (ℕ × ℕ)) (g : ℕ) (hE : ∀ e ∈ E, e.1 ≤ Q) :
    (CompilerMachine.liftStep Q E g).map (ew Q W) = liftStepW Q W (E.map (ew Q W)) (ew Q W (0, g)) := by
  unfold CompilerMachine.liftStep liftStepW
  rw [if_pos (by omega), List.map_append, List.map_append]
  have hf : E.filter (fun e => decide (e.1 < Q)) = E.filter (testW Q W ∘ ew Q W) := by
    apply List.filter_congr
    intro e he
    simp only [Function.comp, ew, testW_entry Q W e.1 e.2 hQ (hE e he)]
  have hm : ((E.filter (fun e => decide (e.1 < Q))).map fun e => (e.1 + 1, e.2 ||| g)).map (ew Q W) =
      ((E.map (ew Q W)).filter (testW Q W)).map (fun r => orW (incrW Q W r) (ew Q W (0, g))) := by
    rw [List.filter_map, List.map_map, List.map_map, ← hf]
    apply List.map_congr_left
    intro e he
    have hlt : e.1 < Q := by simpa using (List.mem_filter.mp he).2
    simp only [Function.comp, ew]
    rw [incrW_entry Q W e.1 e.2 hlt, orW_entry Q W (e.1 + 1) e.2 g (by omega)]
  have hl : ([(1, g)] : List (ℕ × ℕ)).map (ew Q W) = [incrW Q W (ew Q W (0, g))] := by
    simp only [List.map_cons, List.map_nil, ew]
    rw [incrW_entry Q W 0 g (by omega)]
  rw [hm, hl]

theorem liftStep_sizes (Q : ℕ) (hQ : 1 ≤ Q) (E : List (ℕ × ℕ)) (g : ℕ) (hE : ∀ e ∈ E, e.1 ≤ Q) :
    ∀ e ∈ CompilerMachine.liftStep Q E g, e.1 ≤ Q := by
  intro e he
  unfold CompilerMachine.liftStep at he
  rw [if_pos (by omega)] at he
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton, decide_eq_true_eq] at he
  rcases he with (h | ⟨e', ⟨_, h1⟩, rfl⟩) | rfl
  · exact hE e h
  · simp; omega
  · simp; omega

/-- **The streaming unions, as words**: the lift steps over the monomials' entries. -/
theorem unionsM_words (Q W : ℕ) (hQ : 1 ≤ Q) (G : List ℕ) :
    (CompilerMachine.unionsM Q G).map (ew Q W) = (G.map fun g => ew Q W (0, g)).foldl (liftStepW Q W) [] := by
  have key : ∀ (G : List ℕ) (E : List (ℕ × ℕ)), (∀ e ∈ E, e.1 ≤ Q) →
      (G.foldl (CompilerMachine.liftStep Q) E).map (ew Q W) =
        (G.map fun g => ew Q W (0, g)).foldl (liftStepW Q W) (E.map (ew Q W)) := by
    intro G
    induction G with
    | nil => intro E _; rfl
    | cons g G ih =>
      intro E hE
      rw [List.foldl_cons, ih _ (liftStep_sizes Q hQ E g hE), liftStepW_map Q W hQ E g hE]
      rfl
  exact key G [] (by simp)

/-! ## Twin -/

theorem liftStepW_twin :
    liftStepW 2 1 [ew 2 1 (1, 1)] (ew 2 1 (0, 1)) = [ew 2 1 (1, 1), ew 2 1 (2, 1), ew 2 1 (1, 1)] := by
  decide

end NearCubicWires.WireExponent3_5.CompilerMachine.Unions
