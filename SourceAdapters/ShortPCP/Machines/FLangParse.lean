import SourceAdapters.ShortPCP.Machines.FLangStep
import SourceAdapters.Joins.SingleRun

/-!
# Single-run time, machine layer 18: readers of the data word

The program input of the single-run verifier is `frame data ++ frame R` (proof of `thm:short-pcp-ours`), and
`data = Instance.word ++ frame x̄ ++ natWord dB ++ listWord frame masks` (`Joins/SingleRun.lean`): self-delimiting
fields (`natWord`, `listWord`, `frame`) describing the affine instance and verifier request. Step 2,
“Time and queries”, in the proof of `thm:short-pcp-ours` uses the generated instance; here its encoded
parameters are read from the data. The data bits are held in one
number `D` (variable `10`, bit `i` of `D` is bit `i` of the word, `At`), read at a cursor (variable `14`).

This module gives the cursor readers: `frame u` (`pFrameD`), a list of `natWord`s into a packed list of field words
(`pListW`), and the skipping of a self-delimiting list whose entries are skipped by a given routine (`skipLW`; one
gate `skipGate`, one circuit `skipCirc`, one list of numbers `skipList`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicGates.Close.Cells (natWord_one natWord_zero natWord_bit natWord_length lt_natBitLength)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (CodeGate listWord gateWord)
open NearCubicGates.Adapters.ACSP.Affine (Instance)

variable (G : Glob)

/-! ## Words inside a flattened list -/

theorem flatten_take_succ_length {α : Type} (g : α → List Bool) (L : List α) (j : ℕ) (hj : j < L.length) :
    ((L.take (j + 1)).map g).flatten.length = ((L.take j).map g).flatten.length + (g L[j]).length := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append, List.map_cons,
    List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]

theorem flatten_take_le {α : Type} (g : α → List Bool) (L : List α) (j : ℕ) :
    ((L.take j).map g).flatten.length ≤ (L.map g).flatten.length := by
  conv_rhs => rw [← List.take_append_drop j L]
  rw [List.map_append, List.flatten_append, List.length_append]; omega

/-- The entry `j` of a flattened list sits after the first `j` entries. -/
theorem At.flatten {α : Type} {D p : ℕ} (g : α → List Bool) (L : List α) (h : At D p (L.map g).flatten) (j : ℕ)
    (hj : j < L.length) : At D (p + ((L.take j).map g).flatten.length) (g L[j]) := by
  have e : (L.map g).flatten = ((L.take j).map g).flatten ++ (g L[j] ++ ((L.drop (j + 1)).map g).flatten) := by
    conv_lhs => rw [← List.take_append_drop j L]
    rw [List.drop_eq_getElem_cons hj, List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]
  rw [e] at h
  exact (At.append (At.append h).2).1

theorem length_le_flatten {α : Type} (g : α → List Bool) (L : List α) (hne : ∀ x ∈ L, 1 ≤ (g x).length) :
    L.length ≤ (L.map g).flatten.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append]
    have := hne a (by simp); have := ih (fun x hx => hne x (by simp [hx])); omega

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := natWord_length v

theorem natWord_pos (v : ℕ) : 1 ≤ (natWord v).length := by rw [natWord_len]; omega

theorem listWord_eq {α : Type} (g : α → List Bool) (L : List α) :
    listWord g L = natWord L.length ++ (L.map g).flatten := rfl

theorem listWord_pos {α : Type} (g : α → List Bool) (L : List α) : 1 ≤ (listWord g L).length := by
  rw [listWord_eq, List.length_append]; have := natWord_pos L.length; omega

theorem frame_pos (u : List Bool) : 1 ≤ (frame u).length := by rw [frame_len]; omega

/-! ## Bounds -/

/-- The run constants admit words ending before position `Bd` (`pNat_spec`'s clamps and passes). -/
def BdOk (Bd : ℕ) : Prop := Bd + 2 * 2 ^ Bd ≤ G.cap ∧ Bd + 1 ≤ G.N

theorem BdOk.mono {Bd Bd' : ℕ} (h : BdOk G Bd') (hle : Bd ≤ Bd') : BdOk G Bd :=
  ⟨le_trans (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hle; omega) h.1, by have := h.2; omega⟩

theorem natBitLength_le_len (v : ℕ) : natBitLength v + 1 ≤ (natWord v).length := by rw [natWord_len]; omega

/-- `pNat` for a word ending before `Bd`. -/
theorem pNat_at (s : FS) (v p Bd : ℕ) (hat : At (s.env 10) p (natWord v)) (hp : s.env 14 = p)
    (hend : p + (natWord v).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G pNat s).env 5 = v ∧ (evalS G pNat s).env 14 = p + (natWord v).length ∧ Wr pNatW s (evalS G pNat s) := by
  have h1 := natBitLength_le_len v
  have h2 : 2 ^ natBitLength v ≤ 2 ^ Bd := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact pNat_spec G s v p hat hp (by have := hB.1; omega) (by have := hB.2; omega)

/-! ## Affine neighbor pairs -/

theorem pairWord_pos (v : ℕ × ℕ) : 1 ≤ (Instance.pairWord v).length := by
  simp only [Instance.pairWord, List.length_append]
  have := natWord_pos v.1; omega

/-- Skip two self-delimiting coefficient words. -/
def skipPair : S := .seq pNat pNat

theorem skipPair_spec (s : FS) (v : ℕ × ℕ) (p Bd : ℕ)
    (hat : At (s.env 10) p (Instance.pairWord v)) (hp : s.env 14 = p)
    (hend : p + (Instance.pairWord v).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G skipPair s).env 14 = p + (Instance.pairWord v).length ∧
      Wr pNatW s (evalS G skipPair s) := by
  obtain ⟨ha, hb⟩ := At.append hat
  simp only [Instance.pairWord, List.length_append] at hend ⊢
  obtain ⟨-, a14, aW⟩ := pNat_at G s v.1 p Bd ha hp (by omega) hB
  generalize hs : evalS G pNat s = t at a14 aW
  obtain ⟨-, b14, bW⟩ := pNat_at G t v.2 _ Bd (by rw [aW.env 10 (by decide)]; exact hb)
    a14 (by omega) hB
  simp only [skipPair, evalS_seq, hs]
  exact ⟨by rw [b14]; omega, aW.trans bW⟩

/-- Read the slope into `26` and the shift into `27`. -/
def readPair : S := .seq pNat (.seq (.set 26 (.v 5)) (.seq pNat (.set 27 (.v 5))))

def readPairW : List Var := [5, 6, 8, 9, 14, 26, 27]

theorem readPair_spec (s : FS) (v : ℕ × ℕ) (p Bd : ℕ)
    (hat : At (s.env 10) p (Instance.pairWord v)) (hp : s.env 14 = p)
    (hend : p + (Instance.pairWord v).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G readPair s).env 26 = v.1 ∧ (evalS G readPair s).env 27 = v.2 ∧
      (evalS G readPair s).env 14 = p + (Instance.pairWord v).length ∧
      Wr readPairW s (evalS G readPair s) := by
  obtain ⟨ha, hb⟩ := At.append hat
  simp only [Instance.pairWord, List.length_append] at hend ⊢
  obtain ⟨a5, a14, aW⟩ := pNat_at G s v.1 p Bd ha hp (by omega) hB
  generalize hs1 : evalS G pNat s = s1 at a5 a14 aW
  set s2 := s1.setv 26 (s1.env 5) with hs2
  obtain ⟨b5, b14, bW⟩ := pNat_at G s2 v.2 _ Bd
    (by simp [s2]; rw [aW.env 10 (by decide)]; exact hb) (by simp [s2, a14]) (by omega) hB
  generalize hs3 : evalS G pNat s2 = s3 at b5 b14 bW
  have e : evalS G readPair s = s3.setv 27 (s3.env 5) := by
    simp only [readPair, evalS_seq, evalS_set, evalE, hs1]
    rw [show s1.setv 26 (s1.env 5) = s2 from rfl, hs3]
  rw [e]
  refine ⟨?_, by simp [b5], by simp [b14]; omega, ?_⟩
  · simp only [FS.setv_env, Function.update_of_ne (show (26 : Var) ≠ 27 by decide)]
    rw [bW.env 26 (by decide)]; simp [s2, a5]
  · exact (((aW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans
      (bW.mono (by decide))).trans (Wr.setv _ (by decide) _)

/-! ## A loop over the entries of a flattened list -/

/-- **A counted loop through `k` entries**: each pass runs `inner`, which moves the cursor past one entry. -/
theorem curLoop_spec {α : Type} (i : Var) (n : E) (inner : S) (iW : List Var) (g : α → List Bool) (L : List α)
    (s : FS) (p Bd k : ℕ) (hn : min (evalE G s n) G.N = k) (hk : k ≤ L.length)
    (hat : At (s.env 10) p (L.map g).flatten) (hp : s.env 14 = p) (hend : p + (L.map g).flatten.length ≤ Bd)
    (h10 : (10 : Var) ∉ iW) (hi10 : i ≠ 10) (hi14 : i ≠ 14)
    (hin : ∀ x ∈ L, ∀ (t : FS) (p' : ℕ), At (t.env 10) p' (g x) → t.env 14 = p' → p' + (g x).length ≤ Bd →
      (evalS G inner t).env 14 = p' + (g x).length ∧ Wr iW t (evalS G inner t)) :
    (evalS G (.loop i n inner) s).env 14 = p + ((L.take k).map g).flatten.length ∧
      Wr (i :: iW) s (evalS G (.loop i n inner) s) := by
  have hl := loop_inv G (i := i) (n := n) (body := inner) (s := s)
    (fun j t => t.env 14 = p + ((L.take j).map g).flatten.length ∧ Wr (i :: iW) s t)
    ⟨by simp [hp], Wr.refl _ _⟩ (by
      rw [hn]
      rintro j hj t ⟨t14, tW⟩
      have hjL : j < L.length := by omega
      have h10' : (t.setv i j).env 10 = s.env 10 := by
        simp only [FS.setv_env, Function.update_of_ne (Ne.symm hi10)]
        exact tW.env 10 (by simp [Ne.symm hi10, h10])
      have h14' : (t.setv i j).env 14 = p + ((L.take j).map g).flatten.length := by
        simp only [FS.setv_env, Function.update_of_ne (Ne.symm hi14)]; exact t14
      have hA := At.flatten g L hat j hjL
      have hlen := flatten_take_succ_length g L j hjL
      have hle := flatten_take_le g L (j + 1)
      obtain ⟨e14, eW⟩ := hin L[j] (List.getElem_mem hjL) (t.setv i j) _ (by rw [h10']; exact hA) h14' (by omega)
      refine ⟨by rw [e14, hlen]; ring, ?_⟩
      exact (tW.trans (Wr.setv _ (by simp) _)).trans (eW.mono (fun x hx => by simp [hx])))
  rw [hn] at hl
  exact hl

/-! ## Skipping a self-delimiting list -/

/-- Skip `listWord g L` at the cursor: read the count into `c`, then `c` passes of `inner` (loop variable `i`). -/
def skipLW (i c : Var) (inner : S) : S := .seq pNat (.seq (.set c (.v 5)) (.loop i (.v c) inner))

/-- **Skipping a list.** -/
theorem skipLW_spec {α : Type} (i c : Var) (inner : S) (iW : List Var) (g : α → List Bool) (L : List α) (s : FS)
    (p Bd : ℕ) (hat : At (s.env 10) p (listWord g L)) (hp : s.env 14 = p)
    (hend : p + (listWord g L).length ≤ Bd) (hB : BdOk G Bd) (hne : ∀ x ∈ L, 1 ≤ (g x).length)
    (hi10 : i ≠ 10) (hi14 : i ≠ 14) (hic : i ≠ c) (hc10 : c ≠ 10) (hc14 : c ≠ 14) (hcW : c ∉ iW)
    (h10 : (10 : Var) ∉ iW)
    (hin : ∀ x ∈ L, ∀ (t : FS) (p' : ℕ), At (t.env 10) p' (g x) → t.env 14 = p' → p' + (g x).length ≤ Bd →
      (evalS G inner t).env 14 = p' + (g x).length ∧ Wr iW t (evalS G inner t)) :
    (evalS G (skipLW i c inner) s).env 14 = p + (listWord g L).length ∧
      Wr (c :: i :: (pNatW ++ iW)) s (evalS G (skipLW i c inner) s) := by
  rw [listWord_eq] at hat hend ⊢
  obtain ⟨a1, a2⟩ := At.append hat
  simp only [List.length_append] at hend
  obtain ⟨n5, n14, nW⟩ := pNat_at G s L.length p Bd a1 hp (by omega) hB
  generalize hs1 : evalS G pNat s = s1 at n5 n14 nW
  have hlen := length_le_flatten g L hne
  have s2_10 : (s1.setv c (s1.env 5)).env 10 = s.env 10 := by
    simp only [FS.setv_env, Function.update_of_ne (Ne.symm hc10)]; exact nW.env 10 (by decide)
  have hlp := curLoop_spec G i (.v c) inner iW g L (s1.setv c (s1.env 5)) (p + (natWord L.length).length) Bd L.length
    (by simp only [evalE, FS.setv_env, Function.update_self, n5]; have := hB.2; omega) le_rfl
    (by rw [s2_10]; exact a2) (by simp only [FS.setv_env, Function.update_of_ne (Ne.symm hc14)]; exact n14)
    (by omega) h10 hi10 hi14 hin
  rw [List.take_length] at hlp
  have e : evalS G (skipLW i c inner) s = evalS G (.loop i (.v c) inner) (s1.setv c (s1.env 5)) := by
    simp only [skipLW, evalS_seq, evalS_set, hs1, evalE]
  rw [e, List.length_append]
  refine ⟨by rw [hlp.1]; ring, ?_⟩
  refine ((nW.mono (fun x hx => by simp [hx])).trans (Wr.setv _ (by simp) _)).trans (hlp.2.mono ?_)
  intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto

/-! ## Gates, circuits, lists of numbers -/

/-- The three numbers of a gate word (`gateWord`: tag, then two numbers). -/
def gTag : CodeGate → ℕ
  | .input _ => 0
  | .const _ => 1
  | .add _ _ => 2
  | .mul _ _ => 3

def gX : CodeGate → ℕ
  | .input i => i
  | .const v => v
  | .add a _ => a
  | .mul a _ => a

def gY : CodeGate → ℕ
  | .input _ => 0
  | .const _ => 0
  | .add _ b => b
  | .mul _ b => b

theorem gateWord_eq (g : CodeGate) : gateWord g = natWord (gTag g) ++ natWord (gX g) ++ natWord (gY g) := by
  cases g <;> rfl

theorem gateWord_pos (g : CodeGate) : 1 ≤ (gateWord g).length := by
  rw [gateWord_eq, List.length_append, List.length_append]; have := natWord_pos (gTag g); omega

/-- Skip one gate (three `natWord`s). -/
def skipGate : S := .seq pNat (.seq pNat pNat)

theorem skipGate_spec (s : FS) (g : CodeGate) (p Bd : ℕ) (hat : At (s.env 10) p (gateWord g))
    (hp : s.env 14 = p) (hend : p + (gateWord g).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G skipGate s).env 14 = p + (gateWord g).length ∧ Wr pNatW s (evalS G skipGate s) := by
  rw [gateWord_eq] at hat hend ⊢
  obtain ⟨a12, a3⟩ := At.append hat
  obtain ⟨a1, a2⟩ := At.append a12
  simp only [List.length_append] at hend a3 ⊢
  obtain ⟨-, n14, nW⟩ := pNat_at G s _ p Bd a1 hp (by omega) hB
  generalize hs1 : evalS G pNat s = s1 at n14 nW
  obtain ⟨-, m14, mW⟩ := pNat_at G s1 _ _ Bd (by rw [nW.env 10 (by decide)]; exact a2) n14 (by omega) hB
  generalize hs2 : evalS G pNat s1 = s2 at m14 mW
  rw [← add_assoc] at a3
  obtain ⟨-, k14, kW⟩ := pNat_at G s2 (gY g) _ Bd (by rw [mW.env 10 (by decide), nW.env 10 (by decide)]; exact a3)
    m14 (by omega) hB
  have e : evalS G skipGate s = evalS G pNat s2 := by simp only [skipGate, evalS_seq, hs1, hs2]
  rw [e]
  exact ⟨by rw [k14]; ring, (nW.trans mW).trans kW⟩

/-- The variables of the skipping routines. -/
def skipW1 : List Var := [5, 6, 8, 9, 14, 31, 34]
def skipW2 : List Var := [5, 6, 8, 9, 14, 31, 32, 33, 34]

/-- Skip `listWord natWord l`. -/
def skipList : S := skipLW 31 34 pNat

/-- Skip one circuit `listWord gateWord gates`. -/
def skipCirc : S := skipLW 31 34 skipGate

/-- Skip `listWord (listWord gateWord) cs`. -/
def skipCircs : S := skipLW 32 33 skipCirc

/-- Skip `listWord (listWord natWord) ls`. -/
def skipLists : S := skipLW 32 33 skipList

theorem skipList_spec (s : FS) (l : List ℕ) (p Bd : ℕ) (hat : At (s.env 10) p (listWord natWord l))
    (hp : s.env 14 = p) (hend : p + (listWord natWord l).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G skipList s).env 14 = p + (listWord natWord l).length ∧ Wr skipW1 s (evalS G skipList s) := by
  have h := skipLW_spec G 31 34 pNat pNatW natWord l s p Bd hat hp hend hB (fun x _ => natWord_pos x)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x _ t p' ha ht he => let r := pNat_at G t x p' Bd ha ht he hB; ⟨r.2.1, r.2.2⟩)
  exact ⟨h.1, h.2.mono (by decide)⟩

theorem skipCirc_spec (s : FS) (gs : List CodeGate) (p Bd : ℕ)
    (hat : At (s.env 10) p (listWord gateWord gs)) (hp : s.env 14 = p)
    (hend : p + (listWord gateWord gs).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G skipCirc s).env 14 = p + (listWord gateWord gs).length ∧
      Wr skipW1 s (evalS G skipCirc s) := by
  have h := skipLW_spec G 31 34 skipGate pNatW gateWord gs s p Bd hat hp hend hB
    (fun x _ => gateWord_pos x) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x _ t p' ha ht he => skipGate_spec G t x p' Bd ha ht he hB)
  exact ⟨h.1, h.2.mono (by decide)⟩

theorem skipCircs_spec (s : FS) (cs : List (List CodeGate)) (p Bd : ℕ)
    (hat : At (s.env 10) p (listWord (listWord gateWord) cs)) (hp : s.env 14 = p)
    (hend : p + (listWord (listWord gateWord) cs).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G skipCircs s).env 14 = p + (listWord (listWord gateWord) cs).length ∧
      Wr skipW2 s (evalS G skipCircs s) := by
  have h := skipLW_spec G 32 33 skipCirc skipW1 (listWord gateWord) cs s p Bd hat hp hend hB
    (fun x _ => listWord_pos _ x) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun x _ t p' ha ht he => skipCirc_spec G t x p' Bd ha ht he hB)
  exact ⟨h.1, h.2.mono (by decide)⟩

theorem skipLists_spec (s : FS) (ls : List (List ℕ)) (p Bd : ℕ)
    (hat : At (s.env 10) p (listWord (listWord natWord) ls)) (hp : s.env 14 = p)
    (hend : p + (listWord (listWord natWord) ls).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G skipLists s).env 14 = p + (listWord (listWord natWord) ls).length ∧
      Wr skipW2 s (evalS G skipLists s) := by
  have h := skipLW_spec G 32 33 skipList skipW1 (listWord natWord) ls s p Bd hat hp hend hB
    (fun x _ => listWord_pos _ x) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun x _ t p' ha ht he => skipList_spec G t x p' Bd ha ht he hB)
  exact ⟨h.1, h.2.mono (by decide)⟩

/-! ## A framed word in `D` -/

/-- The body of the frame reader: step to the value bit, add it at place `28`, double `28`, count, step on. -/
def pFrameBody : S :=
  .seq (.set 14 (.add (.v 14) (.k 1))) (.seq (.set 26 (.add (.v 26) (.mul bitE (.v 28))))
    (.seq (.set 28 (.add (.v 28) (.v 28))) (.seq (.set 27 (.add (.v 27) (.k 1))) (.set 14 (.add (.v 14) (.k 1))))))

/-- Read `frame u` at the cursor: `26 := bitsValue u`, `27 := |u|` (place value in `28`). -/
def pFrameD : S :=
  .seq (.set 26 (.k 0)) (.seq (.set 27 (.k 0)) (.seq (.set 28 (.k 1)) (.seq (.whl bitE pFrameBody)
    (.set 14 (.add (.v 14) (.k 1))))))

def pFrameW : List Var := [14, 26, 27, 28]

/-- **The reader of a framed word in `D`.** -/
theorem pFrameD_spec (s : FS) (u : List Bool) (p Bd : ℕ) (hat : At (s.env 10) p (frame u)) (hp : s.env 14 = p)
    (hend : p + (frame u).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G pFrameD s).env 26 = bitsValue u ∧ (evalS G pFrameD s).env 27 = u.length ∧
      (evalS G pFrameD s).env 14 = p + (frame u).length ∧ Wr pFrameW s (evalS G pFrameD s) := by
  rw [frame_len] at hend ⊢
  have hcap := hB.1; have hN := hB.2
  have := Nat.one_le_two_pow (n := Bd)
  have hc0 : min 0 G.cap = 0 := by omega
  have hc1 : min 1 G.cap = 1 := by omega
  have hc2 : min 2 G.cap = 2 := by omega
  have hpu : 2 ^ u.length ≤ 2 ^ Bd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbit : ∀ (w : FS) (j : ℕ), w.env 10 = s.env 10 → w.env 14 = p + j → j < 2 * u.length + 1 →
      evalE G w bitE = ((frame u).getD j false).toNat := by
    intro w j h10 h14 hj
    simp only [bitE, evalE, h10, h14, hc2]
    exact hat j (by rw [frame_len]; exact hj)
  let P : FS → Prop := fun w => ∃ k ≤ u.length, w.env 26 = bitsValue (u.take k) ∧ w.env 27 = k ∧ w.env 28 = 2 ^ k ∧
    w.env 14 = p + 2 * k ∧ Wr pFrameW s w
  have hP0 : P (((s.setv 26 (min 0 G.cap)).setv 27 (min 0 G.cap)).setv 28 (min 1 G.cap)) := by
    refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
    · simp (config := { decide := true }) [Function.update_apply, hc0, bitsValue]
    · simp (config := { decide := true }) [Function.update_apply, hc0]
    · simp (config := { decide := true }) [Function.update_apply, hc1]
    · simp (config := { decide := true }) [Function.update_apply, hp]
    · exact ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
  have hw := whl_inv G (c := bitE) (body := pFrameBody) P (fun w => u.length - w.env 27) _ hP0
    (by simp (config := { decide := true }) [Function.update_apply, hc0]; omega) (by
      rintro w ⟨k, hk, w26, w27, w28, w14, wW⟩ hc
      have h10 : w.env 10 = s.env 10 := wW.env 10 (by decide)
      have hk' : k < u.length := by
        have := hbit w (2 * k) h10 w14 (by omega)
        rw [frame_getD_even] at this
        by_contra h; simp [h] at this; exact hc this
      have hb : s.env 10 / 2 ^ (p + 2 * k + 1) % 2 = (u.getD k false).toNat := by
        have := hat (2 * k + 1) (by rw [frame_len]; omega)
        rwa [frame_getD_odd u k hk', ← add_assoc] at this
      have hxlt : bitsValue (u.take k) < 2 ^ k := by
        have := bv_lt (u.take k); simp only [List.length_take] at this; rwa [min_eq_left hk] at this
      have hpow : 2 ^ (k + 1) ≤ 2 ^ u.length := Nat.pow_le_pow_right (by norm_num) hk'
      have hb01 := bool_toNat_le (u.getD k false)
      have hmul : (u.getD k false).toNat * 2 ^ k ≤ 2 ^ k := by
        have := Nat.mul_le_mul_right (2 ^ k) hb01; simpa using this
      rw [pow_succ] at hpow
      have e1 : min (p + 2 * k + min 1 G.cap) G.cap = p + 2 * k + 1 := by rw [hc1]; omega
      have e2 : min ((u.getD k false).toNat * 2 ^ k) G.cap = (u.getD k false).toNat * 2 ^ k := by omega
      have e3 : min (bitsValue (u.take k) + (u.getD k false).toNat * 2 ^ k) G.cap =
          bitsValue (u.take k) + (u.getD k false).toNat * 2 ^ k := by omega
      have e4 : min (2 ^ k + 2 ^ k) G.cap = 2 ^ (k + 1) := by rw [pow_succ]; omega
      have e5 : min (k + min 1 G.cap) G.cap = k + 1 := by rw [hc1]; omega
      have e6 : min (p + 2 * k + 1 + min 1 G.cap) G.cap = p + 2 * (k + 1) := by rw [hc1]; omega
      simp only [pFrameBody, evalS_seq, evalS_set]
      have hbE : ∀ v : ℕ, evalE G (w.setv 14 v) bitE = s.env 10 / 2 ^ v % 2 := by
        intro v; simp (config := { decide := true }) only [bitE, evalE, FS.setv_env, Function.update_apply, if_true,
          if_false, h10, hc2]
      refine ⟨⟨k + 1, hk', ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_true, if_false, w14,
          w26, w28, e1, hbE, hb, e2, e3]
        rw [bitsValue_take_succ u k hk']
      · simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_true, if_false, w27, e5]
      · simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_true, if_false, w28, e4]
      · simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_true, if_false, w14, e1,
          e6]
      · refine wW.trans ?_
        exact ((((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
          (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
      · simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_true, if_false, w27, e5]
        omega)
  obtain ⟨⟨k, hk, w26, w27, w28, w14, wW⟩, hc⟩ := hw
  generalize hs3 : evalS G (.whl bitE pFrameBody)
    (((s.setv 26 (min 0 G.cap)).setv 27 (min 0 G.cap)).setv 28 (min 1 G.cap)) = s3 at w26 w27 w28 w14 wW hc
  have hku : k = u.length := by
    by_contra h
    have h1 := hbit s3 (2 * k) (wW.env 10 (by decide)) w14 (by omega)
    have h2 : ((frame u).getD (2 * k) false).toNat = 1 := by
      rw [frame_getD_even]; simp only [show k < u.length by omega, decide_true, Bool.toNat_true]
    omega
  subst hku
  have e : evalS G pFrameD s = s3.setv 14 (min (s3.env 14 + min 1 G.cap) G.cap) := by
    simp only [pFrameD, evalS_seq, evalS_set, hs3, evalE]
  rw [e]
  refine ⟨by simp (config := { decide := true }) [Function.update_apply, w26, List.take_length],
    by simp (config := { decide := true }) [Function.update_apply, w27], ?_,
    wW.trans (Wr.setv _ (by decide) _)⟩
  simp only [FS.setv_env, Function.update_self, w14, hc1]; omega

/-! ## A list of numbers into a packed list of words -/

/-- Read `listWord natWord l` at the cursor: `29 := |l|`, `30 := packW f l` (width in `23`; loop variable `31`). -/
def pListW : S :=
  .seq pNat (.seq (.set 29 (.v 5)) (.seq (.set 30 (.k 0))
    (.loop 31 (.v 29) (.seq pNat (.set 30 (.add (.v 30) (.shl (.v 5) (.mul (.v 31) (.v 23)))))))))

def pListWW : List Var := [5, 6, 8, 9, 14, 29, 30, 31]

theorem packW_take_succ (w : ℕ) (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    packW w (l.take (j + 1)) = packW w (l.take j) + l[j] * 2 ^ (j * w) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, packW_append, List.length_take,
    min_eq_left hj.le]
  simp [packW, mul_comm]

/-- **The reader of a list of words.** -/
theorem pListW_spec (s : FS) (l : List ℕ) (w p Bd : ℕ) (hat : At (s.env 10) p (listWord natWord l))
    (hp : s.env 14 = p) (h23 : s.env 23 = w) (hl : ∀ a ∈ l, a < 2 ^ w) (hwK : w * l.length ≤ G.K)
    (hend : p + (listWord natWord l).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G pListW s).env 29 = l.length ∧ (evalS G pListW s).env 30 = packW w l ∧
      (evalS G pListW s).env 14 = p + (listWord natWord l).length ∧ Wr pListWW s (evalS G pListW s) := by
  rw [listWord_eq] at hat hend ⊢
  obtain ⟨a1, a2⟩ := At.append hat
  simp only [List.length_append] at hend ⊢
  have hcap := hB.1; have hN := hB.2
  have hc0 : min 0 G.cap = 0 := by omega
  have hlen := length_le_flatten natWord l (fun x _ => natWord_pos x)
  obtain ⟨n5, n14, nW⟩ := pNat_at G s l.length p Bd a1 hp (by omega) hB
  generalize hs1 : evalS G pNat s = s1 at n5 n14 nW
  set p1 := p + (natWord l.length).length with hp1
  set s2 := (s1.setv 29 (s1.env 5)).setv 30 (min 0 G.cap) with hs2
  have s2_10 : s2.env 10 = s.env 10 := by
    simp (config := { decide := true }) only [s2, FS.setv_env, Function.update_apply, if_false]
    exact nW.env 10 (by decide)
  have hmin : min (evalE G s2 (.v 29)) G.N = l.length := by
    simp (config := { decide := true }) only [s2, evalE, FS.setv_env, Function.update_apply, if_true, if_false, n5]
    omega
  have hpk : 2 ^ (w * l.length) ≤ G.cap + 1 := pow_le_cap hwK
  have hl := loop_inv G (i := 31) (n := .v 29) (s := s2)
    (body := .seq pNat (.set 30 (.add (.v 30) (.shl (.v 5) (.mul (.v 31) (.v 23))))))
    (fun j t => t.env 14 = p1 + ((l.take j).map natWord).flatten.length ∧ t.env 30 = packW w (l.take j) ∧
      t.env 29 = l.length ∧ Wr pListWW s t) ⟨by
        simp (config := { decide := true }) only [s2, FS.setv_env, Function.update_apply, if_false, n14]; simp,
      by simp [s2, hc0, packW], by simp (config := { decide := true }) [s2, Function.update_apply, n5],
      (nW.mono (by decide)).trans ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))⟩ (by
      rw [hmin]
      rintro j hj t ⟨t14, t30, t29, tW⟩
      have t10 : (t.setv 31 j).env 10 = s.env 10 := by simp; exact tW.env 10 (by decide)
      have hA := At.flatten natWord l a2 j hj
      have hle := flatten_take_le natWord l (j + 1)
      have hts := flatten_take_succ_length natWord l j hj
      obtain ⟨m5, m14, mW⟩ := pNat_at G (t.setv 31 j) l[j] _ Bd (by rw [t10]; exact hA)
        (by simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 31 by decide)]; exact t14) (by omega) hB
      generalize hs3 : evalS G pNat (t.setv 31 j) = s3 at m5 m14 mW
      have s3_30 : s3.env 30 = packW w (l.take j) := by rw [mW.env 30 (by decide)]; simpa using t30
      have s3_31 : s3.env 31 = j := by rw [mW.env 31 (by decide)]; simp
      have s3_23 : s3.env 23 = w := by
        rw [mW.env 23 (by decide)]; simp only [FS.setv_env, Function.update_of_ne (show (23 : Var) ≠ 31 by decide)]
        rw [tW.env 23 (by decide)]; exact h23
      have hlj : l[j] < 2 ^ w := hl _ (List.getElem_mem hj)
      have hpj := packW_lt w (l.take (j + 1)) (fun a ha => hl a (List.mem_of_mem_take ha))
      rw [List.length_take, min_eq_left hj, packW_take_succ w l j hj] at hpj
      have hjw : j * w ≤ G.K := le_trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ hj.le) hwK
      have hpw : 2 ^ (w * (j + 1)) ≤ 2 ^ (w * l.length) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hj)
      have e1 : min (j * w) G.cap = j * w := min_cap hjw
      have e2 : min (l[j] * 2 ^ (j * w)) G.cap = l[j] * 2 ^ (j * w) := by omega
      have e3 : min (packW w (l.take j) + l[j] * 2 ^ (j * w)) G.cap = packW w (l.take j) + l[j] * 2 ^ (j * w) := by
        omega
      simp only [evalS_seq, evalS_set, hs3]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 30 by decide), m14, hts]; ring
      · simp only [FS.setv_env, Function.update_self, evalE, s3_30, s3_31, s3_23, m5, e1, e2, e3]
        rw [packW_take_succ w l j hj]
      · simp only [FS.setv_env, Function.update_of_ne (show (29 : Var) ≠ 30 by decide)]
        rw [mW.env 29 (by decide)]; simpa using t29
      · exact ((tW.trans (Wr.setv _ (by decide) _)).trans (mW.mono (by decide))).trans (Wr.setv _ (by decide) _))
  rw [hmin] at hl; simp only [List.take_length] at hl
  obtain ⟨f14, f30, f29, fW⟩ := hl
  have e : evalS G pListW s = evalS G (.loop 31 (.v 29) (.seq pNat (.set 30 (.add (.v 30) (.shl (.v 5)
      (.mul (.v 31) (.v 23))))))) s2 := by
    simp only [pListW, evalS_seq, evalS_set, hs1, evalE, s2]
  rw [e]
  exact ⟨f29, f30, by rw [f14]; ring, fW⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
