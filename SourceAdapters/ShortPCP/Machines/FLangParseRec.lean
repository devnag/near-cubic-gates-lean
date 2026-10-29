import SourceAdapters.ShortPCP.Machines.FLangParse

/-!
# Single-run time, machine layer 19: the layout of the data word and the parse record

`data = Instance.word ++ frame x̄ ++ natWord dB ++ listWord frame masks` (`Joins/SingleRun.lean`, proof of `thm:short-pcp-ours`)
is the concatenation of eleven self-delimiting fields (`pieces`); field `k` starts at bit `posOf q k` of `D`.

The parse (`FLangParseMain.lean`) leaves its results in ONE variable (`15`, the record): sixteen slots of width
`K/16` (`recE i` reads slot `i`, `addRec i e` appends it). The slots (`parseRec q`) are the quantities the verifier
uses in Steps 2–3 of the proof of `thm:short-pcp-ours`: the instance data, its low-degree extension,
and the amplification masks.

| slot | value | slot | value |
|---|---|---|---|
| 0 | `f` | 8 | `|x̄|` |
| 1 | `mH = |hBasis|` | 9 | `bitsValue x̄` |
| 2 | `d_A = 2^mH − 1` | 10 | `m = log |x̄|` (`mI`) |
| 3 | `packW f hBasis` | 11 | `dB` |
| 4 | `hOffset` | 12 | number of masks |
| 5 | `cN` | 13 | position of the first mask frame |
| 6 | position of the first neighbor pair | 14 | `packW f iBasis` |
| 7 | position of the constraint circuit | 15 | `iOffset` |
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicGates.Close.Cells (natWord_one natWord_zero natWord_bit natWord_length lt_natBitLength)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (CodeGate listWord gateWord)
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)

variable (G : Glob)

/-! ## The layout -/

/-- The eleven fields of the data word, in order. -/
def pieces (q : Request) : List (List Bool) :=
  [natWord q.code.f, natWord q.code.irr, listWord natWord q.code.hBasis,
    natWord q.code.hOffset, listWord Instance.pairWord q.code.nbr,
    listWord gateWord q.code.cons, listWord natWord q.code.iBasis,
    natWord q.code.iOffset, frame q.xbar, natWord q.dB, listWord frame q.masks]

theorem data_eq (q : Request) : q.data = (pieces q).flatten := by
  simp only [Request.data, Instance.word, pieces, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]

/-- The position of field `k`. -/
def posOf (q : Request) (k : ℕ) : ℕ := ((pieces q).take k).flatten.length

theorem pieces_length (q : Request) : (pieces q).length = 11 := rfl

theorem posOf_eleven (q : Request) : posOf q 11 = q.data.length := by
  rw [posOf, data_eq, ← pieces_length q, List.take_length]

theorem posOf_le (q : Request) (k : ℕ) : posOf q k ≤ q.data.length := by
  rw [posOf, data_eq]
  have := flatten_take_le id (pieces q) k
  simpa using this

/-- **Field `k` of the data word sits at `posOf q k`.** -/
theorem piece_at (q : Request) {D : ℕ} (h : At D 0 q.data) (k : ℕ) (w : List Bool) (hk : k < 11)
    (hw : (pieces q).getD k [] = w) :
    At D (posOf q k) w ∧ posOf q (k + 1) = posOf q k + w.length := by
  rw [data_eq] at h
  have hk' : k < (pieces q).length := by rw [pieces_length]; exact hk
  have hg : (pieces q)[k] = w := by rw [← hw, List.getD_eq_getElem _ _ hk']
  have h1 := At.flatten id (pieces q) (by simpa using h) k hk'
  have h2 := flatten_take_succ_length id (pieces q) k hk'
  simp only [List.map_id, id, Nat.zero_add, hg] at h1 h2
  exact ⟨h1, h2⟩

/-! ## The record -/

/-- The slot width `K / 16`. -/
def rwE : E := .div .gk (.k 16)

/-- Slot `i` of the record in `15`. -/
def recE (i : ℕ) : E := .md (.shr (.v 15) (.mul (.k i) rwE)) (.shl (.k 1) rwE)

/-- Append slot `i` with the value of `e`. -/
def addRec (i : ℕ) (e : E) : S := .set 15 (.add (.v 15) (.shl e (.mul (.k i) rwE)))

theorem rwE_eval (s : FS) (hK : 32 ≤ G.K) : evalE G s rwE = G.K / 16 := by
  have := cap_ge G; simp only [rwE, evalE]; rw [min_eq_left (by omega)]

theorem slot_mul_le (i : ℕ) (hi : i ≤ 16) : i * (G.K / 16) ≤ G.K := by
  calc i * (G.K / 16) ≤ 16 * (G.K / 16) := Nat.mul_le_mul_right _ hi
    _ ≤ G.K := Nat.mul_div_le G.K 16

/-- **Reading a slot.** -/
theorem recE_eval (s : FS) (l : List ℕ) (h15 : s.env 15 = packW (G.K / 16) l) (hl : ∀ a ∈ l, a < 2 ^ (G.K / 16))
    (i : ℕ) (hi : i < 16) (hK : 32 ≤ G.K) : evalE G s (recE i) = l.getD i 0 := by
  have hc := cap_ge G
  have hw := rwE_eval G s hK
  have e1 : min i G.cap = i := by omega
  have e2 : min (i * (G.K / 16)) G.cap = i * (G.K / 16) := min_cap (slot_mul_le G i hi.le)
  have e3 : min (min 1 G.cap * 2 ^ (G.K / 16)) G.cap = 2 ^ (G.K / 16) := by
    rw [show min 1 G.cap = 1 by omega, one_mul]; exact min_cap_pow (by omega)
  simp only [recE, evalE, hw, h15, e1, e2, e3]
  exact packW_get _ l hl i

/-- **Appending a slot.** -/
theorem addRec_spec (s : FS) (l : List ℕ) (i : ℕ) (e : E) (v : ℕ) (h15 : s.env 15 = packW (G.K / 16) l)
    (hl : ∀ a ∈ l, a < 2 ^ (G.K / 16)) (hli : l.length = i) (hi : i < 16) (he : evalE G s e = v)
    (hv : v < 2 ^ (G.K / 16)) (hK : 32 ≤ G.K) : evalS G (addRec i e) s = s.setv 15 (packW (G.K / 16) (l ++ [v])) := by
  subst hli
  have hc := cap_ge G
  have hw := rwE_eval G s hK
  set W := G.K / 16 with hW
  have hlt : packW W (l ++ [v]) < 2 ^ (W * (l.length + 1)) := by
    have := packW_lt W (l ++ [v]) (by intro a ha; simp at ha; rcases ha with h | h; exacts [hl a h, h ▸ hv])
    simpa using this
  have hp : 2 ^ (W * (l.length + 1)) ≤ G.cap + 1 :=
    pow_le_cap (by rw [mul_comm]; exact slot_mul_le G _ (by omega))
  have happ : packW W (l ++ [v]) = packW W l + v * 2 ^ (l.length * W) := by
    rw [packW_append]; simp [packW, mul_comm]
  have e1 : min l.length G.cap = l.length := by omega
  have e2 : min (l.length * W) G.cap = l.length * W := min_cap (slot_mul_le G _ (by omega))
  have e3 : min (v * 2 ^ (l.length * W)) G.cap = v * 2 ^ (l.length * W) := by omega
  have e4 : min (packW W l + v * 2 ^ (l.length * W)) G.cap = packW W l + v * 2 ^ (l.length * W) := by omega
  simp only [addRec, evalS_set, evalE, hw, he, h15, e1, e2, e3, e4, happ]

/-! ## The parse record and its context -/

/-- The position of the first neighbor pair, of the constraint circuit, and of the first mask. -/
def posN (q : Request) : ℕ := posOf q 4 + (natWord q.code.cN).length
def posC (q : Request) : ℕ := posOf q 5
def posM (q : Request) : ℕ := posOf q 10 + (natWord q.masks.length).length

/-- The words of the actual input subspace (basis, offset). -/
def iBw (q : Request) : List ℕ := q.code.iBasis
def iOw (q : Request) : ℕ := q.code.iOffset

/-- **The parse record** (slot table in the module header). -/
def parseRec (q : Request) : List ℕ :=
  [q.code.f, q.code.hBasis.length, q.dA, packW q.code.f q.code.hBasis, q.code.hOffset, q.code.cN, posN q, posC q,
    q.xbar.length, bitsValue q.xbar, q.mI, q.dB, q.masks.length, posM q, packW q.code.f (iBw q), iOw q]

theorem parseRec_length (q : Request) : (parseRec q).length = 16 := rfl

/-- The hypotheses of the parse: the data at bit `0` of `D`, P03's well-formedness, `1 ≤ f`, `1 ≤ m` and the exact input-basis dimension
(`Request.Valid`, `valid_pctx`), and run constants large for the data (`K ≥ 16(|data|² + |data| + 1)`). -/
structure PCtx (q : Request) (D : ℕ) : Prop where
  at0 : At D 0 q.data
  wf : q.code.WellFormed
  f1 : 1 ≤ q.code.f
  m1 : 1 ≤ q.mI
  mi : q.mI = q.code.m
  K : 16 * (q.data.length * q.data.length + q.data.length + 1) ≤ G.K
  N : q.data.length + 1 ≤ G.N

/-- `Request.Valid` gives the instance part of the context. -/
theorem valid_pctx (q : Request) (hv : q.Valid) :
    q.code.WellFormed ∧ 1 ≤ q.code.f ∧ 1 ≤ q.mI ∧ q.mI = q.code.m := by
  obtain ⟨hwf, hvalid, hx, hm⟩ := hv
  have hmI : q.mI = q.code.m := by unfold Request.mI; rw [hx, Nat.log_pow (by norm_num)]
  have hf := Irreducible.natDegree_pos hvalid.1.1
  have hdeg := hvalid.1.2
  exact ⟨hwf, by omega, by omega, hmI⟩

section Ctx

variable {G} {q : Request} {D : ℕ} (c : PCtx G q D)
include c

theorem PCtx.d_pos : 1 ≤ q.data.length := by
  have h := (piece_at q c.at0 0 (natWord q.code.f) (by norm_num) rfl).2
  simp only [Nat.zero_add] at h
  have := posOf_le q 1; have := natWord_pos q.code.f; omega

theorem PCtx.W : q.data.length * q.data.length + q.data.length + 1 ≤ G.K / 16 :=
  (Nat.le_div_iff_mul_le (by norm_num)).2 (by have := c.K; omega)

theorem PCtx.K32 : 32 ≤ G.K := by have := c.K; have := c.d_pos; nlinarith

theorem PCtx.bd : BdOk G q.data.length := by
  refine ⟨?_, c.N⟩
  have hW := c.W
  have h1 : q.data.length + 2 ≤ G.K := by
    have := Nat.div_le_self G.K 16; have := c.d_pos; have := Nat.le_mul_self q.data.length; omega
  have h2 : 2 ^ (q.data.length + 2) ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : q.data.length < 2 ^ q.data.length := Nat.lt_two_pow_self
  rw [pow_add] at h2
  unfold Glob.cap; omega

/-- Every value below `2^(|data|² + |data|)` fits a slot. -/
theorem PCtx.slot_lt {x a : ℕ} (hx : x < 2 ^ a) (ha : a ≤ q.data.length * q.data.length + q.data.length) :
    x < 2 ^ (G.K / 16) :=
  lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by have := c.W; omega))

theorem PCtx.slot_le {x : ℕ} (hx : x ≤ q.data.length) : x < 2 ^ (G.K / 16) :=
  c.slot_lt (a := x) Nat.lt_two_pow_self (by nlinarith)

end Ctx

end NearCubicGates.Adapters.ShortPCP.Machines.FL
