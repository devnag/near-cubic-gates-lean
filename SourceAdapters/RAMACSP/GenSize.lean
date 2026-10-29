import SourceAdapters.RAMACSP.GenSizeItems
import SourceAdapters.RAMACSP.GenFinal
import SourceAdapters.RAMACSP.CheckReads

/-!
# The size of the description

Paper: `lem:generator` ("The description of `I_x` has `poly(log t)` bits, and its constraint circuit has
`O(log³ t)` gates"; "Each pattern costs `O(m_H)` gates and each equation `O(L)` gates, which gives
`O((m_H+K+L)·log² t + m_H² + c_N) = O(log³ t)` gates") and `lem:acsp-degree` (`f = log T + O(log log T)`,
`c_N = O(log T)`).

- `consWord_length_le`: the serialized constraint circuit has at most `gatesBound = 3m² + 2m + 1 + (2m + 3)·I +
  I·itemBound` gates (`compileTerms_spec`, `Routing/CircuitTerms`), `I` the number of items (`GenSizeItems`), each of
  word length `≤ gateWordBound` (constants are reduced masks `< 2^f`, inputs index the bank, gate references precede:
  `WellFormedCircuit`);
- `ownInst_word_length_le`: every other field of the description is `poly(m_H, τ, |bank|, f)` (`wordBound`); the
  input basis has `m < τ` masks under `2 ≤ n ≤ t` (`inBasis_facts`);
- `BndP`: all of `m_H, f, τ, 2^q, |bank|, w, k, L` are `≤ A·(logScale t + 1)^a` for fixed `V`, closed under `+, ·, ^`
  (`bndP_word`), so the description has `≤ K·(logScale t + 1)^e` bits (`parameterSize_own`; export
  `RAMACSP.parameterSize`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMTrace
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

/-! ## The coordinate rows -/

theorem gateCount_squares {F : Type} [Field F] [CharP F 2] (r : ℕ) :
    Routing.Circuit.gateCount (squares (F := F) r) = r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [squares, Routing.Circuit.gateCount, ih]

theorem gateCount_lamExpr {F : Type} [Field F] [CharP F 2] {m : ℕ} (row : Fin m → F) :
    Routing.Circuit.gateCount (lamExpr row) ≤ m * m + 4 * m + 1 := by
  unfold lamExpr
  suffices h : ∀ rs : List (Fin m), (∀ r ∈ rs, r.val < m) → Routing.Circuit.gateCount
      (rs.foldr (fun r acc => Routing.Expr.add (.mul (.const (row r)) (squares r.val)) acc) (.const 0)) ≤
        rs.length * (m + 4) + 1 by
    have := h (List.finRange m) (fun r _ => r.isLt)
    rw [List.length_finRange] at this
    nlinarith
  intro rs hrs
  induction rs with
  | nil => simp [Routing.Circuit.gateCount]
  | cons r rs ih =>
    have h1 := ih (fun x hx => hrs x (by simp [hx]))
    have h2 := hrs r (by simp)
    simp only [List.foldr_cons, Routing.Circuit.gateCount, gateCount_squares, List.length_cons]
    nlinarith

/-! ## The circuit's size and its well-formedness -/

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

/-- The item-count bound. -/
def itemsBound (V : Verifier) (r : ClockRequest) : ℕ :=
  (Routing.routingItems (ownLayout V r.2)).length + 1000 * catX (ownRam V r) (tau V r.2) (laneExp V r.2) ^ 3

theorem ownItems_props {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (lam : ℕ → Routing.Expr F)
    (hlam : ∀ j, Routing.Circuit.gateCount (lam j) ≤ domExp V r.2 * domExp V r.2 + 4 * domExp V r.2 + 1) :
    (ownItems V r lam).length ≤ itemsBound V r ∧
      ((ownItems V r lam).map (fun t => Routing.Circuit.gateCount t.2)).sum ≤
        itemsBound V r * itemBound (codeLen V) (domExp V r.2) := by
  have hc : (ownRam V r).code.length = codeLen V := mnCode_length V _ _ _ _
  have hlen : (ownItems V r lam).length ≤ itemsBound V r := by
    unfold ownItems itemsBound routingPairs
    rw [List.length_append, List.length_map]
    have := machineItems_length_le (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r)
      RAMTrace.mnKind (tau V r.2) (inRecExp V r) lam
    exact Nat.add_le_add_left this _
  refine ⟨hlen, le_trans (sum_map_le _ _ (itemBound (codeLen V) (domExp V r.2)) (fun x hx => ?_))
    (Nat.mul_le_mul_right _ hlen)⟩
  unfold ownItems at hx
  rcases List.mem_append.mp hx with hx | hx
  · have := routing_gateCount_le (F := F) (ownLayout V r.2) x hx
    unfold itemBound; omega
  · have := machine_gateCount_le (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r)
      RAMTrace.mnKind (tau V r.2) (inRecExp V r) lam hlam x hx
    rw [hc] at this; exact this

/-- The gate-count bound of the constraint circuit. -/
def gatesBound (V : Verifier) (r : ClockRequest) : ℕ :=
  3 * (ownLayout V r.2).m ^ 2 + 2 * (ownLayout V r.2).m + 1 + (2 * (ownLayout V r.2).m + 3) * itemsBound V r +
    itemsBound V r * itemBound (codeLen V) (domExp V r.2)

attribute [local irreducible] ownLayout in
theorem compile_facts {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2)
    (e : Fin (ownLayout V r.2).m → F) (coords : Routing.Coordinates (ownLayout V r.2).m e) (lam : ℕ → Routing.Expr F)
    (hlr : ∀ j, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) (lam j))
    (hlg : ∀ j, Routing.Circuit.gateCount (lam j) ≤ domExp V r.2 * domExp V r.2 + 4 * domExp V r.2 + 1) :
    Routing.WellFormedCircuit ((Routing.globalBank (ownLayout V r.2)).length + 1)
        (Routing.Circuit.compileTerms (ownLayout V r.2) e coords (ownItems V r lam)) ∧
      (Routing.Circuit.compileTerms (ownLayout V r.2) e coords (ownItems V r lam)).gates.length ≤ gatesBound V r := by
  have hr := itemsReadInBank V F r hn hnt lam hlr
  obtain ⟨hwf, -, hsz⟩ := Routing.Circuit.compileTerms_spec (ownLayout V r.2) coords (ownItems V r lam) hr
  obtain ⟨hI, hS⟩ := ownItems_props V r lam hlg
  refine ⟨hwf, ?_⟩
  refine hsz.trans ?_
  unfold gatesBound
  have := Nat.mul_le_mul_left (2 * (ownLayout V r.2).m + 3) hI
  linarith

theorem ownCircuit_facts (r : ClockRequest) (h : ModulusGood V irrPoly r) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    Routing.WellFormedCircuit ((Routing.globalBank (ownLayout V r.2)).length + 1) (ownCircuit V irrPoly r h) ∧
      (ownCircuit V irrPoly r h).gates.length ≤ gatesBound V r := by
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
  unfold ownCircuit
  simp only []
  refine compile_facts V r hn hnt _ _ _ (fun j => ?_) (fun j => ?_)
  · split_ifs
    · exact lamExpr_reads _ _
    · trivial
  · split_ifs
    · exact gateCount_lamExpr _
    · simp [Routing.Circuit.gateCount]

/-! ## The serialized circuit -/

theorem natWord_length' (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 :=
  NearCubicGates.Adapters.ShortPCP.Machines.FL.natWord_len v

/-- The per-gate word bound. -/
def gateWordBound (G B f : ℕ) : ℕ := 12 * (G + B + f + 4)

theorem gateWord_le (G B f : ℕ) (hf : 1 ≤ f) (g : CodeGate)
    (h : match g with
      | .input v => v ≤ B
      | .const v => v < 2 ^ f
      | .add a b => a ≤ G ∧ b ≤ G
      | .mul a b => a ≤ G ∧ b ≤ G) :
    (gateWord g).length ≤ gateWordBound G B f := by
  have nb : ∀ v, natBitLength v ≤ v + 1 := natBitLength_le
  unfold gateWordBound
  cases g with
  | input v =>
    simp only [gateWord, List.length_append, natWord_length'] at h ⊢
    have := nb v; have := nb 0; simp [natBitLength] at *; omega
  | const v =>
    simp only [gateWord, List.length_append, natWord_length'] at h ⊢
    have := natBitLength_le_of_lt hf h; have := nb 1; have := nb 0; omega
  | add a b =>
    simp only [gateWord, List.length_append, natWord_length'] at h ⊢
    have := nb a; have := nb b; have := nb 2; omega
  | mul a b =>
    simp only [gateWord, List.length_append, natWord_length'] at h ⊢
    have := nb a; have := nb b; have := nb 3; omega

theorem listWord_length_le {α : Type} (g : α → List Bool) (L : List α) (B : ℕ) (h : ∀ x ∈ L, (g x).length ≤ B) :
    (listWord g L).length ≤ 2 * L.length + 3 + L.length * B := by
  unfold listWord
  rw [List.length_append, natWord_length', List.length_flatten, List.map_map]
  have := natBitLength_le L.length
  have := sum_map_le L (List.length ∘ g) B h
  omega

/-- The bound of the serialized circuit. -/
def consBound (V : Verifier) (r : ClockRequest) : ℕ :=
  2 * gatesBound V r + 3 + gatesBound V r *
    gateWordBound (gatesBound V r) ((Routing.globalBank (ownLayout V r.2)).length) (fieldExp V r.2)

attribute [local irreducible] ownLayout in
theorem consWord_length_le (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    (consWord V irrPoly r).length ≤ consBound V r := by
  unfold consWord ownCons
  split_ifs with h
  · obtain ⟨hwf, hsz⟩ := ownCircuit_facts V irrPoly r h hn hnt
    unfold ownConsOf
    have hl : ((ownCircuit V irrPoly r h).gates.map
        (gateMask (baseIrr V irrPoly r) (modulus_monic h.1) (fieldExp V r.2))).length ≤ gatesBound V r := by
      rw [List.length_map]; exact hsz
    refine le_trans (listWord_length_le _ _ (gateWordBound (gatesBound V r)
      ((Routing.globalBank (ownLayout V r.2)).length) (fieldExp V r.2)) ?_) ?_
    · intro x hx
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg0
      have hw := hwf ⟨i, hi⟩
      simp only [Fin.getElem_fin] at hw
      rw [hgi] at hw
      apply gateWord_le _ _ _ (one_le_fieldExp V r.2)
      cases g0 with
      | input v => simp only [gateMask] at hw ⊢; omega
      | const c => exact WireExponent3_5.GF.ofPoly_lt _ _
      | add a b => simp only [gateMask] at hw ⊢; omega
      | mul a b => simp only [gateMask] at hw ⊢; omega
    · unfold consBound
      have := Nat.mul_le_mul_right (gateWordBound (gatesBound V r)
        ((Routing.globalBank (ownLayout V r.2)).length) (fieldExp V r.2)) hl
      omega
  · unfold consBound; simp [listWord, natWord_length', natBitLength]; omega

/-! ## Bounds in `logScale t` (under `2 ≤ n ≤ t`) -/

/-- The scale `logScale t + 1`. -/
def Zs (r : ClockRequest) : ℕ := logScale r.2 + 1

/-- `g r ≤ A·(logScale t + 1)^a` on every request with `2 ≤ n ≤ t`. -/
def BndP (g : ClockRequest → ℕ) : Prop := ∃ A a : ℕ, ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 → g r ≤ A * Zs r ^ a

theorem one_le_Zs (r : ClockRequest) : 1 ≤ Zs r := by simp [Zs]

namespace BndP

theorem mono {g h : ClockRequest → ℕ} (hg : BndP g) (hle : ∀ r, 2 ≤ r.1.1 → r.1.1 ≤ r.2 → h r ≤ g r) : BndP h := by
  obtain ⟨A, a, hA⟩ := hg
  exact ⟨A, a, fun r h1 h2 => (hle r h1 h2).trans (hA r h1 h2)⟩

theorem const (c : ℕ) : BndP fun _ => c := ⟨c, 0, fun r _ _ => by simp⟩

theorem scale : BndP Zs := ⟨1, 1, fun r _ _ => by simp⟩

theorem add {g h : ClockRequest → ℕ} (hg : BndP g) (hh : BndP h) : BndP fun r => g r + h r := by
  obtain ⟨A, a, hA⟩ := hg
  obtain ⟨B, b, hB⟩ := hh
  refine ⟨A + B, a + b, fun r h1 h2 => ?_⟩
  have p1 : Zs r ^ a ≤ Zs r ^ (a + b) := Nat.pow_le_pow_right (one_le_Zs r) (by omega)
  have p2 : Zs r ^ b ≤ Zs r ^ (a + b) := Nat.pow_le_pow_right (one_le_Zs r) (by omega)
  have := hA r h1 h2
  have := hB r h1 h2
  have := Nat.mul_le_mul_left A p1
  have := Nat.mul_le_mul_left B p2
  show g r + h r ≤ _
  rw [Nat.add_mul]; omega

theorem mul {g h : ClockRequest → ℕ} (hg : BndP g) (hh : BndP h) : BndP fun r => g r * h r := by
  obtain ⟨A, a, hA⟩ := hg
  obtain ⟨B, b, hB⟩ := hh
  refine ⟨A * B, a + b, fun r h1 h2 => ?_⟩
  calc g r * h r ≤ (A * Zs r ^ a) * (B * Zs r ^ b) := Nat.mul_le_mul (hA r h1 h2) (hB r h1 h2)
    _ = A * B * Zs r ^ (a + b) := by rw [pow_add]; ring

theorem pow {g : ClockRequest → ℕ} (hg : BndP g) (e : ℕ) : BndP fun r => g r ^ e := by
  obtain ⟨A, a, hA⟩ := hg
  refine ⟨A ^ e, a * e, fun r h1 h2 => ?_⟩
  calc g r ^ e ≤ (A * Zs r ^ a) ^ e := Nat.pow_le_pow_left (hA r h1 h2) e
    _ = A ^ e * Zs r ^ (a * e) := by rw [mul_pow, ← pow_mul]

end BndP

theorem bits_le_logScale (t : ℕ) : t.bits.length ≤ logScale t := by
  rw [Nat.size_eq_bits_len] at *
  exact Nat.size_le.2 (logScale_facts t).2.2.2

theorem bndP_f : BndP (fun r => fieldExp V r.2) := by
  refine ⟨40 * (clockConst V + tagExp V + 5), 1, fun r _ _ => ?_⟩
  have h1 := fieldExp_le V r.2
  have h2 := bits_le_logScale r.2
  simp only [Zs, pow_one]
  nlinarith

theorem bndP_tau : BndP (fun r => tau V r.2) :=
  bndP_f V |>.mono (fun r _ _ => by
    have := tau_lt_domExp V r.2; have := domExp_add_two_le_fieldExp V r.2; omega)

theorem bndP_m : BndP (fun r => domExp V r.2) :=
  bndP_f V |>.mono (fun r _ _ => by have := domExp_add_two_le_fieldExp V r.2; omega)

theorem bndP_C : BndP (fun r => 2 ^ colExp V r.2) := by
  refine ⟨64 * 2 ^ tagExp V * (clockConst V + 1), 1, fun r _ _ => ?_⟩
  have h1 := sixteenC_le V r.2
  have h2 := bits_le_logScale r.2
  simp only [Zs, pow_one]
  generalize 2 ^ tagExp V = D at *
  generalize 2 ^ colExp V r.2 = C at *
  generalize clockConst V = c at *
  generalize logScale r.2 = L at *
  generalize r.2.bits.length = b at *
  have e1 : b + c ≤ (c + 1) * (L + 1) := by nlinarith
  have e2 : D * (b + c) ≤ D * ((c + 1) * (L + 1)) := Nat.mul_le_mul_left _ e1
  have e3 : 64 * D * (b + c) = 64 * (D * (b + c)) := by ring
  have e4 : 64 * D * (c + 1) * (L + 1) = 64 * (D * ((c + 1) * (L + 1))) := by ring
  omega

theorem bndP_bank : BndP (fun r => (Routing.globalBank (ownLayout V r.2)).length) := by
  refine ((((BndP.mul (BndP.const 8) (bndP_tau V)).add (BndP.const 8)).add (bndP_m V)).add
    (BndP.mul (BndP.const 16) (bndP_C V)) |>.add (BndP.const 3)).mono (fun r _ _ => ?_)
  rw [Routing.LayoutFacts.globalBank_length]
  have hk : (ownLayout V r.2).k = tau V r.2 + 1 := rfl
  have hq : (ownLayout V r.2).q ≤ domExp V r.2 := by
    show colExp V r.2 ≤ domExp V r.2; unfold domExp; omega
  have hC : (ownLayout V r.2).C = 2 ^ colExp V r.2 := rfl
  rw [hk, hC]; omega

theorem bndP_bits : BndP (fun r => r.2.bits.length) :=
  ⟨1, 1, fun r _ _ => by have := bits_le_logScale r.2; simp only [Zs, pow_one]; omega⟩

theorem bndP_catX : BndP (fun r => catX (ownRam V r) (tau V r.2) (laneExp V r.2)) := by
  refine (((BndP.mul (BndP.const 2) (bndP_bits)).add (BndP.const (2 * clockConst V + regCount V + codeLen V + 3))).add
    (BndP.mul (BndP.const 2) (bndP_tau V))).mono (fun r _ _ => ?_)
  unfold catX
  have hw : (ownRam V r).w = wordWidth (clockConst V) r.2 := rfl
  have hk : (ownRam V r).k = regCount V := rfl
  have hc : (ownRam V r).code.length = codeLen V := mnCode_length V _ _ _ _
  have := w_le_bits V r.2
  have hl : laneExp V r.2 = tau V r.2 + 1 := rfl
  omega

theorem bndP_items : BndP (fun r => itemsBound V r) := by
  refine ((BndP.mul (BndP.mul (BndP.const 2) ((bndP_tau V).add (BndP.const 1))) ((bndP_m V).add (BndP.const 4))).add
    (BndP.mul (BndP.const 1000) (BndP.pow (bndP_catX V) 3))).mono (fun r _ _ => ?_)
  unfold itemsBound
  have h1 := Routing.Circuit.routingItems_length_le (ownLayout V r.2)
  have hk : (ownLayout V r.2).k = tau V r.2 + 1 := rfl
  have hq : (ownLayout V r.2).q ≤ domExp V r.2 := by show colExp V r.2 ≤ domExp V r.2; unfold domExp; omega
  rw [hk] at h1
  have := Nat.mul_le_mul_left (2 * (tau V r.2 + 1)) (show (ownLayout V r.2).q + 4 ≤ domExp V r.2 + 4 by omega)
  have e : 2 * (tau V r.2 + 1) * ((ownLayout V r.2).q + 4) = 2 * (tau V r.2 + 1) * (ownLayout V r.2).q +
    8 * (tau V r.2 + 1) := by ring
  show _ ≤ 2 * (tau V r.2 + 1) * (domExp V r.2 + 4) + 1000 * catX (ownRam V r) (tau V r.2) (laneExp V r.2) ^ 3
  omega

theorem bndP_gates : BndP (fun r => gatesBound V r) := by
  have hm := bndP_m V
  have hI := bndP_items V
  refine (((((BndP.mul (BndP.const 3) (BndP.pow hm 2)).add (BndP.mul (BndP.const 2) hm)).add (BndP.const 1)).add
    (BndP.mul ((BndP.mul (BndP.const 2) hm).add (BndP.const 3)) hI)).add
    (BndP.mul hI ((((BndP.const (30 * codeLen V)).add (BndP.mul hm hm)).add (BndP.mul (BndP.const 4) hm)).add
      (BndP.const 70)))).mono (fun r _ _ => ?_)
  unfold gatesBound itemBound
  rw [ownLayout_m]

theorem bndP_cons : BndP (fun r => consBound V r) := by
  have hG := bndP_gates V
  refine ((((BndP.mul (BndP.const 2) hG).add (BndP.const 3)).add (BndP.mul hG (BndP.mul (BndP.const 12)
    ((((hG.add (bndP_bank V)).add (bndP_f V)).add (BndP.const 4)))))).mono (fun r _ _ => ?_))
  unfold consBound gateWordBound
  exact le_rfl

/-! ## The instance word -/

/-- The bound of the instance word: `f`, `irr`, the basis and offset of `H`, the neighbor pairs, `cons`, the basis
and offset of `I` (in the order of `ownInst_word`). -/
def wordBound (V : Verifier) (r : ClockRequest) : ℕ :=
  (2 * fieldExp V r.2 + 3) + (2 * fieldExp V r.2 + 5) +
    (2 * domExp V r.2 + 3 + domExp V r.2 * (2 * domExp V r.2 + 1)) + 3 +
    (2 * (Routing.globalBank (ownLayout V r.2)).length + 3 +
      (Routing.globalBank (ownLayout V r.2)).length * (2 * domExp V r.2 + 4)) +
    consBound V r +
    (2 * tau V r.2 + 3 + tau V r.2 * (2 * domExp V r.2 + 1)) +
    (2 * domExp V r.2 + 1)

theorem natWord_le_of_lt {v L : ℕ} (hL : 1 ≤ L) (h : v < 2 ^ L) : (natWord v).length ≤ 2 * L + 1 := by
  rw [natWord_length']; have := natBitLength_le_of_lt hL h; omega

theorem natWord_le_self (v : ℕ) : (natWord v).length ≤ 2 * v + 3 := by
  rw [natWord_length']; have := natBitLength_le v; omega

/-- Under `2 ≤ n ≤ t` the input basis has at most `τ` masks, each below `2^{m_H}`. -/
theorem inBasis_facts (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    (inBasis V r).length ≤ tau V r.2 ∧ ∀ a ∈ inBasis V r, a < 2 ^ domExp V r.2 := by
  obtain ⟨-, -, hω, hmτ, -⟩ := inExp_facts V r hn hnt
  have hτm := tau_lt_domExp V r.2
  have hdm : domExp V r.2 = laneExp V r.2 + stageExp V r.2 + colExp V r.2 + 4 := rfl
  have hq : colExp V r.2 = tagExp V + wordExp V r.2 := rfl
  refine ⟨by simp only [inBasis, List.length_append, List.length_map, List.length_range]; omega, fun a ha => ?_⟩
  simp only [inBasis, List.mem_append, List.mem_map, List.mem_range] at ha
  rcases ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact Nat.pow_lt_pow_right (by norm_num) (by omega)

attribute [local irreducible] ownLayout in
theorem ownInst_word_length_le (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    (ownInst V irrPoly (ownCons V irrPoly) r).word.length ≤ wordBound V r := by
  have hm1 : 1 ≤ domExp V r.2 := by unfold domExp; omega
  have hτm := tau_lt_domExp V r.2
  rw [ownInst_word]
  simp only [List.length_append]
  -- f, irr
  have w2 := natWord_le_self (fieldExp V r.2)
  have w3 : (natWord (modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2))).length ≤ 2 * fieldExp V r.2 + 5 := by
    have := natWord_le_of_lt (L := fieldExp V r.2 + 1) (by omega) (WireExponent3_5.GF.ofPoly_lt (irrPoly (fieldExp V r.2)) (fieldExp V r.2 + 1))
    unfold modMask; omega
  -- the basis and offset of `H`
  have w4 : (listWord natWord ((List.range (domExp V r.2)).map (2 ^ ·))).length ≤
      2 * domExp V r.2 + 3 + domExp V r.2 * (2 * domExp V r.2 + 1) := by
    have := listWord_length_le natWord ((List.range (domExp V r.2)).map (2 ^ ·)) (2 * domExp V r.2 + 1) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact natWord_le_of_lt hm1 (Nat.pow_lt_pow_right (by norm_num) (List.mem_range.mp hb)))
    simpa only [List.length_map, List.length_range] using this
  have w5 : (natWord 0).length ≤ 3 := natWord_le_self 0
  -- the neighbor pairs `(1, b)`
  have w6 : (listWord ACSP.Affine.Instance.pairWord
      ((Routing.globalBank (ownLayout V r.2)).map (fun b => (1, b)))).length ≤
      2 * (Routing.globalBank (ownLayout V r.2)).length + 3 +
        (Routing.globalBank (ownLayout V r.2)).length * (2 * domExp V r.2 + 4) := by
    have := listWord_length_le ACSP.Affine.Instance.pairWord
      ((Routing.globalBank (ownLayout V r.2)).map (fun b => (1, b))) (2 * domExp V r.2 + 4) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have hbl : b < 2 ^ domExp V r.2 := by
        have := Routing.LayoutFacts.globalBank_lt (ownLayout V r.2) b hb
        rwa [Routing.Layout.h, ownLayout_m] at this
      have h1 := natWord_le_of_lt hm1 hbl
      have h2 : (natWord 1).length = 3 := by rw [natWord_length']; simp [natBitLength]
      simp only [ACSP.Affine.Instance.pairWord, List.length_append]
      omega)
    simpa only [List.length_map] using this
  -- cons
  have w7 := consWord_length_le V irrPoly r hn hnt
  unfold consWord at w7
  -- the basis and offset of `I`
  obtain ⟨hil, hia⟩ := inBasis_facts V r hn hnt
  have w8 : (listWord natWord (inBasis V r)).length ≤ 2 * tau V r.2 + 3 + tau V r.2 * (2 * domExp V r.2 + 1) := by
    have := listWord_length_le natWord (inBasis V r) (2 * domExp V r.2 + 1) (fun a ha => natWord_le_of_lt hm1 (hia a ha))
    have := Nat.mul_le_mul_right (2 * domExp V r.2 + 1) hil
    omega
  have w9 : (natWord (2 ^ tau V r.2)).length ≤ 2 * domExp V r.2 + 1 :=
    natWord_le_of_lt hm1 (Nat.pow_lt_pow_right (by norm_num) hτm)
  unfold wordBound
  omega

theorem bndP_word : BndP (fun r => wordBound V r) := by
  have hτ := bndP_tau V
  have hf := bndP_f V
  have hm := bndP_m V
  have hB := bndP_bank V
  have hc := bndP_cons V
  refine (((((((((BndP.mul (BndP.const 2) hf).add (BndP.const 3)).add ((BndP.mul (BndP.const 2) hf).add
    (BndP.const 5))).add
    ((((BndP.mul (BndP.const 2) hm).add (BndP.const 3))).add (BndP.mul hm ((BndP.mul (BndP.const 2) hm).add
      (BndP.const 1))))).add (BndP.const 3)).add
    ((((BndP.mul (BndP.const 2) hB).add (BndP.const 3))).add (BndP.mul hB ((BndP.mul (BndP.const 2) hm).add
      (BndP.const 4))))).add hc).add
    ((((BndP.mul (BndP.const 2) hτ).add (BndP.const 3))).add (BndP.mul hτ ((BndP.mul (BndP.const 2) hm).add
      (BndP.const 1))))).add ((BndP.mul (BndP.const 2) hm).add (BndP.const 1))).mono (fun r _ _ => ?_)
  unfold wordBound
  exact le_of_eq (by ring)

/-- **The parameter size** (`lem:generator`, "The description of `I_x` has `poly(log t)` bits"): the description has
length polynomial in `logScale t` on every request with `2 ≤ n ≤ t`. -/
theorem parameterSize_own (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) :
    ParameterSize V irrPoly (ownCons V irrPoly) := by
  obtain ⟨A, a, hA⟩ := bndP_word V
  exact ⟨A, a, fun r h1 h2 => (ownInst_word_length_le V irrPoly r h1 h2).trans (hA r h1 h2)⟩

end NearCubicGates.Adapters.RAMACSP.Gen

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.Joins NearCubicWires.RepairOrdinary Polynomial

/-- **Export: the parameter size** (`lem:generator`) of the instance with the emitted constraint circuit `ownCons`. -/
theorem parameterSize : ∀ (irrPoly : ℕ → (ZMod 2)[X]) (V : Verifier), ParameterSize V irrPoly (ownCons V irrPoly) :=
  fun irrPoly V => Gen.parameterSize_own V irrPoly

end NearCubicGates.Adapters.RAMACSP
