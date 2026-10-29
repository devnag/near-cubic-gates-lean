import SourceAdapters.RAMACSP.GenItemsMain
import SourceAdapters.RAMACSP.GenItemsWF
import SourceAdapters.Routing.LayoutBank

/-!
# The machine-items printer as an ordinary machine (the generator's stage G5, machine catalog)

Paper: `lem:generator`. The complete ordinary machine writes the machine
item stream, in order, within a fixed polynomial budget.

- `den_mainP`: on the request's state, `mainP` prints exactly `machineNums`;
- `machineItems_readsIn`: every read of every machine item is an offset of the global bank, on every request (the
  access census of `app:affine-embedding`; the argument of `CheckReads.itemsReadInBank`, with `τ < w` for every clock);
- `machineNums_lt`: every printed number is below `2^(f+1)`;
- **`machineItemsWF`**: the seam `Gen.MachineItemsWF` from Shoup's choice, its irreducibility, and the coordinate
  machine.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary
open Polynomial

variable {G : Glob} (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
  (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly)

attribute [local irreducible] ownLayout baseIrr in
/-- **The printer prints the machine-item numbers.** -/
theorem den_mainP (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (hc : CoordV V irrPoly hI r s) :
    den G s (mainP V) = machineNums V irrPoly r := by
  unfold machineNums
  rw [dif_pos (modulusGood V irrPoly hI r)]
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
  exact den_mainP_gen V (F := Field2 (baseIrr V irrPoly r))
    (termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)))
    (Routing.TermsMachine.termsMask_zero _ _) (Routing.TermsMachine.termsMask_one _ _) r hR hb
    (termsLam V irrPoly r (modulusGood V irrPoly hI r)) (den_b5 V irrPoly hI r hR hb hc)

/-! ## Every read is a bank offset, on every request -/

theorem machineItems_readsIn {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (lam : ℕ → Routing.Expr F)
    (hlam : ∀ j, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) (lam j)) :
    ∀ t ∈ machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind
      (tau V r.2) (inRecExp V r) lam, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) t.2 := by
  intro t hm
  have hK : (dims (ownRam V r) (tau V r.2)).K = regCount V := rfl
  have hL : (dims (ownRam V r) (tau V r.2)).L = codeLen V := mnCode_length V _ _ _ _
  have hw : (dims (ownRam V r) (tau V r.2)).w = 2 ^ wordExp V r.2 := wordW_eq V r.2
  have hτ : (dims (ownRam V r) (tau V r.2)).τ < (dims (ownRam V r) (tau V r.2)).w := by
    simp only [dims]; exact tau_lt_wordW_all V r.2
  have hβ : (dims (ownRam V r) (tau V r.2)).β ≤ (dims (ownRam V r) (tau V r.2)).τ := by
    simp only [dims]; exact Nat.sub_le _ _
  have hF : 32 + 3 * regCount V + 2 * codeLen V ≤ 2 ^ tagExp V := ftags_bound V
  have hq : (ownLayout V r.2).q = tagExp V + wordExp V r.2 := by simp only [ownLayout, colExp]
  have hk : (ownLayout V r.2).k = tau V r.2 + 1 := by simp only [ownLayout, laneExp]
  have hw1 : 1 ≤ (ownRam V r).w := by
    have : (dims (ownRam V r) (tau V r.2)).w = (ownRam V r).w := by simp only [dims]
    omega
  have hom : 0 < 2 ^ wordExp V r.2 := Nat.two_pow_pos _
  have mem := localOffset_mem (ownLayout V r.2) (wordExp V r.2) (tagExp V) hq
  have tok := tCell_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have rok := recCell_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have sok := sCell_ok _ _ _ _ _ hK hL hw hτ hF
  have thok := tHost_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have shok := sHost_ok _ _ _ _ _ hK hL hw hτ hF
  have dok := dstCell_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have role3 : ∀ c : Cell, c.Ok (wordExp V r.2) (tagExp V) → c.role ≤ 1 → ∀ rr, rr < 8 →
      (⟨c.tag, c.bit, rr, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) :=
    fun c hc _ rr hrr => ⟨hc.1, hc.2.1, hrr, show (1 : ℕ) < 2 by norm_num⟩
  simp only [machineItems, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_range,
    List.not_mem_nil, or_false] at hm
  rcases hm with ((((((h | h) | h) | h) | h) | h) | h) | h
  · obtain ⟨q, hq', rfl⟩ := h
    have hqa := mem_timeEqList _ q hq'
    refine toRouting_reads _ _ _ fun v hv => ?_
    have hva := timeEq_reads_active _ _ _ hw1 q hqa v hv
    cases v with
    | inl s => exact mem _ _ (thok q hqa) (tok s hva)
    | inr s => exact mem _ _ (thok q hqa) (rok s hva)
  · obtain ⟨s, hs, rfl⟩ := h
    have hc := tok s (mem_timeSlotList _ s hs)
    have hh := role3 _ hc (tCell_role _ _ s).1 ((tCell (regCount V) (codeLen V) s).role + 3)
      (by have := (tCell_role (regCount V) (codeLen V) s).1; omega)
    exact ⟨mem _ _ hh hc, mem _ _ hh hc⟩
  · obtain ⟨cp, hcp, h⟩ := h
    have hdc := dok cp (mem_copyList _ cp hcp)
    have hh : (⟨(dstCell (regCount V) (codeLen V) cp).tag, (dstCell (regCount V) (codeLen V) cp).bit, 5, 1⟩ :
        Cell).Ok (wordExp V r.2) (tagExp V) :=
      ⟨hdc.1, hdc.2.1, show (5 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with rfl | ⟨u, hu, rfl⟩
    · exact mem _ _ hh hdc
    · exact ⟨mem _ _ hh hdc, pred5_mem _ u (by rw [hk]; omega)⟩
  · have hh : (⟨7, 0, 7, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) :=
      ⟨hom, show 7 < 2 ^ tagExp V by omega, show (7 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with ⟨b, -, rfl⟩ | rfl
    · refine toRouting_reads _ _ _ fun v hv => ?_
      have hva := outE_reads _ (tau V r.2) v hv
      cases v with
      | inl s => exact mem _ _ hh (tok s hva)
      | inr s => exact mem _ _ hh (rok s hva)
    · refine toRouting_reads _ _ _ fun v hv => ?_
      have hva := accE_reads _ (tau V r.2) v hv
      cases v with
      | inl s => exact mem _ _ hh (tok s hva)
      | inr s => exact mem _ _ hh (rok s hva)
  · obtain ⟨q, hq', rfl⟩ := h
    have hqa := mem_sortEqList _ q hq'
    refine toRouting_reads _ _ _ fun v hv => ?_
    have hva := sortEq_reads_active _ hw1 q hqa v hv
    cases v with
    | inl s => exact mem _ _ (shok q hqa) (sok s hva)
    | inr s => exact mem _ _ (shok q hqa) (rok s hva)
  · obtain ⟨s, hs, rfl⟩ := h
    have hc := sok s (mem_sortSlotList _ s hs)
    have hh := role3 _ hc (sCell_role _ s).1 ((sCell (ownRam V r).w s).role + 3)
      (by have := (sCell_role (ownRam V r).w s).1; omega)
    exact ⟨mem _ _ hh hc, mem _ _ hh hc⟩
  · obtain ⟨s, hs, h⟩ := h
    obtain ⟨f, hf', j, hj', rfl⟩ := hs
    have hpa : (SSlot.prev f j).Active (dims (ownRam V r) (tau V r.2)) := by
      refine ⟨?_, hj'⟩
      rcases hf' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hc := sok _ hpa
    have hh : (⟨(sCell (ownRam V r).w (.prev f j)).tag, (sCell (ownRam V r).w (.prev f j)).bit, 6, 1⟩ : Cell).Ok
        (wordExp V r.2) (tagExp V) := ⟨hc.1, hc.2.1, show (6 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with rfl | ⟨u, hu, rfl⟩
    · exact ⟨mem _ _ hh hc, trivial⟩
    · exact ⟨mem _ _ hh hc, pred6_mem _ u hu⟩
  · obtain ⟨s, hs, h⟩ := h
    have hc := rok s (mem_recSlotList _ s hs)
    have hh : (⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) :=
      ⟨hc.1, hc.2.1, show (7 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with ⟨E, hE, rfl⟩ | ⟨u, -, rfl⟩
    · exact inputEqs_reads _ _ lam hlam (Routing.Expr.read (some (localOffset (ownLayout V r.2) (wordExp V r.2)
        ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))) (mem _ _ hh hc) s E hE
    · exact mem _ _ hh hc

/-! ## The printed numbers are below `2^(f+1)` -/

theorem exprToks_lt {F : Type} (mk : F → ℕ) (B : ℕ) (bank : List ℕ) (hB : 6 ≤ B) (hmk : ∀ c, mk c < B)
    (hbank : ∀ b ∈ bank, b + 1 < B) :
    ∀ e : Routing.Expr F, Routing.Circuit.ReadsIn bank e → ∀ x ∈ (Joins.exprToks mk e).flatMap tokNums, x < B
  | .const c, _, x, hx => by
    simp [Joins.exprToks, tokNums] at hx; rcases hx with rfl | rfl <;> [omega; exact hmk c]
  | .read none, _, x, hx => by simp [Joins.exprToks, tokNums, Joins.varCode] at hx; omega
  | .read (some b), hr, x, hx => by
    simp [Joins.exprToks, tokNums, Joins.varCode] at hx
    rcases hx with rfl | rfl
    · omega
    · exact hbank b hr
  | .add a b, hr, x, hx => by
    simp only [Joins.exprToks, List.flatMap_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact exprToks_lt mk B bank hB hmk hbank a hr.1 x hx
    · exact exprToks_lt mk B bank hB hmk hbank b hr.2 x hx
    · simp [tokNums] at hx; omega
  | .mul a b, hr, x, hx => by
    simp only [Joins.exprToks, List.flatMap_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact exprToks_lt mk B bank hB hmk hbank a hr.1 x hx
    · exact exprToks_lt mk B bank hB hmk hbank b hr.2 x hx
    · simp [tokNums] at hx; omega
  | .square a, hr, x, hx => by
    simp only [Joins.exprToks, List.flatMap_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact exprToks_lt mk B bank hB hmk hbank a hr x hx
    · simp [tokNums] at hx; omega

theorem itemNums_lt {F : Type} (mk : F → ℕ) (B : ℕ) (bank : List ℕ) (hB : 6 ≤ B) (hmk : ∀ c, mk c < B)
    (hbank : ∀ b ∈ bank, b + 1 < B) {m : ℕ} (it : Routing.Pattern m × Routing.Expr F)
    (hr : Routing.Circuit.ReadsIn bank it.2) : ∀ x ∈ itemNums mk it, x < B := by
  intro x hx
  simp only [itemNums, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with ((rfl | hx) | hx) | (rfl | rfl)
  · omega
  · obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    rcases o with _ | _ | _ <;> simp [Joins.guardCode] <;> omega
  · exact exprToks_lt mk B bank hB hmk hbank _ hr x hx
  · omega
  · omega

/-- **Every printed number is below `B`** (for any field and masks below `B`, rows reading the bank). -/
theorem machineNums_lt_gen {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (r : ClockRequest)
    (lam : ℕ → Routing.Expr F)
    (hlam : ∀ j, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) (lam j)) (B : ℕ) (hB : 6 ≤ B)
    (hmk : ∀ c, mk c < B) (hbank : ∀ b ∈ Routing.globalBank (ownLayout V r.2), b + 1 < B) :
    ∀ x ∈ (machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind
      (tau V r.2) (inRecExp V r) lam).flatMap (itemNums mk), x < B := by
  intro x hx
  obtain ⟨it, hit, hx⟩ := List.mem_flatMap.mp hx
  exact itemNums_lt mk B _ hB hmk hbank it (machineItems_readsIn V r lam hlam it hit) x hx

theorem bank_succ_lt (r : ClockRequest) :
    ∀ b ∈ Routing.globalBank (ownLayout V r.2), b + 1 < 2 ^ (fieldExp V r.2 + 1) := by
  intro b hb
  have hmf : (ownLayout V r.2).m ≤ fieldExp V r.2 := by
    rw [ownLayout_m]; have := domExp_add_two_le_fieldExp V r.2; omega
  have h1 := Routing.LayoutFacts.globalBank_lt (ownLayout V r.2) b hb
  have h2 : 2 ^ (ownLayout V r.2).m ≤ 2 ^ fieldExp V r.2 := Nat.pow_le_pow_right (by norm_num) hmf
  have h3 : (ownLayout V r.2).h = 2 ^ (ownLayout V r.2).m := rfl
  rw [pow_succ]; omega

theorem six_le_field (r : ClockRequest) : 6 ≤ 2 ^ (fieldExp V r.2 + 1) := by
  have : 3 ≤ fieldExp V r.2 + 1 := by have := domExp_add_two_le_fieldExp V r.2; omega
  exact le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) this : 2 ^ 3 ≤ _)

include hI in
attribute [local irreducible] ownLayout baseIrr in
/-- **Every printed number is below `2^(f+1)`.** -/
theorem machineNums_lt (r : ClockRequest) (x : ℕ) (hx : x ∈ machineNums V irrPoly r) :
    x < 2 ^ (fieldExp V r.2 + 1) := by
  unfold machineNums at hx
  rw [dif_pos (modulusGood V irrPoly hI r)] at hx
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
  have hf : (termsRequest V irrPoly r (modulusGood V irrPoly hI r)).f = fieldExp V r.2 := rfl
  have hmk : ∀ c, termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)) c < 2 ^ (fieldExp V r.2 + 1) := fun c => by
    have h1 : termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
        (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)) c <
        2 ^ (termsRequest V irrPoly r (modulusGood V irrPoly hI r)).f := WireExponent3_5.GF.ofPoly_lt _ _
    have h2 : 2 ^ (termsRequest V irrPoly r (modulusGood V irrPoly hI r)).f ≤ 2 ^ (fieldExp V r.2 + 1) := by
      rw [hf]; exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    omega
  have hlam : ∀ j, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2))
      (termsLam V irrPoly r (modulusGood V irrPoly hI r) j) := by
    intro j
    dsimp only [termsLam]
    split
    · exact lamExpr_reads _ _
    · trivial
  exact machineNums_lt_gen V (F := Field2 (baseIrr V irrPoly r)) _ r _ hlam _ (six_le_field V r) hmk
    (bank_succ_lt V r) x hx

/-! ## The export -/

/-- **The machine-items printer** (`lem:generator`): an ordinary machine printing the item words of the machine catalog
on every clock request, within a polynomial budget. -/
theorem machineItemsWF (hP : NearCubicGates.Published.Shoup.PolyTimeIrrChoice irrPoly)
    (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly) (hC : Joins.CoordArrayWF) :
    Gen.MachineItemsWF V irrPoly :=
  machineItemsWF_of_printer V irrPoly hP hI hC (mainP V) (WF_mainP V) (Ok_mainP V)
    (fun _ r _ hR hb hc => den_mainP V irrPoly hI r hR hb hc) (fun r x hx => machineNums_lt V irrPoly hI r x hx)

end NearCubicGates.Adapters.RAMACSP.Gen.Items
