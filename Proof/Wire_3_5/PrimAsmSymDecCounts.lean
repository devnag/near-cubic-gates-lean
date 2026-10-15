import Proof.Wire_3_5.PrimAsmSymDecReq
import Proof.Wire_3_5.PrimAsmDataRun

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

def dM0 : Fin LNR := ⟨330, by decide⟩
def dM1 : Fin LNR := ⟨331, by decide⟩
def dM2 : Fin LNR := ⟨332, by decide⟩
def dM3 : Fin LNR := ⟨333, by decide⟩
def dMS : Fin LNR := ⟨334, by decide⟩
def dK2 : Fin LNR := ⟨335, by decide⟩

section Gen
variable {ns nr : ℕ} (cap : ℕ)

theorem seth_seth' (σ : WState ns nr) (s : Fin (ns + 1)) (a b : ℕ) : (σ.seth s a).seth s b = σ.seth s b :=
  WState.eq (by simp [Function.update_idem]) rfl rfl rfl

theorem seth_self (σ : WState ns nr) (s : Fin (ns + 1)) : σ.seth s (σ.sh s) = σ :=
  WState.eq (by simp) rfl rfl rfl

theorem read_unary (pre rest : List Bool) (c k : ℕ) (hk : k ≤ c) :
    readTapeBit (pre ++ (List.replicate c true ++ false :: rest)) (pre.length + k) = decide (k < c) := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show pre.length + k - pre.length = k by omega]
  by_cases h : k < c
  · rw [List.getElem?_append_left (by simp; exact h)]
    simp [h]
  · have : k = c := by omega
    subst this
    rw [List.getElem?_append_right (by simp)]
    simp

/-- Skip one unary count `1^c 0`. -/
def skipItemW (s : Fin (ns + 1)) : WM ns nr := .seq (.whs s (.fwd s)) (.fwd s)

theorem skipItem_spec (s : Fin (ns + 1)) (pre rest : List Bool) (c : ℕ) (σ : WState ns nr)
    (hst : σ.st s = pre ++ List.replicate c true ++ false :: rest) (hsh : σ.sh s = pre.length) :
    WExec cap (skipItemW s) σ (σ.seth s (pre.length + c + 1)) (3 * c + 3) := by
  have loop : ∀ m k, k + m = c →
      WExec cap (.whs s (.fwd s)) (σ.seth s (pre.length + k)) (σ.seth s (pre.length + c)) (3 * m + 1) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      subst hk
      exact WExec.whsF (by show readTapeBit _ _ = false; simp [hst, read_unary pre rest k k le_rfl])
    | succ m ih =>
      intro k hk
      have hb : wbit (σ.seth s (pre.length + k)) s = true := by
        show readTapeBit _ _ = true; simp [hst, read_unary pre rest c k (by omega)]; omega
      have e1 := WExec.fwd (cap := cap) s (σ.seth s (pre.length + k))
      have e2 := ih (k + 1) (by omega)
      rw [seth_seth'] at e1
      simp only [WState.seth_sh, Function.update_self] at e1
      rw [show pre.length + k + 1 = pre.length + (k + 1) by omega] at e1
      exact WExec.mono (WExec.whsT hb e1 e2) (by omega)
  have l0 := loop c 0 (by omega)
  have i0 : σ.seth s (pre.length + 0) = σ := by rw [Nat.add_zero, ← hsh, seth_self]
  rw [i0] at l0
  have e3 := WExec.fwd (cap := cap) s (σ.seth s (pre.length + c))
  rw [seth_seth'] at e3
  simp only [WState.seth_sh, Function.update_self] at e3
  exact WExec.mono (WExec.seq l0 e3) (by omega)

/-- Read one unary count `1^c 0` into `r` (`r += c`). -/
def readItemW (s : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .seq (.whs s (.seq (.inc r) (.fwd s))) (.fwd s)

theorem readItem_spec (s : Fin (ns + 1)) (r : Fin nr) (pre rest : List Bool) (c : ℕ) (σ : WState ns nr)
    (hst : σ.st s = pre ++ List.replicate c true ++ false :: rest) (hsh : σ.sh s = pre.length)
    (hc : σ.val r + c ≤ cap) :
    WExec cap (readItemW s r) σ ((σ.seth s (pre.length + c + 1)).setv r (σ.val r + c)) (7 * c + 3) := by
  have loop : ∀ m k, k + m = c →
      WExec cap (.whs s (.seq (.inc r) (.fwd s))) ((σ.seth s (pre.length + k)).setv r (σ.val r + k))
        ((σ.seth s (pre.length + c)).setv r (σ.val r + c)) (7 * m + 1) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      subst hk
      exact WExec.whsF (by show readTapeBit _ _ = false; simp [hst, read_unary pre rest k k le_rfl])
    | succ m ih =>
      intro k hk
      have hb : wbit ((σ.seth s (pre.length + k)).setv r (σ.val r + k)) s = true := by
        show readTapeBit _ _ = true; simp [hst, read_unary pre rest c k (by omega)]; omega
      have e1 := WExec.inc (cap := cap) r ((σ.seth s (pre.length + k)).setv r (σ.val r + k)) (by simp; omega)
      have e2 := WExec.fwd (cap := cap) s
        (((σ.seth s (pre.length + k)).setv r (σ.val r + k)).setv r
          (((σ.seth s (pre.length + k)).setv r (σ.val r + k)).val r + 1))
      have e3 := ih (k + 1) (by omega)
      have eq : (((σ.seth s (pre.length + k)).setv r (σ.val r + k)).setv r
          (((σ.seth s (pre.length + k)).setv r (σ.val r + k)).val r + 1)).seth s
          ((((σ.seth s (pre.length + k)).setv r (σ.val r + k)).setv r
          (((σ.seth s (pre.length + k)).setv r (σ.val r + k)).val r + 1)).sh s + 1) =
          (σ.seth s (pre.length + (k + 1))).setv r (σ.val r + (k + 1)) := by
        apply WState.eq
        · funext i; by_cases hi : i = s
          · subst hi; simp; omega
          · simp [Function.update_of_ne hi]
        · rfl
        · funext q; by_cases hq : q = r
          · subst hq; simp; omega
          · simp [Function.update_of_ne hq]
        · rfl
      rw [eq] at e2
      exact WExec.mono (WExec.whsT hb (WExec.seq e1 e2) e3) (by omega)
  have l0 := loop c 0 (by omega)
  have i0 : (σ.seth s (pre.length + 0)).setv r (σ.val r + 0) = σ := by
    rw [Nat.add_zero, Nat.add_zero, ← hsh, seth_self]; exact wsetv_same σ r
  rw [i0] at l0
  have e4 := WExec.fwd (cap := cap) s ((σ.seth s (pre.length + c)).setv r (σ.val r + c))
  have eq2 : ((σ.seth s (pre.length + c)).setv r (σ.val r + c)).seth s
      (((σ.seth s (pre.length + c)).setv r (σ.val r + c)).sh s + 1) =
      (σ.seth s (pre.length + c + 1)).setv r (σ.val r + c) := by
    apply WState.eq
    · funext i; by_cases hi : i = s
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  rw [eq2] at e4
  exact WExec.mono (WExec.seq l0 e4) (by omega)

/-- Past the stream's end the read finds no count: the register unchanged, the head one further. -/
theorem readItem_end (s : Fin (ns + 1)) (r : Fin nr) (σ : WState ns nr) (hsh : (σ.st s).length ≤ σ.sh s) :
    WExec cap (readItemW s r) σ (σ.seth s (σ.sh s + 1)) 3 := by
  have hb : wbit σ s = false := by
    show readTapeBit _ _ = false
    unfold readTapeBit
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hsh]
    rfl
  exact WExec.mono (WExec.seq (WExec.whsF hb) (WExec.fwd s σ)) (by omega)

end Gen

/-! ## The counts -/

variable (cap : ℕ) (x : ℕ)

theorem unaryList_take_succ (cy : List ℕ) (i : ℕ) (hi : i < cy.length) :
    Data.unaryList (cy.take (i + 1)) = Data.unaryList (cy.take i) ++ (List.replicate cy[i] true ++ [false]) := by
  unfold Data.unaryList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem unaryList_drop (cy : List ℕ) (i : ℕ) (hi : i < cy.length) :
    Data.unaryList (cy.drop i) = List.replicate cy[i] true ++ false :: Data.unaryList (cy.drop (i + 1)) := by
  unfold Data.unaryList
  rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem unaryList_length_le (cs : List ℕ) : (Data.unaryList cs).length = cs.sum + cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Data.unaryList] at ih ⊢; omega

/-- One circuit slot: `r += m_i` (`0` past the counts), the head at the next slot. -/
theorem readSlot_spec (r : Fin LNR) (cx cy : List ℕ) (i : ℕ) (σ : WState (LNS x) LNR)
    (hst : σ.st (sk x 113) = Data.unaryList (cx ++ cy))
    (hpos : (i < cy.length ∧ σ.sh (sk x 113) = (Data.unaryList cx ++ Data.unaryList (cy.take i)).length) ∨
      (cy.length ≤ i ∧ (Data.unaryList (cx ++ cy)).length ≤ σ.sh (sk x 113)))
    (hc : σ.val r + cy.getD i 0 ≤ cap) (Cmax : ℕ) (hC : ∀ c ∈ cy, c ≤ Cmax) :
    ∃ τ, WExec cap (readItemW (sk x 113) r) σ τ (7 * Cmax + 3) ∧ τ.val r = σ.val r + cy.getD i 0 ∧
      (∀ q, q ≠ r → τ.val q = σ.val q) ∧ τ.st = σ.st ∧ (∀ j, j ≠ sk x 113 → τ.sh j = σ.sh j) ∧ τ.cell = σ.cell ∧
      ((i + 1 < cy.length + 1 ∧ i + 1 ≤ cy.length ∧ i + 1 < cy.length →
          τ.sh (sk x 113) = (Data.unaryList cx ++ Data.unaryList (cy.take (i + 1))).length) ∧
        (cy.length ≤ i + 1 → (Data.unaryList (cx ++ cy)).length ≤ τ.sh (sk x 113))) := by
  rcases hpos with ⟨hi, hh⟩ | ⟨hi, hh⟩
  · have hu : Data.unaryList (cx ++ cy) = (Data.unaryList cx ++ Data.unaryList (cy.take i)) ++
        List.replicate cy[i] true ++ false :: Data.unaryList (cy.drop (i + 1)) := by
      have e : Data.unaryList cy = Data.unaryList (cy.take i) ++ Data.unaryList (cy.drop i) := by
        rw [← Data.unaryList_append, List.take_append_drop]
      rw [Data.unaryList_append, e, unaryList_drop cy i hi]
      simp only [List.append_assoc]
    have e := readItem_spec cap (sk x 113) r (Data.unaryList cx ++ Data.unaryList (cy.take i))
      (Data.unaryList (cy.drop (i + 1))) cy[i] σ (by rw [hst, hu]) hh
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hc; simpa using hc)
    have hgi : cy.getD i 0 = cy[i] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    refine ⟨_, WExec.mono e (by have := hC _ (List.getElem_mem hi); omega), ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
    · rw [hgi]; simp
    · intro q hq; simp [Function.update_of_ne hq]
    · intro j hj; simp [Function.update_of_ne hj]
    · intro _
      simp only [WState.setv_sh, WState.seth_sh, Function.update_self]
      rw [unaryList_take_succ cy i hi]
      simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
      omega
    · intro hle
      simp only [WState.setv_sh, WState.seth_sh, Function.update_self]
      have hlast : i + 1 = cy.length := by omega
      rw [hu]
      simp only [List.length_append, List.length_replicate, List.length_cons]
      have : cy.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [this]
      simp [Data.unaryList]
  · have e := readItem_end cap (sk x 113) r σ (by rw [hst]; exact hh)
    have hgi : cy.getD i 0 = 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]; rfl
    refine ⟨_, WExec.mono e (by omega), ?_, fun q _ => rfl, rfl, ?_, rfl, ?_, ?_⟩
    · rw [hgi]; simp
    · intro j hj; simp [Function.update_of_ne hj]
    · intro h; omega
    · intro _; simp; omega

/-- Skip the `|cx|` carrier counts (`dK` counts down). -/
def skipCountsW : WM (LNS x) LNR := .whr dK (.seq (.dec dK) (skipItemW (sk x 113)))

theorem skipCounts_spec (cx : List ℕ) (tail : List Bool) (Cmax : ℕ) (hC : ∀ c ∈ cx, c ≤ Cmax)
    (σ : WState (LNS x) LNR) (hst : σ.st (sk x 113) = Data.unaryList cx ++ tail) (hsh : σ.sh (sk x 113) = 0)
    (hK : σ.val dK = cx.length) (hcap : cx.length ≤ cap) :
    WExec cap (skipCountsW x) σ ((σ.seth (sk x 113) (Data.unaryList cx).length).setv dK 0)
      (cx.length * (3 * Cmax + 3 + 4) + 1) := by
  let S : ℕ → WState (LNS x) LNR := fun k =>
    (σ.seth (sk x 113) (Data.unaryList (cx.take k)).length).setv dK (cx.length - k)
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext i
      by_cases hi : i = sk x 113
      · subst hi; simp [S, hsh, Data.unaryList]
      · simp [S, Function.update_of_ne hi]
    · rfl
    · funext r
      by_cases hr : r = dK
      · subst hr; simp [S, hK]
      · simp [S, Function.update_of_ne hr]
    · rfl
  have hSn : S cx.length = (σ.seth (sk x 113) (Data.unaryList cx).length).setv dK 0 := by simp [S]
  have hloop := UnionMachine.Round.wloop cap dK (skipItemW (sk x 113)) (3 * Cmax + 3) cx.length S
    (fun k _ => by simp [S]) hcap
    (fun k hk => by
      have hu : σ.st (sk x 113) = Data.unaryList (cx.take k) ++ List.replicate cx[k] true ++
          false :: (Data.unaryList (cx.drop (k + 1)) ++ tail) := by
        have e : Data.unaryList cx = Data.unaryList (cx.take k) ++ Data.unaryList (cx.drop k) := by
          rw [← Data.unaryList_append, List.take_append_drop]
        rw [hst, e, unaryList_drop cx k hk]
        simp only [List.append_assoc, List.cons_append]
      have hx := skipItem_spec cap (sk x 113) (Data.unaryList (cx.take k)) (Data.unaryList (cx.drop (k + 1)) ++ tail)
        cx[k] ((S k).setv dK (cx.length - k - 1)) (by simp only [S, WState.setv_st, WState.seth_st]; exact hu)
        (by simp [S])
      refine WExec.mono (WExec.cast cap hx ?_ le_rfl) (by have := hC _ (List.getElem_mem hk); omega)
      apply WState.eq
      · funext i
        by_cases hi : i = sk x 113
        · subst hi
          simp only [S, WState.setv_sh, WState.seth_sh, Function.update_self]
          rw [unaryList_take_succ cx k hk]
          simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
          omega
        · simp [S, Function.update_of_ne hi]
      · rfl
      · funext r
        by_cases hr : r = dK
        · subst hr; simp [S]; omega
        · simp [S, Function.update_of_ne hr]
      · rfl)
  rw [hS0, hSn] at hloop
  exact hloop

theorem sum_getD4 (cy : List ℕ) (h : cy.length ≤ 4) :
    cy.getD 0 0 + cy.getD 1 0 + cy.getD 2 0 + cy.getD 3 0 = cy.sum := by
  rcases cy with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;> simp at h ⊢ <;> omega

/-- A slot's head position (before slot `i`): inside the circuit counts, or past the stream. -/
def SlotPos (cx cy : List ℕ) (i h : ℕ) : Prop :=
  (i < cy.length ∧ h = (Data.unaryList cx ++ Data.unaryList (cy.take i)).length) ∨
    (cy.length ≤ i ∧ (Data.unaryList (cx ++ cy)).length ≤ h)

theorem readSlot_step (r : Fin LNR) (cx cy : List ℕ) (i : ℕ) (σ : WState (LNS x) LNR)
    (hst : σ.st (sk x 113) = Data.unaryList (cx ++ cy)) (hpos : SlotPos cx cy i (σ.sh (sk x 113)))
    (hc : σ.val r + cy.getD i 0 ≤ cap) (Cmax : ℕ) (hC : ∀ c ∈ cy, c ≤ Cmax) :
    ∃ τ, WExec cap (readItemW (sk x 113) r) σ τ (7 * Cmax + 3) ∧ τ.val r = σ.val r + cy.getD i 0 ∧
      (∀ q, q ≠ r → τ.val q = σ.val q) ∧ τ.st = σ.st ∧ (∀ j, j ≠ sk x 113 → τ.sh j = σ.sh j) ∧ τ.cell = σ.cell ∧
      SlotPos cx cy (i + 1) (τ.sh (sk x 113)) := by
  obtain ⟨τ, e, v, k, s, h, c, p1, p2⟩ := readSlot_spec cap x r cx cy i σ hst hpos hc Cmax hC
  refine ⟨τ, e, v, k, s, h, c, ?_⟩
  by_cases hi : i + 1 < cy.length
  · exact Or.inl ⟨hi, p1 ⟨by omega, by omega, hi⟩⟩
  · exact Or.inr ⟨by omega, p2 (by omega)⟩

/-- **The counts program**: skip the carriers' counts, read four circuit slots, sum them. -/
def countsW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR dNC dK dT) (.seq (skipCountsW x) (.seq (readItemW (sk x 113) dM0)
    (.seq (readItemW (sk x 113) dM1) (.seq (readItemW (sk x 113) dM2) (.seq (readItemW (sk x 113) dM3)
      (.seq (addTo dM0 dMS dT) (.seq (addTo dM1 dMS dT) (.seq (addTo dM2 dMS dT) (addTo dM3 dMS dT)))))))))

/-- The counts program's cost bound. -/
def countsCost (nc Cmax Sm : ℕ) : ℕ :=
  18 * nc + 3 + 1 + (nc * (3 * Cmax + 3 + 4) + 1 + 1 + (4 * (7 * Cmax + 3 + 1) + 4 * (18 * Sm + 3 + 1)))

theorem counts_spec (cx cy : List ℕ) (hcy : cy.length ≤ 4) (Cmax : ℕ) (hC : ∀ c ∈ cx ++ cy, c ≤ Cmax)
    (σ : WState (LNS x) LNR) (hst : σ.st (sk x 113) = Data.unaryList (cx ++ cy)) (hsh : σ.sh (sk x 113) = 0)
    (hNC : σ.val dNC = cx.length) (zK : σ.val dK = 0) (zT : σ.val dT = 0) (z0 : σ.val dM0 = 0)
    (z1 : σ.val dM1 = 0) (z2 : σ.val dM2 = 0) (z3 : σ.val dM3 = 0) (zS : σ.val dMS = 0)
    (hcap : cx.length + cy.sum + Cmax + 1 ≤ cap) :
    ∃ τ c, WExec cap (countsW x) σ τ c ∧ τ.val dM0 = cy.getD 0 0 ∧ τ.val dM1 = cy.getD 1 0 ∧
      τ.val dM2 = cy.getD 2 0 ∧ τ.val dM3 = cy.getD 3 0 ∧ τ.val dMS = cy.sum ∧ τ.val dK = 0 ∧ τ.val dT = 0 ∧
      (∀ r, r ≠ dM0 → r ≠ dM1 → r ≠ dM2 → r ≠ dM3 → r ≠ dMS → r ≠ dK → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      (∀ j, j ≠ sk x 113 → τ.sh j = σ.sh j) ∧ τ.cell = σ.cell ∧ c ≤ countsCost cx.length Cmax cy.sum := by
  have hCx : ∀ c ∈ cx, c ≤ Cmax := fun c hc => hC c (List.mem_append_left _ hc)
  have hCy : ∀ c ∈ cy, c ≤ Cmax := fun c hc => hC c (List.mem_append_right _ hc)
  have hg : ∀ i, cy.getD i 0 ≤ cy.sum := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : cy[i]? with
    | none => simp
    | some v =>
      simp only [Option.getD_some]
      exact List.le_sum_of_mem (List.mem_of_getElem? h)
  -- K := |cx|
  have e1 := FinalPass.Hash4.wcopyR_spec cap dNC dK dT (by decide) (by decide) (by decide) σ zK zT (by omega)
  rw [hNC] at e1
  obtain ⟨σ1, h1⟩ : ∃ y, y = σ.setv dK cx.length := ⟨_, rfl⟩
  rw [← h1] at e1
  -- skip the carriers
  have e2 := skipCounts_spec cap x cx (Data.unaryList cy) Cmax hCx σ1
    (by rw [h1]; simp only [WState.setv_st]; rw [hst, Data.unaryList_append]) (by rw [h1]; exact hsh)
    (by rw [h1]; simp) (by omega)
  obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 113) (Data.unaryList cx).length).setv dK 0 := ⟨_, rfl⟩
  rw [← h2] at e2
  have k2 : ∀ r, r ≠ dK → σ2.val r = σ.val r := fun r hr => by
    rw [h2, h1]; simp [Function.update_of_ne hr]
  have st2 : σ2.st (sk x 113) = Data.unaryList (cx ++ cy) := by rw [h2, h1]; exact hst
  have pos0 : SlotPos cx cy 0 (σ2.sh (sk x 113)) := by
    have hh : σ2.sh (sk x 113) = (Data.unaryList cx).length := by rw [h2]; simp
    by_cases h0 : 0 < cy.length
    · exact Or.inl ⟨h0, by rw [hh]; simp [Data.unaryList]⟩
    · have : cy = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact Or.inr ⟨by simp, by rw [hh]; simp⟩
  -- four slots
  obtain ⟨σ3, e3, v3, k3, s3, sh3, c3, pos1⟩ := readSlot_step cap x dM0 cx cy 0 σ2 st2 pos0
    (by rw [k2 _ (by decide), z0]; have := hg 0; omega) Cmax hCy
  obtain ⟨σ4, e4, v4, k4, s4, sh4, c4, pos2⟩ := readSlot_step cap x dM1 cx cy 1 σ3 (by rw [s3]; exact st2) pos1
    (by rw [k3 _ (by decide), k2 _ (by decide), z1]; have := hg 1; omega) Cmax hCy
  obtain ⟨σ5, e5, v5, k5, s5, sh5, c5, pos3⟩ := readSlot_step cap x dM2 cx cy 2 σ4 (by rw [s4, s3]; exact st2) pos2
    (by rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), z2]; have := hg 2; omega) Cmax hCy
  obtain ⟨σ6, e6, v6, k6, s6, sh6, c6, -⟩ := readSlot_step cap x dM3 cx cy 3 σ5
    (by rw [s5, s4, s3]; exact st2) pos3
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), z3]; have := hg 3; omega)
    Cmax hCy
  have k6a : ∀ r, r ≠ dM0 → r ≠ dM1 → r ≠ dM2 → r ≠ dM3 → r ≠ dK → σ6.val r = σ.val r := fun r a b c d e => by
    rw [k6 r d, k5 r c, k4 r b, k3 r a, k2 r e]
  have m0 : σ6.val dM0 = cy.getD 0 0 := by
    rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), v3, k2 _ (by decide), z0]; simp
  have m1 : σ6.val dM1 = cy.getD 1 0 := by
    rw [k6 _ (by decide), k5 _ (by decide), v4, k3 _ (by decide), k2 _ (by decide), z1]; simp
  have m2 : σ6.val dM2 = cy.getD 2 0 := by
    rw [k6 _ (by decide), v5, k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), z2]; simp
  have m3 : σ6.val dM3 = cy.getD 3 0 := by
    rw [v6, k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), z3]; simp
  have hsum := sum_getD4 cy hcy
  -- the sum
  have t6 : σ6.val dT = 0 := by rw [k6a _ (by decide) (by decide) (by decide) (by decide) (by decide), zT]
  have sS6 : σ6.val dMS = 0 := by rw [k6a _ (by decide) (by decide) (by decide) (by decide) (by decide), zS]
  have a1 := addTo_spec cap dM0 dMS dT (by decide) (by decide) (by decide) σ6 t6 (by rw [m0]; omega)
    (by rw [m0, sS6]; omega)
  obtain ⟨σ7, h7⟩ : ∃ y, y = σ6.setv dMS (σ6.val dMS + σ6.val dM0) := ⟨_, rfl⟩
  rw [← h7] at a1
  have k7 : ∀ r, r ≠ dMS → σ7.val r = σ6.val r := fun r hr => by rw [h7]; simp [Function.update_of_ne hr]
  have vS7 : σ7.val dMS = cy.getD 0 0 := by rw [h7]; simp [sS6, m0]
  have a2 := addTo_spec cap dM1 dMS dT (by decide) (by decide) (by decide) σ7 (by rw [k7 dT (by decide), t6])
    (by rw [k7 dM1 (by decide), m1]; omega) (by rw [vS7, k7 dM1 (by decide), m1]; omega)
  obtain ⟨σ8, h8⟩ : ∃ y, y = σ7.setv dMS (σ7.val dMS + σ7.val dM1) := ⟨_, rfl⟩
  rw [← h8] at a2
  have k8 : ∀ r, r ≠ dMS → σ8.val r = σ7.val r := fun r hr => by rw [h8]; simp [Function.update_of_ne hr]
  have vS8 : σ8.val dMS = cy.getD 0 0 + cy.getD 1 0 := by
    rw [h8]; simp only [WState.setv_val, Function.update_self]; rw [vS7, k7 dM1 (by decide), m1]
  have a3 := addTo_spec cap dM2 dMS dT (by decide) (by decide) (by decide) σ8
    (by rw [k8 dT (by decide), k7 dT (by decide), t6]) (by rw [k8 dM2 (by decide), k7 dM2 (by decide), m2]; omega)
    (by rw [vS8, k8 dM2 (by decide), k7 dM2 (by decide), m2]; omega)
  obtain ⟨σ9, h9⟩ : ∃ y, y = σ8.setv dMS (σ8.val dMS + σ8.val dM2) := ⟨_, rfl⟩
  rw [← h9] at a3
  have k9 : ∀ r, r ≠ dMS → σ9.val r = σ8.val r := fun r hr => by rw [h9]; simp [Function.update_of_ne hr]
  have vS9 : σ9.val dMS = cy.getD 0 0 + cy.getD 1 0 + cy.getD 2 0 := by
    rw [h9]; simp only [WState.setv_val, Function.update_self]; rw [vS8, k8 dM2 (by decide), k7 dM2 (by decide), m2]
  have a4 := addTo_spec cap dM3 dMS dT (by decide) (by decide) (by decide) σ9
    (by rw [k9 dT (by decide), k8 dT (by decide), k7 dT (by decide), t6])
    (by rw [k9 dM3 (by decide), k8 dM3 (by decide), k7 dM3 (by decide), m3]; omega)
    (by rw [vS9, k9 dM3 (by decide), k8 dM3 (by decide), k7 dM3 (by decide), m3]; omega)
  obtain ⟨σ10, h10⟩ : ∃ y, y = σ9.setv dMS (σ9.val dMS + σ9.val dM3) := ⟨_, rfl⟩
  rw [← h10] at a4
  have k10 : ∀ r, r ≠ dMS → σ10.val r = σ6.val r := fun r hr => by
    rw [h10]; simp [Function.update_of_ne hr]; rw [k9 r hr, k8 r hr, k7 r hr]
  have vS10 : σ10.val dMS = cy.sum := by
    rw [h10]; simp only [WState.setv_val, Function.update_self]
    rw [vS9, k9 dM3 (by decide), k8 dM3 (by decide), k7 dM3 (by decide), m3, hsum]
  have st10 : σ10.st = σ.st := by
    have : σ10.st = σ6.st := by rw [h10, h9, h8, h7]; rfl
    rw [this, s6, s5, s4, s3, h2, h1]; rfl
  have ce10 : σ10.cell = σ.cell := by
    have : σ10.cell = σ6.cell := by rw [h10, h9, h8, h7]; rfl
    rw [this, c6, c5, c4, c3, h2, h1]; rfl
  have sh10 : ∀ j, j ≠ sk x 113 → σ10.sh j = σ.sh j := by
    intro j hj
    have : σ10.sh = σ6.sh := by rw [h10, h9, h8, h7]; rfl
    rw [this, sh6 j hj, sh5 j hj, sh4 j hj, sh3 j hj, h2, h1]
    simp [Function.update_of_ne hj]
  refine ⟨σ10, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 a4)))))))), ?_, ?_, ?_, ?_, vS10, ?_, ?_, ?_, st10, sh10, ce10, ?_⟩
  · rw [k10 dM0 (by decide), m0]
  · rw [k10 dM1 (by decide), m1]
  · rw [k10 dM2 (by decide), m2]
  · rw [k10 dM3 (by decide), m3]
  · rw [k10 dK (by decide), k6 dK (by decide), k5 dK (by decide), k4 dK (by decide), k3 dK (by decide), h2]; simp
  · rw [k10 dT (by decide), t6]
  · intro r a b c d e f
    rw [k10 r e, k6a r a b c d f]
  · unfold countsCost
    have f2 : σ7.val dM1 = cy.getD 1 0 := by rw [k7 dM1 (by decide), m1]
    have f3 : σ8.val dM2 = cy.getD 2 0 := by rw [k8 dM2 (by decide), k7 dM2 (by decide), m2]
    have f4 : σ9.val dM3 = cy.getD 3 0 := by rw [k9 dM3 (by decide), k8 dM3 (by decide), k7 dM3 (by decide), m3]
    have g0 := hg 0; have g1 := hg 1; have g2 := hg 2; have g3 := hg 3
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
