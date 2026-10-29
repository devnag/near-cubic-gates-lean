import SourceAdapters.RAMACSP.GenItemsSort
import SourceAdapters.RAMACSP.GenParams
import SourceAdapters.RAMACSP.ConstraintEmit

/-!
# The state of the item printer and the items of the TIME catalog

Paper: `lem:generator` and "Placement" in `app:affine-embedding`.
The item printer visits each fixed template and every active bit index,
using the explicit catalog range of that template.

`Base V r s`: the numbers of the request (`PV`), the layout masks used by the guards and the reads (`k + ℓ`, the fixed
guard coordinates, `η_5 ⊕ η_1`, `areaMask ⊕ η_6`), the coordinate array, and room in the run constants. Under `Base`,
`den_itemT`: the printer `itemT q` of the time equation `q` prints exactly the numbers of its item of
`machineItems` (bit index `tBit q` in `vJ`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.RAMACSP.RamCodeWord
open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

variable {G : Glob} (V : Verifier)

/-! ## `τ < w` for every clock -/

theorem tau_lt_wordW_all (t : ℕ) : tau V t < wordW V t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hc : 64 ≤ clockConst V := (consts_le V).1
    show Nat.clog 2 (clockConst V * (0 + wordWidth (clockConst V) 0)) < wordWidth (clockConst V) 0
    unfold wordWidth
    rw [Nat.clog_zero_right, zero_add, zero_add]
    set e := Nat.clog 2 (clockConst V)
    have h1 : clockConst V ≤ 2 ^ e := Nat.le_pow_clog (by norm_num) _
    have h6 : 6 ≤ e := by
      by_contra hlt
      have : 2 ^ e ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : clockConst V * 2 ^ e ≤ 2 ^ (2 * e) := by
      rw [two_mul, pow_add]; exact Nat.mul_le_mul_right _ h1
    have h3 : Nat.clog 2 (clockConst V * 2 ^ e) ≤ 2 * e := Nat.clog_le_of_le_pow h2
    have h4 : e - 2 < 2 ^ (e - 2) := Nat.lt_two_pow_self
    have h5 : 2 ^ e = 4 * 2 ^ (e - 2) := by
      rw [show e = (e - 2) + 2 from by omega, pow_add]; simp; ring
    omega
  · exact tau_lt_wordW V t ht

/-! ## Program variables of the item printer -/

/-- `η_5 ⊕ η_1` (48), `areaMask ⊕ η_6` (49), the outer loop index (50), the lane-carry index (51), the coordinate
array (52), the coordinate row index (53), the squaring index (54). -/
def vP5 : Var := 48
def vP6 : Var := 49
def vI : Var := 50
def vT : Var := 51
def vD : Var := 52
def vR : Var := 53
def vS : Var := 54

/-- The run room: the constants of the code terms, the masks of `H` and of the field, the coordinate array, and the
loop counts. -/
structure Room (r : ClockRequest) (G : Glob) : Prop where
  cap : cB V + 2 ^ (domExp V r.2 + 8) ≤ G.cap
  kn : G.K ≤ G.N
  mN : domExp V r.2 + 4 * wordW V r.2 ≤ G.N
  mK : domExp V r.2 + 8 ≤ G.K
  capF : 2 ^ (fieldExp V r.2 + 8) ≤ G.cap
  fK : fieldExp V r.2 + 8 ≤ G.K
  dK : domExp V r.2 * domExp V r.2 * fieldExp V r.2 + 8 ≤ G.K

/-- **The state of the item printer** at the request `r`. -/
structure Base (r : ClockRequest) (s : FS) : Prop where
  pv : PV V r s
  kl : s.env vKL = laneExp V r.2 + stageExp V r.2
  uk : s.env vUK = upperKnown (ownLayout V r.2)
  p5 : s.env vP5 = Routing.eta (ownLayout V r.2) 5 ^^^ Routing.eta (ownLayout V r.2) 1
  p6 : s.env vP6 = Routing.areaMask (ownLayout V r.2) ^^^ Routing.eta (ownLayout V r.2) 6

/-- The variables `Base` reads. -/
def baseA (x : Var) : Prop := (20 ≤ x.val ∧ x.val ≤ 36) ∨ x = vKL ∨ x = vUK ∨ x = vP5 ∨ x = vP6 ∨ x = vD

theorem baseA_ge (x : Var) (h : baseA x) : 20 ≤ x.val := by
  rcases h with h | h | h | h | h | h
  · exact h.1
  all_goals (subst h; decide)

theorem layA_baseA (x : Var) (h : layA x) : baseA x := by
  rcases h with h | h | h | h | h | h | h
  all_goals (subst h; first | (left; decide) | simp [baseA])

theorem Base.agree {r : ClockRequest} {s t : FS} (h : Base V r s) (ha : Agree baseA s t) : Base V r t :=
  ⟨h.pv.keep V (fun i h1 h2 => ha.1 i (Or.inl ⟨h1, h2⟩)), (ha.1 _ (by simp [baseA])).trans h.kl,
    (ha.1 _ (by simp [baseA])).trans h.uk, (ha.1 _ (by simp [baseA])).trans h.p5, (ha.1 _ (by simp [baseA])).trans h.p6⟩

theorem Base.setv {r : ClockRequest} {s : FS} (h : Base V r s) (i : Var) (hi : ¬ baseA i) (v : ℕ) :
    Base V r (s.setv i v) :=
  h.agree V ⟨fun x hx => by
    have : x ≠ i := fun e => hi (e ▸ hx)
    simp [Function.update_of_ne this], rfl, rfl⟩

theorem Base.lay {r : ClockRequest} {s : FS} (h : Base V r s) : LayV (ownLayout V r.2) (wordExp V r.2) (tagExp V) s :=
  ⟨h.pv.om, h.pv.k, h.pv.ell, h.pv.q, h.pv.mH, h.kl, h.uk, rfl⟩

/-! ## The machine's parameters -/

theorem log_wordW (t : ℕ) : Nat.log 2 (wordW V t) = wordExp V t := by
  rw [wordW_eq]; exact Nat.log_pow (by norm_num) _

theorem ownRam_w (r : ClockRequest) : (ownRam V r).w = wordW V r.2 := rfl

theorem dims_own (r : ClockRequest) :
    dims (ownRam V r) (tau V r.2) = ⟨wordW V r.2, regCount V, codeLen V, tau V r.2, tau V r.2 - wordExp V r.2⟩ := by
  have e1 : Nat.log 2 (wordWidth (clockConst V) r.2) = wordExp V r.2 := log_wordW V r.2
  simp only [dims, e1]
  congr 1
  exact mnCode_length V _ _ _ _

theorem cellT_ok_gen (W K L τ β om dt : ℕ) (hw : W = 2 ^ om) (hτ : τ < W) (hβ : β ≤ τ)
    (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt) (v : TVar) (hv : v.Active ⟨W, K, L, τ, β⟩) : (cellT K L v).Ok om dt := by
  cases v with
  | inl s => exact tCell_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hβ hF s hv
  | inr s => exact recCell_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hβ hF s hv

/-- Cells of active slots are catalog cells. -/
theorem cellT_ok (r : ClockRequest) (v : TVar) (hv : v.Active (dims (ownRam V r) (tau V r.2))) :
    (cellT (regCount V) (codeLen V) v).Ok (wordExp V r.2) (tagExp V) := by
  have hF : 32 + 3 * regCount V + 2 * codeLen V ≤ 2 ^ tagExp V := by
    have := ftags_le V; unfold ftags at this; exact this
  rw [dims_own V r] at hv
  exact cellT_ok_gen _ _ _ _ _ _ _ (wordW_eq V r.2) (tau_lt_wordW_all V r.2) (Nat.sub_le _ _) hF v hv

theorem tHost_ok_gen (W K L τ β om dt : ℕ) (hw : W = 2 ^ om) (hτ : τ < W) (hβ : β ≤ τ)
    (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt) (q : TEq) (hq : q.Active ⟨W, K, L, τ, β⟩) :
    (⟨tTag K L q, tBit q, 2, 1⟩ : Cell).Ok om dt :=
  tHost_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hβ hF q hq

theorem ftags_bound : 32 + 3 * regCount V + 2 * codeLen V ≤ 2 ^ tagExp V := by
  have := ftags_le V; unfold ftags at this; exact this

/-! ## Items of the TIME catalog -/

/-- The host of a time equation (bit index in `vJ`). -/
def hostT (q : TEq) : SC := ⟨tTag (regCount V) (codeLen V) q, jE, 2, 1⟩

/-- The printer of the item of the time equation `q`: guard TIME (`lane bit τ = 0`, the lane mask `2^τ` in 28),
host stage `0`, the template's tokens. -/
def itemT (q : TEq) : P :=
  itemP (knE (.v 28)) (vaE (hostT V q) k0 k0) (tokP (hostT V q) (tmplT V (regCount V) (codeLen V) q))

/-- The item of the time equation `q` in `machineItems`. -/
def tItem {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (q : TEq) :
    Routing.Pattern (ownLayout V r.2).m × Routing.Expr F :=
  (guardAt (ownLayout V r.2) (wordExp V r.2) (2 ^ tau V r.2) 0 0 ⟨tTag (regCount V) (codeLen V) q, tBit q, 2, 1⟩,
    toRouting (tRead (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V)
      ⟨tTag (regCount V) (codeLen V) q, tBit q, 2, 1⟩) (timeEq (ownRam V r) RAMTrace.mnKind (tau V r.2) q))

theorem pow_dom (r : ClockRequest) : 2 ^ (ownLayout V r.2).m ≤ 2 ^ (domExp V r.2 + 8) :=
  Nat.pow_le_pow_right (by norm_num) (by rw [ownLayout_m]; omega)

/-- **The time items**: under `Base`, with bit index `tBit q`, `itemT q` prints the numbers of the item of `q`. -/
theorem den_itemT {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (q : TEq)
    (hq : q.Active (dims (ownRam V r) (tau V r.2))) (hj : s.env vJ = tBit q) :
    den G s (itemT V q) = itemNums mk (tItem V r q) := by
  have hl := hb.lay
  have hpd := pow_dom V r
  have hcap : 2 ^ (ownLayout V r.2).m + 8 ≤ G.cap := by
    have := hR.cap; have : 1 ≤ 2 ^ (domExp V r.2 + 8) := Nat.one_le_two_pow
    have := Nat.two_pow_pos (domExp V r.2 + 8)
    have h8 : 8 ≤ 2 ^ (domExp V r.2 + 8) := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (show 3 ≤ domExp V r.2 + 8 by omega) : 2 ^ 3 ≤ _)
    have := cB_16 V
    omega
  have hmN : (ownLayout V r.2).m ≤ G.N := by rw [ownLayout_m]; have := hR.mN; omega
  have hτ := tau_lt_wordW_all V r.2
  have hT : evalE G s (.v 28) = 2 ^ tau V r.2 := hb.pv.T
  have hTk : 2 ^ tau V r.2 < 2 ^ (ownLayout V r.2).k := Nat.pow_lt_pow_right (by norm_num) (by
    show tau V r.2 < laneExp V r.2; unfold laneExp; omega)
  have h0k : 0 < 2 ^ (ownLayout V r.2).k := Nat.two_pow_pos _
  have h0l : 0 < 2 ^ (ownLayout V r.2).ell := Nat.two_pow_pos _
  have hd := dims_own V r
  have hq' := hq
  rw [hd] at hq'
  have hhost : ((hostT V q).ev G s) = ⟨tTag (regCount V) (codeLen V) q, tBit q, 2, 1⟩ := by
    simp only [hostT, SC.ev, jE, evalE, hj]
  have hhok : ((hostT V q).ev G s).Ok (wordExp V r.2) (tagExp V) := by
    rw [hhost]
    exact tHost_ok_gen _ _ _ _ _ _ _ (wordW_eq V r.2) hτ (Nat.sub_le _ _) (ftags_bound V) q hq'
  have htv : TimeV V (G := G) (w := wordWidth (clockConst V) r.2) (n := r.1.1) (t := r.2)
      (T := 2 ^ timeExp (clockConst V) r.2) (tau V r.2) (tBit q) s :=
    ⟨⟨hj, hb.pv.n, hb.pv.t, hb.pv.T, hb.pv.w, le_trans (Nat.le_add_right _ _) hR.cap⟩, hb.pv.ta,
      hb.pv.om.trans (log_wordW V r.2).symm⟩
  have hev := tmplT_ok V (regCount V) (codeLen V) (codeLen_le_two_pow_wordW V r.2) (tau V r.2) q hq htv
  have hx : ∀ c ∈ (SX.ev G s (tmplT V (regCount V) (codeLen V) q)).vars, c.Ok (wordExp V r.2) (tagExp V) := by
    rw [hev, vars_xmap]
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact cellT_ok V r v (timeEq_reads_active _ _ _ (by
      show 1 ≤ wordW V r.2; rw [wordW_eq]; exact Nat.one_le_two_pow) q hq v hv)
  rw [itemT, den_item mk hm0 hm1 hl hcap hmN (hostT V q) _ (.v 28) k0 k0 (2 ^ tau V r.2) 0 0 hT (Nat.zero_min _)
    (Nat.zero_min _) hTk h0k h0l hhok hx (by simp [RdE, knE, notA, vA, vUK]) (by
      simp [RdE, vaE, colE, notA, vA, hostT, jE, vJ, k0]), hev, ← toRouting_xmap, hhost]
  unfold tItem
  congr 3
  funext v
  exact (tRead_eq' _ _ _ _ _ v).symm

end NearCubicGates.Adapters.RAMACSP.Gen.Items
