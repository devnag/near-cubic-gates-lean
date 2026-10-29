import SourceAdapters.Refuter.RMachBase
import Proof.Gates.WordPrograms.BinW

/-!
# Emitting words for R (input 7, R: the query words and the output record)

Paper anchor: proof of `lem:multitape-refuter` (R writes each query in full), (R outputs the record `x_p`),
proof of `cor:framed-refuter` (`x_i = 1^M 0 1^{N−M−2−g} 0 w_i`, `w_i` the `i`-th `g`-bit string, first bit most significant),
 (the interval endpoint is written in binary).

Everything R writes is appended at the end of a target stream `D` whose head sits at its end, with a
counter register `R` (used later to rewind `D`): `app σ D R w`. An *act* (`IsAct`) appends `f b` for a bit
`b`. Bits come from

* a unary stream (`forU_act`: `1^a` gives `f true` `a` times),
* a framed word (`forP`: the data bits of `fpre l ++ rest`, in order),
* a stored number `frame (binary (g+2) v)` (`msb_spec`: its low `g` bits, most significant first, i.e. the
  witness `unrank g v`; `halve_spec`: its canonical bits `v.bits`, by repeated halving).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Appending at a stream's end -/

/-- Append `w` at the end of `D` (head at the end); counter `R` advances by `|w|`. -/
def app (σ : WState ns nr) (D : Fin (ns + 1)) (R : Fin nr) (w : List Bool) : WState ns nr :=
  ((σ.sets D (σ.st D ++ w)).seth D (σ.sh D + w.length)).setv R (σ.val R + w.length)

section App
variable (σ : WState ns nr) (D : Fin (ns + 1)) (R : Fin nr)

@[simp] theorem app_st_D (w : List Bool) : (app σ D R w).st D = σ.st D ++ w := by simp [app]
@[simp] theorem app_sh_D (w : List Bool) : (app σ D R w).sh D = σ.sh D + w.length := by simp [app]
@[simp] theorem app_val_R (w : List Bool) : (app σ D R w).val R = σ.val R + w.length := by simp [app]
theorem app_st_ne (w : List Bool) (i : Fin (ns + 1)) (h : i ≠ D) : (app σ D R w).st i = σ.st i := by
  simp [app, Function.update_of_ne h]
theorem app_sh_ne (w : List Bool) (i : Fin (ns + 1)) (h : i ≠ D) : (app σ D R w).sh i = σ.sh i := by
  simp [app, Function.update_of_ne h]
theorem app_val_ne (w : List Bool) (r : Fin nr) (h : r ≠ R) : (app σ D R w).val r = σ.val r := by
  simp [app, Function.update_of_ne h]
@[simp] theorem app_cell (w : List Bool) : (app σ D R w).cell = σ.cell := rfl

theorem app_app (w1 w2 : List Bool) : app (app σ D R w1) D R w2 = app σ D R (w1 ++ w2) := by
  unfold app; wst

@[simp] theorem app_nil : app σ D R [] = σ := by unfold app; wst

theorem app_mv (U : Fin (ns + 1)) (R' : Fin nr) (hU : U ≠ D) (hR : R' ≠ R) (k : ℕ) (w : List Bool) :
    app (mv σ U R' k) D R w = mv (app σ D R w) U R' k := by
  unfold app mv; wst

theorem app_end (w : List Bool) (h : σ.sh D = (σ.st D).length) :
    (app σ D R w).sh D = ((app σ D R w).st D).length := by simp [h]

end App

/-- `act` appends `f b` to `D` (counter `R`) within `c` steps, from any state with `D`'s head at its end. -/
def IsAct (act : Bool → WMX ns nr) (D : Fin (ns + 1)) (R : Fin nr) (f : Bool → List Bool) (c : ℕ) : Prop :=
  ∀ b (τ : WState ns nr), τ.sh D = (τ.st D).length → τ.val R + (f b).length ≤ cap →
    WXExec cap (act b) τ (app τ D R (f b)) c

/-- One framed bit `1 b`, counted twice. -/
def em1 (D : Fin (ns + 1)) (R : Fin nr) (b : Bool) : WMX ns nr :=
  .seq (pairA D b) (.seq (WMX.inc R) (WMX.inc R))

theorem em1_act (D : Fin (ns + 1)) (R : Fin nr) : IsAct cap (em1 D R) D R (fun b => [true, b]) 15 := by
  intro b τ hD hc
  have e1 := pairA_spec cap D b τ hD
  have e2 := WXExec.inc cap R ((τ.sets D (τ.st D ++ [true, b])).seth D (τ.sh D + 2)) (by simp at hc ⊢; omega)
  have e3 := WXExec.inc cap R (((τ.sets D (τ.st D ++ [true, b])).seth D (τ.sh D + 2)).setv R
    (((τ.sets D (τ.st D ++ [true, b])).seth D (τ.sh D + 2)).val R + 1)) (by simp at hc ⊢; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  unfold app; wst

/-- A framed bit of a framed bit: `1 1 1 b` (a bit of a framed word, written inside an outer frame). -/
def em2 (D : Fin (ns + 1)) (R : Fin nr) (b : Bool) : WMX ns nr := .seq (em1 D R true) (em1 D R b)

theorem em2_act (D : Fin (ns + 1)) (R : Fin nr) :
    IsAct cap (em2 D R) D R (fun b => [true, true, true, b]) 31 := by
  intro b τ hD hc
  have e1 := em1_act cap D R true τ hD (by simp at hc ⊢; omega)
  have e2 := em1_act cap D R b (app τ D R [true, true]) (app_end τ D R _ hD) (by simp at hc ⊢; omega)
  refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
  rw [app_app]; rfl

/-! ## Acts over a unary stream -/

theorem forU_act {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (b : Bool) (U : Fin (ns + 1)) (R : Fin nr) (hUD : U ≠ D) (hR : R ≠ RD)
    (σ : WState ns nr) (a : ℕ) (hU : σ.st U = List.replicate a true) (hUh : σ.sh U = 0) (hR0 : σ.val R = 0)
    (hD : σ.sh D = (σ.st D).length) (hc : σ.val RD + a * (f b).length ≤ cap) (ha : a ≤ cap) :
    WXExec cap (forU U R (act b)) σ (app σ D RD ((List.replicate a b).flatMap f)) (a * (c + 13) + 3) := by
  have h := forU_spec cap U R (act b) a c (fun k => app σ D RD ((List.replicate k b).flatMap f))
    (fun k _ => by rw [app_st_ne _ _ _ _ _ hUD, hU]) (fun k _ => by rw [app_sh_ne _ _ _ _ _ hUD, hUh])
    (fun k _ => by rw [app_val_ne _ _ _ _ _ hR, hR0])
    (fun k hk => by
      have e := hact b (mv (app σ D RD ((List.replicate k b).flatMap f)) U R k)
        (by simp [mv, Function.update_of_ne hUD.symm, hD])
        (by
          simp only [mv, WState.setv_val, WState.seth_val, Function.update_of_ne hR.symm, app_val_R,
            List.length_flatMap, List.map_replicate, List.sum_replicate, smul_eq_mul]
          nlinarith)
      rw [app_mv _ _ _ _ _ hUD hR, app_app] at e
      rw [List.replicate_succ', List.flatMap_append, List.flatMap_singleton]
      exact e)
    ha
  simpa using h

/-! ## Acts over the data bits of a framed word -/

/-- Walk the pairs `1 b` of `X`: `inner` runs with the head on each data bit; `X` is rewound by `R`. -/
def forP (X : Fin (ns + 1)) (R : Fin nr) (inner : WMX ns nr) : WMX ns nr :=
  .seq (.whs X (.seq (WMX.fwd X) (.seq inner (.seq (WMX.fwd X) (.seq (WMX.inc R) (WMX.inc R)))))) (rew X R)

/-- `σ` with stream `X` at `h` and register `R = v`. -/
def mv2 (σ : WState ns nr) (X : Fin (ns + 1)) (R : Fin nr) (h v : ℕ) : WState ns nr := (σ.seth X h).setv R v

/-- The framed bits of `l` without the terminator: `1 b_1 1 b_2 ⋯`. -/
def fpre (l : List Bool) : List Bool := l.flatMap fun b => [true, b]

@[simp] theorem fpre_length (l : List Bool) : (fpre l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [fpre, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢; omega

theorem rd_fpre (l rest : List Bool) (k : ℕ) (hk : k < l.length) :
    readTapeBit (fpre l ++ rest) (2 * k) = true ∧ readTapeBit (fpre l ++ rest) (2 * k + 1) = l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b l ih =>
    cases k with
    | zero => simp [fpre, readTapeBit]
    | succ k =>
      have := ih k (by simp at hk; omega)
      simp only [fpre, List.flatMap_cons, List.cons_append, List.nil_append] at this ⊢
      simpa [readTapeBit, show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
        using this

theorem rd_fpre_end (l rest : List Bool) (k : ℕ) :
    readTapeBit (fpre l ++ rest) (2 * l.length + k) = readTapeBit rest k := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem forP_spec (X : Fin (ns + 1)) (R : Fin nr) (inner : WMX ns nr) (l rest : List Bool) (c : ℕ)
    (st : ℕ → WState ns nr) (hX : ∀ k ≤ l.length, (st k).st X = fpre l ++ rest)
    (hXh : ∀ k ≤ l.length, (st k).sh X = 0) (hR : ∀ k ≤ l.length, (st k).val R = 0)
    (hrest : readTapeBit rest 0 = false)
    (hin : ∀ k < l.length, WXExec cap inner (mv2 (st k) X R (2 * k + 1) (2 * k))
      (mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)) c) (hcap : 2 * l.length ≤ cap) :
    WXExec cap (forP X R inner) (st 0) (st l.length) (l.length * (c + 24) + 3) := by
  have e0 : mv2 (st 0) X R 0 0 = st 0 := by
    have h1 := hXh 0 (Nat.zero_le _); have h2 := hR 0 (Nat.zero_le _)
    unfold mv2; wst
  have hloop := loopS cap (i := X)
    (body := .seq (WMX.fwd X) (.seq inner (.seq (WMX.fwd X) (.seq (WMX.inc R) (WMX.inc R)))))
    (fun k => mv2 (st k) X R (2 * k) (2 * k)) l.length (c + 12)
    (fun k hk => by
      simp only [wbit, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hX k hk.le]
      exact (rd_fpre l rest k hk).1)
    (by
      simp only [wbit, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hX _ le_rfl]
      have := rd_fpre_end l rest 0
      simpa using this.trans hrest)
    (fun k hk => by
      have e1 := WXExec.fwd cap X (mv2 (st k) X R (2 * k) (2 * k))
      have e1' : (mv2 (st k) X R (2 * k) (2 * k)).seth X ((mv2 (st k) X R (2 * k) (2 * k)).sh X + 1) =
          mv2 (st k) X R (2 * k + 1) (2 * k) := by unfold mv2; wst
      rw [e1'] at e1
      have e2 := hin k hk
      have e3 := WXExec.fwd cap X (mv2 (st (k + 1)) X R (2 * k + 1) (2 * k))
      have e4 := WXExec.inc cap R ((mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)).seth X
        ((mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)).sh X + 1)) (by simp [mv2]; omega)
      have e5 := WXExec.inc cap R ((((mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)).seth X
        ((mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)).sh X + 1))).setv R
        ((((mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)).seth X
        ((mv2 (st (k + 1)) X R (2 * k + 1) (2 * k)).sh X + 1))).val R + 1)) (by simp [mv2]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ (by omega)
      unfold mv2; wst)
  rw [e0] at hloop
  have e6 := rew_spec cap X R (mv2 (st l.length) X R (2 * l.length) (2 * l.length)) (2 * l.length)
    (by simp [mv2]) hcap
  refine (WXExec.seq hloop e6).cast cap ?_ (by nlinarith)
  have h1 := hXh _ le_rfl; have h2 := hR _ le_rfl
  unfold mv2; wst

theorem forP_act {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (X : Fin (ns + 1)) (R : Fin nr) (hXD : X ≠ D) (hR : R ≠ RD)
    (σ : WState ns nr) (l rest : List Bool) (hX : σ.st X = fpre l ++ rest) (hXh : σ.sh X = 0) (hR0 : σ.val R = 0)
    (hrest : readTapeBit rest 0 = false) (hD : σ.sh D = (σ.st D).length)
    (hfl : ∀ b, (f b).length ≤ 4) (hc : σ.val RD + 4 * l.length ≤ cap) (hcap : 2 * l.length ≤ cap) :
    WXExec cap (forP X R (.ifs X (act true) (act false))) σ (app σ D RD (l.flatMap f))
      (l.length * (c + 25) + 3) := by
  have h := forP_spec cap X R (.ifs X (act true) (act false)) l rest (c + 1)
    (fun k => app σ D RD ((l.take k).flatMap f))
    (fun k _ => by rw [app_st_ne _ _ _ _ _ hXD, hX]) (fun k _ => by rw [app_sh_ne _ _ _ _ _ hXD, hXh])
    (fun k _ => by rw [app_val_ne _ _ _ _ _ hR, hR0]) hrest
    (fun k hk => by
      have hbit : wbit (mv2 (app σ D RD ((l.take k).flatMap f)) X R (2 * k + 1) (2 * k)) X = l[k] := by
        simp only [wbit, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
          app_st_ne _ _ _ _ _ hXD, hX]
        exact (rd_fpre l rest k hk).2
      have htake : (l.take (k + 1)).flatMap f = (l.take k).flatMap f ++ f l[k] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append,
          List.flatMap_singleton]
      have hlen : ((l.take k).flatMap f).length ≤ 4 * k := by
        rw [List.length_flatMap]
        calc ((l.take k).map (fun b => (f b).length)).sum ≤ ((l.take k).map (fun _ => 4)).sum :=
              List.sum_le_sum (fun b _ => hfl b)
          _ = 4 * (l.take k).length := by simp [List.sum_replicate, mul_comm]
          _ ≤ 4 * k := by simp
      have hpre : (mv2 (app σ D RD ((l.take k).flatMap f)) X R (2 * k + 1) (2 * k)).sh D =
          ((mv2 (app σ D RD ((l.take k).flatMap f)) X R (2 * k + 1) (2 * k)).st D).length := by
        simp [mv2, Function.update_of_ne hXD.symm, hD]
      have hcv : (mv2 (app σ D RD ((l.take k).flatMap f)) X R (2 * k + 1) (2 * k)).val RD + (f l[k]).length ≤
          cap := by
        simp only [mv2, WState.setv_val, WState.seth_val, Function.update_of_ne hR.symm, app_val_R]
        have := hfl l[k]; nlinarith
      have e := hact l[k] _ hpre hcv
      have e' : WXExec cap (.ifs X (act true) (act false))
          (mv2 (app σ D RD ((l.take k).flatMap f)) X R (2 * k + 1) (2 * k))
          (app (mv2 (app σ D RD ((l.take k).flatMap f)) X R (2 * k + 1) (2 * k)) D RD (f l[k])) (c + 1) := by
        cases hb : l[k]
        · rw [hb] at hbit e; exact WXExec.ifsF hbit e
        · rw [hb] at hbit e; exact WXExec.ifsT hbit e
      refine e'.cast cap ?_ le_rfl
      rw [htake]; unfold mv2 app; wst)
    hcap
  simpa using h

/-! ## Reading stored numbers -/

theorem binary_getElem (W v j : ℕ) (hj : j < W) : (binary W v)[j]'(by simpa using hj) = v.testBit j := by
  induction W generalizing v j with
  | zero => omega
  | succ W ih =>
    cases j with
    | zero =>
      simp only [binary, List.getElem_cons_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    | succ j =>
      simp only [binary, List.getElem_cons_succ]
      rw [ih (v / 2) j (by omega), Nat.testBit_div_two]

theorem frame_eq_fpre (l : List Bool) : RepairOrdinary.frame l = fpre l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, fpre, ih]

theorem rd_num (W v j : ℕ) (hj : j < W) :
    readTapeBit (RepairOrdinary.frame (binary W v)) (2 * j) = true ∧
      readTapeBit (RepairOrdinary.frame (binary W v)) (2 * j + 1) = v.testBit j := by
  rw [frame_eq_fpre]
  have := rd_fpre (binary W v) [false] j (by simpa using hj)
  rw [binary_getElem W v j hj] at this
  exact this

theorem rd_num_end (W v : ℕ) : readTapeBit (RepairOrdinary.frame (binary W v)) (2 * W) = false := by
  rw [frame_eq_fpre]
  have := rd_fpre_end (binary W v) [false] 0
  rw [binary_length, Nat.add_zero] at this
  rw [this]; rfl

/-! ## The witness bits of a stored number, most significant first -/

/-- Emit the low `g` bits of `X = frame (binary (g+2) v)` most significant first (`R1` scratch). -/
def msb (X : Fin (ns + 1)) (R1 : Fin nr) (act : Bool → WMX ns nr) : WMX ns nr :=
  .seq (.whs X (.seq (WMX.fwd X) (.seq (WMX.fwd X) (WMX.inc R1))))
    (.seq (WMX.dec R1) (.seq (WMX.dec R1) (.seq (WMX.bwd X) (.seq (WMX.bwd X) (.seq (WMX.bwd X)
      (.seq (WMX.bwd X) (.seq (WMX.bwd X)
        (.whr R1 (.seq (.ifs X (act true) (act false)) (.seq (WMX.bwd X) (.seq (WMX.bwd X) (WMX.dec R1))))))))))))

/-- The `g`-bit witness of rank `v`, as a list. -/
def wbits (g v : ℕ) : List Bool := List.ofFn fun j : Fin g => v.testBit (g - 1 - j.val)

theorem wbits_take_succ (g v i : ℕ) (hi : i < g) :
    (wbits g v).take (i + 1) = (wbits g v).take i ++ [v.testBit (g - 1 - i)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [wbits]; omega)]
  simp [wbits]

theorem msb_spec {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (X : Fin (ns + 1)) (R1 : Fin nr) (hXD : X ≠ D) (hR : R1 ≠ RD)
    (σ : WState ns nr) (g v : ℕ) (hX : σ.st X = RepairOrdinary.frame (binary (g + 2) v)) (hXh : σ.sh X = 0)
    (hR0 : σ.val R1 = 0) (hD : σ.sh D = (σ.st D).length) (hfl : ∀ b, (f b).length ≤ 4)
    (hc : σ.val RD + 4 * g ≤ cap) (hcap : 2 * g + 6 ≤ cap) :
    WXExec cap (msb X R1 act) σ (app σ D RD ((wbits g v).flatMap f)) ((g + 3) * (c + 20) + 20) := by
  -- walk to the terminator
  have l1 := loopS cap (i := X) (body := .seq (WMX.fwd X) (.seq (WMX.fwd X) (WMX.inc R1)))
    (fun k => (σ.seth X (2 * k)).setv R1 k) (g + 2) 7
    (fun k hk => by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hX]
      exact (rd_num _ v k hk).1)
    (by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hX]
      exact rd_num_end _ v)
    (fun k hk => by
      have e1 := WXExec.fwd cap X ((σ.seth X (2 * k)).setv R1 k)
      have e2 := WXExec.fwd cap X (((σ.seth X (2 * k)).setv R1 k).seth X
        (((σ.seth X (2 * k)).setv R1 k).sh X + 1))
      have e3 := WXExec.inc cap R1 ((((σ.seth X (2 * k)).setv R1 k).seth X
        (((σ.seth X (2 * k)).setv R1 k).sh X + 1)).seth X ((((σ.seth X (2 * k)).setv R1 k).seth X
        (((σ.seth X (2 * k)).setv R1 k).sh X + 1)).sh X + 1)) (by simp; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
      wst)
  have s0 : (σ.seth X (2 * 0)).setv R1 0 = σ := by wst
  rw [s0] at l1
  -- back to the data cell of bit `g - 1`
  let τ0 := (σ.seth X (2 * (g + 2))).setv R1 (g + 2)
  have d1 := WXExec.dec cap R1 τ0 (by simp [τ0]; omega)
  have d2 := WXExec.dec cap R1 (τ0.setv R1 (τ0.val R1 - 1)) (by simp [τ0]; omega)
  set τ1 := (τ0.setv R1 (τ0.val R1 - 1)).setv R1 ((τ0.setv R1 (τ0.val R1 - 1)).val R1 - 1) with hτ1
  have b1 := WXExec.bwd cap X τ1
  have b2 := WXExec.bwd cap X (τ1.seth X (τ1.sh X - 1))
  have b3 := WXExec.bwd cap X ((τ1.seth X (τ1.sh X - 1)).seth X ((τ1.seth X (τ1.sh X - 1)).sh X - 1))
  set τ2 := ((τ1.seth X (τ1.sh X - 1)).seth X ((τ1.seth X (τ1.sh X - 1)).sh X - 1)).seth X
    (((τ1.seth X (τ1.sh X - 1)).seth X ((τ1.seth X (τ1.sh X - 1)).sh X - 1)).sh X - 1) with hτ2
  have b4 := WXExec.bwd cap X τ2
  have b5 := WXExec.bwd cap X (τ2.seth X (τ2.sh X - 1))
  -- the emitting loop
  let st : ℕ → WState ns nr := fun i =>
    ((app σ D RD (((wbits g v).take i).flatMap f)).seth X (2 * g + 3 - 2 * i - 4)).setv R1 (g - i)
  have hmid : (τ2.seth X (τ2.sh X - 1)).seth X ((τ2.seth X (τ2.sh X - 1)).sh X - 1) = st 0 := by
    simp only [st, hτ2, hτ1, τ0, List.take_zero, List.flatMap_nil, app_nil]
    wst
  rw [hmid] at b5
  have l2 := loopR cap (r := R1) (body := .seq (.ifs X (act true) (act false)) (.seq (WMX.bwd X)
      (.seq (WMX.bwd X) (WMX.dec R1)))) st g (c + 7)
    (fun i hi => by simp [st, Function.update_apply]; omega)
    (by simp [st])
    (fun i hi => by
      have hbit : wbit (st i) X = v.testBit (g - 1 - i) := by
        simp only [wbit, st, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
          app_st_ne _ _ _ _ _ hXD, hX]
        have := (rd_num (g + 2) v (g - 1 - i) (by omega)).2
        rwa [show 2 * (g - 1 - i) + 1 = 2 * g + 3 - 2 * i - 4 by omega] at this
      have hlen : (((wbits g v).take i).flatMap f).length ≤ 4 * i := by
        rw [List.length_flatMap]
        calc (((wbits g v).take i).map (fun b => (f b).length)).sum ≤
              (((wbits g v).take i).map (fun _ => 4)).sum := List.sum_le_sum (fun b _ => hfl b)
          _ = 4 * ((wbits g v).take i).length := by simp [List.sum_replicate, mul_comm]
          _ ≤ 4 * i := by simp
      have hpre : (st i).sh D = ((st i).st D).length := by
        simp [st, Function.update_of_ne hXD.symm, hD]
      have hcv : (st i).val RD + (f (v.testBit (g - 1 - i))).length ≤ cap := by
        simp only [st, WState.setv_val, WState.seth_val, Function.update_of_ne hR.symm, app_val_R]
        have := hfl (v.testBit (g - 1 - i)); nlinarith
      have e := hact _ (st i) hpre hcv
      have e' : WXExec cap (.ifs X (act true) (act false)) (st i) (app (st i) D RD (f (v.testBit (g - 1 - i))))
          (c + 1) := by
        cases hb : v.testBit (g - 1 - i)
        · rw [hb] at hbit e; exact WXExec.ifsF hbit e
        · rw [hb] at hbit e; exact WXExec.ifsT hbit e
      set ρ := app (st i) D RD (f (v.testBit (g - 1 - i))) with hρ
      have e2 := WXExec.bwd cap X ρ
      have e3 := WXExec.bwd cap X (ρ.seth X (ρ.sh X - 1))
      have e4 := WXExec.dec cap R1 ((ρ.seth X (ρ.sh X - 1)).seth X ((ρ.seth X (ρ.sh X - 1)).sh X - 1))
        (by simp [ρ, st, app_val_ne _ _ _ _ _ hR]; omega)
      refine (WXExec.seq e' (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
      simp only [hρ, st]
      rw [wbits_take_succ g v i hi, List.flatMap_append, List.flatMap_singleton]
      unfold app; wst)
  have hend : st g = app σ D RD ((wbits g v).flatMap f) := by
    simp only [st, show (wbits g v).take g = wbits g v by simp [wbits]]
    have h1 : (app σ D RD ((wbits g v).flatMap f)).sh X = 0 := by rw [app_sh_ne _ _ _ _ _ hXD, hXh]
    have h2 : (app σ D RD ((wbits g v).flatMap f)).val R1 = 0 := by rw [app_val_ne _ _ _ _ _ hR, hR0]
    rw [show 2 * g + 3 - 2 * g - 4 = 0 by omega, Nat.sub_self]
    wst
  rw [hend] at l2
  refine (WXExec.seq l1 (WXExec.seq d1 (WXExec.seq d2 (WXExec.seq b1 (WXExec.seq b2 (WXExec.seq b3
    (WXExec.seq b4 (WXExec.seq b5 l2)))))))).cast cap rfl ?_
  nlinarith

/-! ## The canonical bits of a stored number, by halving -/

/-- While `X ≠ 0`: emit its low bit, halve it (`Z` holds `0`; `F`, `R` scratch). -/
def halveLoop (X Z : Fin (ns + 1)) (F R : Fin nr) (act : Bool → WMX ns nr) : WMX ns nr :=
  .whr F (.seq (WMX.dec F) (.seq (WMX.fwd X) (.seq (.ifs X (act true) (act false)) (.seq (WMX.bwd X)
    (.seq (BinW.half X R) (BinW.lt Z X F R))))))

/-- `F := [0 < x]`, then the halving loop. -/
def halve (X Z : Fin (ns + 1)) (F R : Fin nr) (act : Bool → WMX ns nr) : WMX ns nr :=
  .seq (BinW.lt Z X F R) (halveLoop X Z F R act)

theorem bits_cons_of_pos (x : ℕ) (hx : 0 < x) : x.bits = (x % 2 == 1) :: (x / 2).bits := by
  have hq2 : x = Nat.bit (x % 2 == 1) (x / 2) := by
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.bit, h] <;> omega
  conv_lhs => rw [hq2]
  apply Nat.bits_append_bit
  intro h0
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · omega
  · simp [h]

theorem halveLoop_spec {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (X Z : Fin (ns + 1)) (F R : Fin nr) (hXD : X ≠ D) (hZD : Z ≠ D)
    (hXZ : X ≠ Z) (hFR : F ≠ R) (hFD : F ≠ RD) (hRD : R ≠ RD) (W : ℕ) (hW : 1 ≤ W)
    (hfl : ∀ b, (f b).length ≤ 4) (hcap : 2 * W + 1 ≤ cap) (σ : WState ns nr)
    (hZ : NumOn σ Z W 0) (hXh : σ.sh X = 0) (hR0 : σ.val R = 0) (hD : σ.sh D = (σ.st D).length) :
    ∀ n x (E : List Bool), x < 2 ^ n → x < 2 ^ W → σ.val RD + E.length + 4 * n ≤ cap →
      WXExec cap (halveLoop X Z F R act)
        (((app σ D RD E).sets X (RepairOrdinary.frame (binary W x))).setv F (decide (0 < x)).toNat)
        (((app σ D RD (E ++ x.bits.flatMap f)).sets X (RepairOrdinary.frame (binary W 0))).setv F 0)
        ((n + 1) * (c + 90 * W + 20)) := by
  intro n
  induction n with
  | zero =>
    intro x E hx _ _
    have : x = 0 := by simpa using hx
    subst this
    exact (WXExec.whrF (by simp)).cast cap (by simp) (by nlinarith)
  | succ n ih =>
    intro x E hx hxW hc
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · exact (WXExec.whrF (by simp)).cast cap (by simp) (by nlinarith)
    set σ0 := ((app σ D RD E).sets X (RepairOrdinary.frame (binary W x))).setv F (decide (0 < x)).toNat
      with hσ0
    have hF1 : σ0.val F = 1 := by simp [σ0, hpos]
    have e1 := WXExec.dec cap F σ0 (by rw [hF1]; omega)
    set σ1 := σ0.setv F (σ0.val F - 1) with hσ1
    have e2 := WXExec.fwd cap X σ1
    set σ2 := σ1.seth X (σ1.sh X + 1) with hσ2
    have hb : wbit σ2 X = x.testBit 0 := by
      simp only [wbit, σ2, σ1, σ0, WState.seth_st, WState.setv_st, WState.sets_st, WState.seth_sh,
        WState.setv_sh, WState.sets_sh, Function.update_self, app_sh_ne _ _ _ _ _ hXD, hXh]
      exact (rd_num W x 0 hW).2
    have hpre : σ2.sh D = (σ2.st D).length := by
      simp [σ2, σ1, σ0, Function.update_of_ne hXD.symm, hD]
    have hcv : σ2.val RD + (f (x.testBit 0)).length ≤ cap := by
      simp only [σ2, σ1, σ0, WState.seth_val, WState.setv_val, WState.sets_val, Function.update_of_ne hFD.symm,
        app_val_R]
      have := hfl (x.testBit 0); omega
    have e3 := hact (x.testBit 0) σ2 hpre hcv
    have e3' : WXExec cap (.ifs X (act true) (act false)) σ2 (app σ2 D RD (f (x.testBit 0))) (c + 1) := by
      cases hbb : x.testBit 0
      · rw [hbb] at hb e3; exact WXExec.ifsF hb e3
      · rw [hbb] at hb e3; exact WXExec.ifsT hb e3
    set σ3 := app σ2 D RD (f (x.testBit 0)) with hσ3
    have e4 := WXExec.bwd cap X σ3
    set σ4 := σ3.seth X (σ3.sh X - 1) with hσ4
    have hn4 : NumOn σ4 X W x := by
      constructor
      · simp [σ4, σ3, σ2, σ1, σ0, app_st_ne _ _ _ _ _ hXD]
      · simp [σ4, σ3, σ2, σ1, σ0, app_sh_ne _ _ _ _ _ hXD, hXh]
    have e5 := BinW.half_spec cap W (A := X) (R := R) σ4 x hn4 (by simp [σ4, σ3, σ2, σ1, σ0, app_val_ne _ _ _ _ _ hRD,
      Function.update_of_ne hFR.symm, hR0]) hxW (by omega)
    set σ5 := σ4.sets X (RepairOrdinary.frame (binary W (x / 2))) with hσ5
    have hz5 : NumOn σ5 Z W 0 := by
      constructor
      · simp [σ5, σ4, σ3, σ2, σ1, σ0, app_st_ne _ _ _ _ _ hZD, Function.update_of_ne hXZ.symm, hZ.1]
      · simp [σ5, σ4, σ3, σ2, σ1, σ0, app_sh_ne _ _ _ _ _ hZD, Function.update_of_ne hXZ.symm, hZ.2]
    have hx5 : NumOn σ5 X W (x / 2) := by
      constructor
      · simp [σ5]
      · simp [σ5, σ4, σ3, σ2, σ1, σ0, app_sh_ne _ _ _ _ _ hXD, hXh]
    have hx2W : x / 2 < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) hxW
    have e6 := BinW.lt_spec cap W hXZ.symm hFR σ5 0 (x / 2) hz5 hx5 (by simp [σ5, σ4, σ3, σ2, σ1, σ0,
      app_val_ne _ _ _ _ _ hFD, hF1, hpos]) (by simp [σ5, σ4, σ3, σ2, σ1, σ0, app_val_ne _ _ _ _ _ hRD,
      Function.update_of_ne hFR.symm, hR0]) (by positivity) hx2W hcap
    have hx2 : x / 2 < 2 ^ n := by rw [pow_succ] at hx; omega
    have e7 := ih (x / 2) (E ++ f (x.testBit 0)) hx2 hx2W (by
      have := hfl (x.testBit 0); simp only [List.length_append]; omega)
    have hmid : σ5.setv F (decide (0 < x / 2)).toNat =
        ((app σ D RD (E ++ f (x.testBit 0))).sets X (RepairOrdinary.frame (binary W (x / 2)))).setv F
          (decide (0 < x / 2)).toNat := by
      simp only [σ5, σ4, σ3, σ2, σ1, σ0]
      unfold app; wst
    rw [← hmid] at e7
    have hbits : x.bits.flatMap f = f (x.testBit 0) ++ (x / 2).bits.flatMap f := by
      rw [bits_cons_of_pos x hpos, List.flatMap_cons]
      congr 2
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
    refine (WXExec.whrT (by rw [hF1]; omega) (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3'
      (WXExec.seq e4 (WXExec.seq e5 e6))))) e7).cast cap ?_ (by nlinarith)
    rw [hbits, ← List.append_assoc]

theorem halve_spec {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (X Z : Fin (ns + 1)) (F R : Fin nr) (hXD : X ≠ D) (hZD : Z ≠ D)
    (hXZ : X ≠ Z) (hFR : F ≠ R) (hFD : F ≠ RD) (hRD : R ≠ RD) (W : ℕ) (hW : 1 ≤ W)
    (hfl : ∀ b, (f b).length ≤ 4) (hcap : 2 * W + 1 ≤ cap) (σ : WState ns nr)
    (hZ : NumOn σ Z W 0) (hR0 : σ.val R = 0) (hF0 : σ.val F = 0) (hD : σ.sh D = (σ.st D).length)
    (x : ℕ) (hX : NumOn σ X W x) (hxW : x < 2 ^ W) (hc : σ.val RD + 4 * W ≤ cap) :
    WXExec cap (halve X Z F R act) σ
      ((app σ D RD (x.bits.flatMap f)).sets X (RepairOrdinary.frame (binary W 0)))
      ((W + 2) * (c + 90 * W + 20)) := by
  have e1 := BinW.lt_spec cap W hXZ.symm hFR σ 0 x hZ hX hF0 hR0 (by positivity) hxW hcap
  have e2 := halveLoop_spec cap hact X Z F R hXD hZD hXZ hFR hFD hRD W hW hfl hcap σ hZ hX.2 hR0 hD W x []
    hxW hxW (by simp; omega)
  have h0 : σ.setv F (decide (0 < x)).toNat =
      ((app σ D RD []).sets X (RepairOrdinary.frame (binary W x))).setv F (decide (0 < x)).toNat := by
    rw [app_nil, ← hX.1]; wst
  rw [← h0] at e2
  refine (WXExec.seq e1 e2).cast cap ?_ (by nlinarith)
  have h1 : (app σ D RD (x.bits.flatMap f)).val F = 0 := by rw [app_val_ne _ _ _ _ _ hFD, hF0]
  simp only [List.nil_append]
  wst

end NearCubicGates.Adapters.Refuter.RM
