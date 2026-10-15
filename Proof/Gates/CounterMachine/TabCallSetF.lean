import Proof.Gates.CounterMachine.TabCallLayout

/-! # RK, part 6: the printer's registers (RG's `FState`)

After the unpack: copies of a bound into several registers (`cpyL_spec`), rewinds of several streams by that bound
(`rwL_spec`), and the small register computations of RG's layout (`rc·(J+1)`, `G₀`, `2k`, `q − 1` or `j`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ} (cap : ℕ)

/-- Copy `v` into every register of a list (`t` scratch). -/
def cpyL (v t : Fin nr) : List (Fin nr) → WM ns nr
  | [] => .skip
  | d :: ds => .seq (copyR v d t) (cpyL v t ds)

theorem cpyL_spec (v t : Fin nr) (hvt : v ≠ t) : ∀ (ds : List (Fin nr)) (σ : WState ns nr), ds.Nodup →
    (∀ d ∈ ds, d ≠ v ∧ d ≠ t ∧ σ.val d = 0) → σ.val t = 0 → σ.val v ≤ cap →
    ∃ τ, WExec cap (cpyL v t ds) σ τ (ds.length * (18 * σ.val v + 4)) ∧ (∀ d ∈ ds, τ.val d = σ.val v) ∧
      (∀ r, r ∉ ds → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh
  | [], σ, _, _, _, _ => ⟨σ, by simpa [cpyL] using WExec.skip (cap := cap) σ, by simp, by simp, rfl, rfl⟩
  | d :: ds, σ, hnd, hd, ht, hc => by
    obtain ⟨hdv, hdt, hd0⟩ := hd d (by simp)
    have e1 := copyR_spec cap (v := v) (d := d) (t := t) (Ne.symm hdv) hvt (hdt) σ ht (by omega)
    rw [hd0, Nat.zero_add] at e1
    have hnd' := (List.nodup_cons.1 hnd)
    obtain ⟨τ, e2, h1, h2, h3, h4⟩ := cpyL_spec v t hvt ds (σ.setv d (σ.val v)) hnd'.2
      (fun d' hd' => by
        obtain ⟨a, b, c⟩ := hd d' (by simp [hd'])
        have hne : d' ≠ d := fun h => hnd'.1 (h ▸ hd')
        exact ⟨a, b, by simp [Function.update_of_ne hne, c]⟩)
      (by simp [Function.update_of_ne (Ne.symm hdt), ht]) (by simp [Function.update_of_ne (Ne.symm hdv)]; omega)
    have hv : (σ.setv d (σ.val v)).val v = σ.val v := by simp [Function.update_of_ne (Ne.symm hdv)]
    rw [hv] at e2 h1
    refine ⟨τ, WExec.mono (WExec.seq e1 e2) (by simp; ring_nf; omega), ?_, ?_, by rw [h3]; rfl, by rw [h4]; rfl⟩
    · intro d' hd'
      simp only [List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · rw [h2 _ hnd'.1]; simp
      · exact h1 d' hd'
    · intro r hr
      simp only [List.mem_cons, not_or] at hr
      rw [h2 r hr.2]; simp [Function.update_of_ne hr.1]

/-- Rewind every stream of a list by the bound in `v` (`u`, `t` scratch). -/
def rwL (v u t : Fin nr) : List (Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | y :: ys => .seq (.seq (copyR v u t) (WM.rewind y u)) (rwL v u t ys)

theorem rwL_spec (v u t : Fin nr) (hvu : v ≠ u) (hvt : v ≠ t) (hut : u ≠ t) :
    ∀ (ys : List (Fin (ns + 1))) (σ : WState ns nr), σ.val u = 0 → σ.val t = 0 →
    (∀ y ∈ ys, σ.sh y ≤ σ.val v) → σ.val v ≤ cap →
    ∃ τ, WExec cap (rwL v u t ys) σ τ (ys.length * (30 * σ.val v + 10)) ∧ (∀ y ∈ ys, τ.sh y = 0) ∧
      (∀ y, y ∉ ys → τ.sh y = σ.sh y) ∧ τ.st = σ.st ∧ τ.val = σ.val
  | [], σ, _, _, _, _ => ⟨σ, by simpa [rwL] using WExec.skip (cap := cap) σ, by simp, by simp, rfl, rfl⟩
  | y :: ys, σ, hu, ht, hy, hc => by
    have e1 := copyR_spec cap (v := v) (d := u) (t := t) hvu hvt hut σ ht (by omega)
    rw [hu, Nat.zero_add] at e1
    have e2 := wrewind_spec (cap := cap) y u (σ.val v) (σ.setv u (σ.val v)) (by simp) (by simp; omega)
    set σ2 := ((σ.setv u (σ.val v)).setv u 0).seth y ((σ.setv u (σ.val v)).sh y - σ.val v) with hσ2
    have hσ2' : σ2 = σ.seth y 0 := by
      apply WState.eq
      · funext j; by_cases hj : j = y
        · subst hj; simp [hσ2]; have := hy j (by simp); omega
        · simp [hσ2, Function.update_of_ne hj]
      · simp [hσ2]
      · funext r; by_cases hr : r = u
        · subst hr; simp [hσ2, hu]
        · simp [hσ2, Function.update_of_ne hr]
      · simp [hσ2]
    rw [hσ2'] at e2
    obtain ⟨τ, e3, h1, h2, h3, h4⟩ := rwL_spec v u t hvu hvt hut ys (σ.seth y 0) (by simp [hu]) (by simp [ht])
      (fun y' hy' => by
        by_cases h : y' = y
        · subst h; simp
        · simp [Function.update_of_ne h]; exact hy y' (by simp [hy'])) (by simp; omega)
    simp only [WState.seth_val] at e3 h4
    refine ⟨τ, WExec.mono (WExec.seq (WExec.seq e1 e2) e3) (by simp; ring_nf; omega), ?_, ?_, ?_, h4⟩
    · intro y' hy'
      simp only [List.mem_cons] at hy'
      by_cases h : y' ∈ ys
      · exact h1 y' h
      · rcases hy' with rfl | hy'
        · rw [h2 _ h]; simp
        · exact absurd hy' h
    · intro y' hy'
      simp only [List.mem_cons, not_or] at hy'
      rw [h2 y' hy'.2]; simp [Function.update_of_ne hy'.1]
    · rw [h3]; simp

def rcP (Fl Jr R U1 U2 : Fin nr) : WM ns nr :=
  .seq (copyR Jr R U1) (.seq (.inc R) (.ifr Fl (.seq (copyR R U2 U1) (WM.move U2 R)) .skip))

theorem rcP_spec (Fl Jr R U1 U2 : Fin nr) (hd : [Fl, Jr, R, U1, U2].Nodup) (σ : WState ns nr) (f J : ℕ)
    (hf : σ.val Fl = f) (hf1 : f ≤ 1) (hJ : σ.val Jr = J) (hR : σ.val R = 0) (h1 : σ.val U1 = 0)
    (h2 : σ.val U2 = 0) (hc : 2 * (J + 1) + 1 ≤ cap) :
    WExec cap (rcP Fl Jr R U1 U2) σ (σ.setv R ((f + 1) * (J + 1))) (60 * (J + 1) + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨FJ, FR, F1, F2⟩, ⟨JR, J1, J2⟩, ⟨R1, R2⟩, U12⟩ := hd
  have e1 := copyR_spec cap (v := Jr) (d := R) (t := U1) JR J1 R1 σ h1 (by omega)
  rw [hR, hJ, Nat.zero_add] at e1
  have e2 := WExec.inc (cap := cap) R (σ.setv R J) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at e2
  rw [wsetv_setv] at e2
  set σ2 := σ.setv R (J + 1) with hσ2
  by_cases hf0 : f = 0
  · subst hf0
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.ifrF (by simp [hσ2, Function.update_of_ne FR, hf])
      (WExec.skip σ2)))) (by simp [hσ2]) (by omega)
  · have hf1' : f = 1 := by omega
    subst hf1'
    have e3 := copyR_spec cap (v := R) (d := U2) (t := U1) R2 R1 (Ne.symm U12) σ2 (by simp [hσ2, Function.update_of_ne (Ne.symm R1), h1])
      (by simp [hσ2, Function.update_of_ne (Ne.symm R2), h2]; omega)
    simp only [hσ2, WState.setv_val, Function.update_self, Function.update_of_ne (Ne.symm R2), h2, Nat.zero_add] at e3
    have e4 := wmove_spec (cap := cap) U2 R (Ne.symm R2) (J + 1) ((σ.setv R (J + 1)).setv U2 (J + 1)) (by simp)
      (by simp; omega) (by simp [Function.update_of_ne R2]; omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.ifrT (by simp [hσ2, Function.update_of_ne FR, hf])
      (WExec.seq e3 e4)))) ?_ (by omega)
    apply WState.eq <;> simp
    funext r
    by_cases rR : r = R
    · subst rR; simp [Function.update_of_ne R2]; ring
    · by_cases rU : r = U2
      · subst rU; simp [Function.update_of_ne (Ne.symm R2), h2]
      · simp [Function.update_of_ne rR, Function.update_of_ne rU]

/-- Measure a framed word: `L := 2|w|` (two per marked pair), then rewind (`U` scratch). -/
def measP (IN : Fin (ns + 1)) (L U T : Fin nr) : WM ns nr :=
  .seq (.whs IN (.seq (.fwd IN) (.seq (.fwd IN) (.seq (.inc L) (.inc L))))) (.seq (copyR L U T) (WM.rewind IN U))

theorem meas_loop (IN : Fin (ns + 1)) (L : Fin nr) (rest : List Bool) :
    ∀ (w pre : List Bool) (σ : WState ns nr), σ.st IN = pre ++ RepairOrdinary.frame w ++ rest →
      σ.sh IN = pre.length → σ.val L + 2 * w.length < cap →
      WExec cap (.whs IN (.seq (.fwd IN) (.seq (.fwd IN) (.seq (.inc L) (.inc L))))) σ
        ((σ.seth IN (pre.length + 2 * w.length)).setv L (σ.val L + 2 * w.length)) (13 * w.length + 1)
  | [], pre, σ, hst, hsh, _ => by
    have hb : wbit σ IN = false := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [RepairOrdinary.frame, List.getD_append_right]
    have e : (σ.seth IN (pre.length + 2 * ([] : List Bool).length)).setv L (σ.val L + 2 * ([] : List Bool).length) = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = IN
        · subst hj; simp [hsh]
        · simp [Function.update_of_ne hj]
      · simp
      · simp
      · simp
    rw [e]; exact WExec.mono (WExec.whsF hb) (by simp)
  | b :: w, pre, σ, hst, hsh, hc => by
    have hb : wbit σ IN = true := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [RepairOrdinary.frame, List.getD_append_right]
    have e1 := WExec.fwd (cap := cap) IN σ
    have e2 := WExec.fwd (cap := cap) IN (σ.seth IN (σ.sh IN + 1))
    set σ2 := (σ.seth IN (σ.sh IN + 1)).seth IN ((σ.seth IN (σ.sh IN + 1)).sh IN + 1) with hσ2
    have e3 := WExec.inc (cap := cap) L σ2 (by simp [hσ2]; simp at hc; omega)
    have e4 := WExec.inc (cap := cap) L (σ2.setv L (σ2.val L + 1)) (by simp [hσ2]; simp at hc; omega)
    have ih := meas_loop IN L rest w (pre ++ [true, b])
      ((σ2.setv L (σ2.val L + 1)).setv L ((σ2.setv L (σ2.val L + 1)).val L + 1))
      (by simp [hσ2, hst, RepairOrdinary.frame]) (by simp [hσ2, hsh]) (by simp [hσ2]; simp at hc; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) ?_ (by simp only [List.length_cons]; omega)
    apply WState.eq
    · funext j; by_cases hj : j = IN
      · subst hj; simp [hσ2, hsh]; omega
      · simp [hσ2, Function.update_of_ne hj]
    · simp [hσ2]
    · funext r; by_cases hr : r = L
      · subst hr; simp [hσ2]; omega
      · simp [hσ2, Function.update_of_ne hr]
    · simp [hσ2]

theorem measP_spec (IN : Fin (ns + 1)) (L U T : Fin nr) (hLU : L ≠ U) (hLT : L ≠ T) (hUT : U ≠ T) (w : List Bool)
    (σ : WState ns nr) (hst : σ.st IN = RepairOrdinary.frame w) (hsh : σ.sh IN = 0) (hL : σ.val L = 0)
    (hU : σ.val U = 0) (hT : σ.val T = 0) (hc : 4 * w.length + 1 ≤ cap) :
    WExec cap (measP IN L U T) σ (σ.setv L (2 * w.length)) (60 * w.length + 10) := by
  have e1 := meas_loop cap IN L [] w [] σ (by simpa using hst) (by simpa using hsh) (by rw [hL]; omega)
  simp only [List.length_nil, Nat.zero_add, hL] at e1
  set σ1 := (σ.seth IN (2 * w.length)).setv L (2 * w.length) with hσ1
  have e2 := copyR_spec cap (v := L) (d := U) (t := T) hLU hLT hUT σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hLT), hT])
    (by simp [hσ1, Function.update_of_ne (Ne.symm hLU), hU]; omega)
  have hv : σ1.val L = 2 * w.length := by simp [hσ1]
  have hu : σ1.val U = 0 := by simp [hσ1, Function.update_of_ne (Ne.symm hLU), hU]
  rw [hv, hu, Nat.zero_add] at e2
  have e3 := wrewind_spec (cap := cap) IN U (2 * w.length) (σ1.setv U (2 * w.length)) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = IN
    · subst hj; simp [hσ1, hsh]
    · simp [hσ1, Function.update_of_ne hj]
  · simp [hσ1]
  · funext r; by_cases hr : r = U
    · subst hr; simp [hσ1, Function.update_of_ne (Ne.symm hLU), hU]
    · simp [hσ1, Function.update_of_ne hr]
  · simp [hσ1]

def pidxP (T0 T1 Tg I U V : Fin nr) : WM ns nr :=
  .ifr T0 (.seq (copyR T1 I U) (.seq (.inc I) (.seq (copyR Tg V U) (.seq (.dec V)
    (.seq (.ifr V (.inc I) .skip) (WM.clear V)))))) (.seq (copyR T1 I U) (.dec I))

def pidx (tag a g : ℕ) : ℕ := if tag = 0 then a - 1 else a + 1 + (if 2 ≤ g then 1 else 0)

theorem pidxP_spec (T0 T1 Tg I U V : Fin nr) (hd : [T0, T1, Tg, I, U, V].Nodup) (σ : WState ns nr)
    (tag a g : ℕ) (h0 : σ.val T0 = tag) (h1 : σ.val T1 = a) (hg : σ.val Tg = g) (hI : σ.val I = 0)
    (hU : σ.val U = 0) (hV : σ.val V = 0) (hc : a + g + 3 ≤ cap) :
    WExec cap (pidxP T0 T1 Tg I U V) σ (σ.setv I (pidx tag a g)) (40 * (a + g + 1) + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b2, b3, b4, b5⟩, ⟨c3, c4, c5⟩, ⟨d4, d5⟩, e5⟩ := hd
  have e1 := copyR_spec cap (v := T1) (d := I) (t := U) b3 b4 d4 σ hU (by omega)
  rw [hI, h1, Nat.zero_add] at e1
  by_cases ht : tag = 0
  · have e2 := WExec.dec (cap := cap) I (σ.setv I a) (by simp; omega)
    refine WExec.cast cap (WExec.ifrF (by rw [h0, ht]) (WExec.seq e1 e2)) ?_ (by omega)
    simp [pidx, ht, wsetv_setv]
  · have e2 := WExec.inc (cap := cap) I (σ.setv I a) (by simp; omega)
    simp only [WState.setv_val, Function.update_self] at e2
    rw [wsetv_setv] at e2
    have e3 := copyR_spec cap (v := Tg) (d := V) (t := U) c5 c4 (Ne.symm e5) (σ.setv I (a + 1))
      (by simp [Function.update_of_ne (Ne.symm d4), hU])
      (by simp [Function.update_of_ne (Ne.symm d5), hV, hg, Function.update_of_ne c3]; omega)
    simp only [WState.setv_val, Function.update_of_ne (Ne.symm d5), Function.update_of_ne c3,
      hV, hg, Nat.zero_add] at e3
    have e4 := WExec.dec (cap := cap) V ((σ.setv I (a + 1)).setv V g) (by simp; omega)
    simp only [WState.setv_val, Function.update_self] at e4
    rw [wsetv_setv] at e4
    set σ4 := (σ.setv I (a + 1)).setv V (g - 1) with hσ4
    by_cases hg2 : 2 ≤ g
    · have e5' := WExec.inc (cap := cap) I σ4 (by simp [hσ4, Function.update_of_ne d5]; omega)
      have hv : σ4.val V ≠ 0 := by simp [hσ4]; omega
      set σ5 := σ4.setv I (σ4.val I + 1) with hσ5
      have e6 := wclear_spec (cap := cap) V (g - 1) σ5 (by simp [hσ5, hσ4, Function.update_of_ne (Ne.symm d5)])
        (by simp [hσ5, hσ4, Function.update_of_ne (Ne.symm d5)]; omega)
      refine WExec.cast cap (WExec.ifrT (by rw [h0]; exact ht) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3
        (WExec.seq e4 (WExec.seq (WExec.ifrT hv e5') e6)))))) ?_ (by omega)
      apply WState.eq <;> simp [hσ5, hσ4]
      funext r
      by_cases rI : r = I
      · subst rI; simp [Function.update_of_ne d5, pidx, ht, hg2]
      · by_cases rV : r = V
        · subst rV; simp [Function.update_of_ne (Ne.symm d5), hV]
        · simp [Function.update_of_ne rI, Function.update_of_ne rV]
    · have hv : σ4.val V = 0 := by simp [hσ4]; omega
      have e6 := wclear_spec (cap := cap) V 0 σ4 hv (by rw [hv]; omega)
      refine WExec.cast cap (WExec.ifrT (by rw [h0]; exact ht) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3
        (WExec.seq e4 (WExec.seq (WExec.ifrF hv (WExec.skip σ4)) e6)))))) ?_ (by omega)
      apply WState.eq <;> simp [hσ4]
      funext r
      by_cases rI : r = I
      · subst rI; simp [Function.update_of_ne d5, pidx, ht, hg2]
      · by_cases rV : r = V
        · subst rV; simp [Function.update_of_ne (Ne.symm d5), hV]
        · simp [Function.update_of_ne rI, Function.update_of_ne rV]

/-- Clear every register of a list. -/
def clrL : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clrL rs)

theorem clrL_spec (B : ℕ) (hB : B ≤ cap) : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (∀ r ∈ rs, σ.val r ≤ B) →
    ∃ τ, WExec cap (clrL rs) σ τ (rs.length * (3 * B + 2)) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      (∀ r ∈ rs, τ.val r = 0) ∧ (∀ r, r ∉ rs → τ.val r = σ.val r)
  | [], σ, _ => ⟨σ, by simpa [clrL] using WExec.skip (cap := cap) σ, rfl, rfl, by simp, fun _ _ => rfl⟩
  | r :: rs, σ, h => by
    have e1 := wclear_spec (cap := cap) r (σ.val r) σ rfl (by have := h r (by simp); omega)
    obtain ⟨τ, e2, h1, h2, h3, h4⟩ := clrL_spec B hB rs (σ.setv r 0) (fun r' hr' => by
      by_cases h' : r' = r
      · subst h'; simp
      · simp [Function.update_of_ne h']; exact h r' (by simp [hr']))
    refine ⟨τ, WExec.mono (WExec.seq e1 e2) ?_, by rw [h1]; rfl, by rw [h2]; rfl, ?_, ?_⟩
    · have := h r (by simp); simp only [List.length_cons]; nlinarith
    · intro r' hr'
      by_cases hm : r' ∈ rs
      · exact h3 r' hm
      · simp only [List.mem_cons] at hr'
        rcases hr' with rfl | hr'
        · rw [h4 _ hm]; simp
        · exact absurd hr' hm
    · intro r' hr'
      simp only [List.mem_cons, not_or] at hr'
      rw [h4 r' hr'.2]; simp [Function.update_of_ne hr'.1]

/-- **Registers grow at most by the step count.** -/
theorem WExec.val_le {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    ∀ r, τ.val r ≤ σ.val r + n := by
  induction h with
  | skip σ => intro r; simp
  | inc r σ _ => intro r'; by_cases h : r' = r <;> simp [Function.update_apply, h]
  | dec r σ _ => intro r'; by_cases h : r' = r <;> simp [Function.update_apply, h]; omega
  | fwd i σ => intro r; simp
  | bwd i σ => intro r; simp
  | wr i b σ => intro r; simp
  | setc v σ => intro r; simp
  | seq _ _ ih1 ih2 => intro r; have := ih1 r; have := ih2 r; omega
  | ifrT _ _ ih => intro r; have := ih r; omega
  | ifrF _ _ ih => intro r; have := ih r; omega
  | ifsT _ _ ih => intro r; have := ih r; omega
  | ifsF _ _ ih => intro r; have := ih r; omega
  | whrF _ => intro r; omega
  | whrT _ _ _ ih1 ih2 => intro r; have := ih1 r; have := ih2 r; omega
  | whsF _ => intro r; omega
  | whsT _ _ _ ih1 ih2 => intro r; have := ih1 r; have := ih2 r; omega
  | mono _ hnm ih => intro r; have := ih r; omega

end NearCubicGates.Close.CounterMachine
