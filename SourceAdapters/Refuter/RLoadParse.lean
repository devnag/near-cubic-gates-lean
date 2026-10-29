import SourceAdapters.Refuter.RMachReq

/-!
# R's loader, part 1: parsing the input pair (input 7, R: INIT)

Paper anchor: `lem:multitape-refuter` (R reads its input `(M, 1^N)`) and the CLW20 input
convention `pairInput M N = fr(code M) fr(1^N)` (`Statement.lean` §22, CLW20 Thm 1.13 item 1: "The input to R
is a pair (M, 1^n)"); (the clock `T(N)` is computed from `1^N`).

The input stream holds `fr(fr(code) fr(1^N))`: every bit `b` of `code` or of `1^N` appears as the four cells
`1 1 1 b` (`f2 b`), each half ends with `1 0`. `forQ` walks these cells; `parseP` writes `CODE := fr(code)` and
`NU := 1^N` and returns every head to `0` (`parse_spec`, `≤ 100(|code|+N+1)` steps). `tcinP` writes the time
constructor's input `fr(1^N)` from `NU` (`tcin_spec`).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Moving one head or one counter of an `mv2` state -/

theorem fwd_mv2 (σ : WState ns nr) (X : Fin (ns + 1)) (R : Fin nr) (h v h' : ℕ) (e : h' = h + 1) :
    WXExec cap (WMX.fwd X) (mv2 σ X R h v) (mv2 σ X R h' v) 1 := by
  refine (WXExec.fwd cap X (mv2 σ X R h v)).cast cap ?_ le_rfl
  subst e; unfold mv2; wst

theorem inc_mv2 (σ : WState ns nr) (X : Fin (ns + 1)) (R : Fin nr) (h v v' : ℕ) (e : v' = v + 1) (hv : v < cap) :
    WXExec cap (WMX.inc R) (mv2 σ X R h v) (mv2 σ X R h v') 3 := by
  refine (WXExec.inc cap R (mv2 σ X R h v) (by simp [mv2]; omega)).cast cap ?_ le_rfl
  subst e; unfold mv2; wst

theorem app_mv2 (σ : WState ns nr) (D X : Fin (ns + 1)) (RD R : Fin nr) (hX : X ≠ D) (hR : R ≠ RD) (h v : ℕ)
    (w : List Bool) : app (mv2 σ X R h v) D RD w = mv2 (app σ D RD w) X R h v := by
  unfold app mv2; wst

/-! ## Reading the cells `1 1 1 b` -/

theorem rd_pre (pre L : List Bool) (i : ℕ) : readTapeBit (pre ++ L) (pre.length + i) = readTapeBit L i := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem rd_q (l rest : List Bool) (k : ℕ) (hk : k < l.length) :
    readTapeBit (l.flatMap f2 ++ rest) (4 * k + 1) = true ∧ readTapeBit (l.flatMap f2 ++ rest) (4 * k + 3) = l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b l ih =>
    cases k with
    | zero => simp [readTapeBit]
    | succ k =>
      have := ih k (by simp at hk; omega)
      simp only [List.flatMap_cons, f2, List.cons_append, List.nil_append] at this ⊢
      simpa [readTapeBit, show 4 * (k + 1) + 1 = 4 * k + 1 + 4 by ring, show 4 * (k + 1) + 3 = 4 * k + 3 + 4 by ring]
        using this

theorem flatMap_f2_length (l : List Bool) : (l.flatMap f2).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp [f2]; ring

theorem rd_q_end (l rest : List Bool) (j : ℕ) :
    readTapeBit (l.flatMap f2 ++ rest) (4 * l.length + j) = readTapeBit rest j := by
  rw [← flatMap_f2_length]; exact rd_pre _ _ j

/-! ## The four-cell walk -/

/-- Walk the cells `1 1 1 b` of `X` from the cell `p + 1` of the first group: `inner` runs with the head on each
data bit; `R` counts the head's moves. -/
def forQ (X : Fin (ns + 1)) (R : Fin nr) (inner : WMX ns nr) : WMX ns nr :=
  .whs X (.seq (WMX.fwd X) (.seq (WMX.fwd X) (.seq inner (.seq (WMX.fwd X) (.seq (WMX.fwd X)
    (.seq (WMX.inc R) (.seq (WMX.inc R) (.seq (WMX.inc R) (WMX.inc R)))))))))

theorem forQ_spec (X : Fin (ns + 1)) (R : Fin nr) (inner : WMX ns nr) (pre l rest : List Bool) (p c r0 : ℕ)
    (hp : pre.length = p) (st : ℕ → WState ns nr) (hX : ∀ k ≤ l.length, (st k).st X = pre ++ (l.flatMap f2 ++ rest))
    (hrest : readTapeBit rest 1 = false)
    (hin : ∀ k < l.length, WXExec cap inner (mv2 (st k) X R (p + 4 * k + 3) (r0 + 4 * k))
      (mv2 (st (k + 1)) X R (p + 4 * k + 3) (r0 + 4 * k)) c) (hcap : r0 + 4 * l.length ≤ cap) :
    WXExec cap (forQ X R inner) (mv2 (st 0) X R (p + 1) r0)
      (mv2 (st l.length) X R (p + 4 * l.length + 1) (r0 + 4 * l.length)) (l.length * (c + 26) + 1) := by
  have hloop := loopS cap (i := X)
    (body := .seq (WMX.fwd X) (.seq (WMX.fwd X) (.seq inner (.seq (WMX.fwd X) (.seq (WMX.fwd X)
      (.seq (WMX.inc R) (.seq (WMX.inc R) (.seq (WMX.inc R) (WMX.inc R)))))))))
    (fun k => mv2 (st k) X R (p + 4 * k + 1) (r0 + 4 * k)) l.length (c + 24)
    (fun k hk => by
      simp only [wbit, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hX k hk.le]
      rw [← hp, show pre.length + 4 * k + 1 = pre.length + (4 * k + 1) by ring, rd_pre]
      exact (rd_q l rest k hk).1)
    (by
      simp only [wbit, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hX _ le_rfl]
      rw [← hp, show pre.length + 4 * l.length + 1 = pre.length + (4 * l.length + 1) by ring, rd_pre, rd_q_end]
      exact hrest)
    (fun k hk => by
      have e1 := fwd_mv2 cap (st k) X R (p + 4 * k + 1) (r0 + 4 * k) (p + 4 * k + 2) rfl
      have e2 := fwd_mv2 cap (st k) X R (p + 4 * k + 2) (r0 + 4 * k) (p + 4 * k + 3) rfl
      have e3 := hin k hk
      have e4 := fwd_mv2 cap (st (k + 1)) X R (p + 4 * k + 3) (r0 + 4 * k) (p + 4 * k + 4) rfl
      have e5 := fwd_mv2 cap (st (k + 1)) X R (p + 4 * k + 4) (r0 + 4 * k) (p + 4 * (k + 1) + 1) (by ring)
      have e6 := inc_mv2 cap (st (k + 1)) X R (p + 4 * (k + 1) + 1) (r0 + 4 * k) (r0 + 4 * k + 1) rfl (by omega)
      have e7 := inc_mv2 cap (st (k + 1)) X R (p + 4 * (k + 1) + 1) (r0 + 4 * k + 1) (r0 + 4 * k + 2) rfl (by omega)
      have e8 := inc_mv2 cap (st (k + 1)) X R (p + 4 * (k + 1) + 1) (r0 + 4 * k + 2) (r0 + 4 * k + 3) rfl (by omega)
      have e9 := inc_mv2 cap (st (k + 1)) X R (p + 4 * (k + 1) + 1) (r0 + 4 * k + 3) (r0 + 4 * (k + 1)) (by ring)
        (by omega)
      exact (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
        (WXExec.seq e7 (WXExec.seq e8 e9)))))))).mono (by omega))
  simp only [Nat.mul_zero, Nat.add_zero] at hloop
  exact hloop.mono (by nlinarith)

/-- The cells of `l` drive an act: `D` receives `l.flatMap f`. -/
theorem forQ_act {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (X : Fin (ns + 1)) (R : Fin nr) (hXD : X ≠ D) (hR : R ≠ RD)
    (σ : WState ns nr) (pre l rest : List Bool) (p r0 : ℕ) (hp : pre.length = p)
    (hX : σ.st X = pre ++ (l.flatMap f2 ++ rest)) (hrest : readTapeBit rest 1 = false)
    (hD : σ.sh D = (σ.st D).length) (hfl : ∀ b, (f b).length ≤ 4) (hc : σ.val RD + 4 * l.length ≤ cap)
    (hcap : r0 + 4 * l.length ≤ cap) :
    WXExec cap (forQ X R (.ifs X (act true) (act false))) (mv2 σ X R (p + 1) r0)
      (mv2 (app σ D RD (l.flatMap f)) X R (p + 4 * l.length + 1) (r0 + 4 * l.length)) (l.length * (c + 27) + 1) := by
  have h := forQ_spec cap X R (.ifs X (act true) (act false)) pre l rest p (c + 1) r0 hp
    (fun k => app σ D RD ((l.take k).flatMap f))
    (fun k _ => by rw [app_st_ne _ _ _ _ _ hXD, hX]) hrest
    (fun k hk => by
      have hbit : wbit (mv2 (app σ D RD ((l.take k).flatMap f)) X R (p + 4 * k + 3) (r0 + 4 * k)) X = l[k] := by
        simp only [wbit, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
          app_st_ne _ _ _ _ _ hXD, hX]
        rw [← hp, show pre.length + 4 * k + 3 = pre.length + (4 * k + 3) by ring, rd_pre]
        exact (rd_q l rest k hk).2
      have htake : (l.take (k + 1)).flatMap f = (l.take k).flatMap f ++ f l[k] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append,
          List.flatMap_singleton]
      have hlen := flatMap_len_le f hfl (l.take k)
      have hlk : (l.take k).length ≤ k := by simp
      have hpre : (mv2 (app σ D RD ((l.take k).flatMap f)) X R (p + 4 * k + 3) (r0 + 4 * k)).sh D =
          ((mv2 (app σ D RD ((l.take k).flatMap f)) X R (p + 4 * k + 3) (r0 + 4 * k)).st D).length := by
        simp [mv2, Function.update_of_ne hXD.symm, hD]
      have hcv : (mv2 (app σ D RD ((l.take k).flatMap f)) X R (p + 4 * k + 3) (r0 + 4 * k)).val RD +
          (f l[k]).length ≤ cap := by
        simp only [mv2, WState.setv_val, WState.seth_val, Function.update_of_ne hR.symm, app_val_R]
        have := hfl l[k]; nlinarith
      have e := hact l[k] _ hpre hcv
      have e' : WXExec cap (.ifs X (act true) (act false))
          (mv2 (app σ D RD ((l.take k).flatMap f)) X R (p + 4 * k + 3) (r0 + 4 * k))
          (app (mv2 (app σ D RD ((l.take k).flatMap f)) X R (p + 4 * k + 3) (r0 + 4 * k)) D RD (f l[k])) (c + 1) := by
        cases hb : l[k]
        · rw [hb] at hbit e; exact WXExec.ifsF hbit e
        · rw [hb] at hbit e; exact WXExec.ifsT hbit e
      refine e'.cast cap ?_ le_rfl
      rw [htake, app_mv2 _ _ _ _ _ hXD hR, app_app])
    hcap
  simp only [List.take_zero, List.flatMap_nil, app_nil, List.take_length] at h
  exact h.mono (by nlinarith)

/-! ## Appending a single bit -/

/-- Append the bit `b` at the end of `D`. -/
def wb (D : Fin (ns + 1)) (R : Fin nr) (b : Bool) : WMX ns nr := .seq (WMX.wr D b) (.seq (WMX.fwd D) (WMX.inc R))

theorem wb_act (D : Fin (ns + 1)) (R : Fin nr) : IsAct cap (wb D R) D R (fun b => [b]) 7 := by
  intro b τ hD hc
  have e1 := WXExec.wr cap D b τ
  have w : writeTapeBit (τ.st D) (τ.sh D) b = τ.st D ++ [b] := by rw [hD, wtb_append]
  rw [w] at e1
  have e2 := WXExec.fwd cap D (τ.sets D (τ.st D ++ [b]))
  have e3 := WXExec.inc cap R ((τ.sets D (τ.st D ++ [b])).seth D ((τ.sets D (τ.st D ++ [b])).sh D + 1))
    (by simp at hc ⊢; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  unfold app; wst

/-! ## Parsing `fr(fr(code) fr(1^N))` -/

/-- The input stream in cells. -/
theorem in_cells (code : List Bool) (N : ℕ) :
    RepairOrdinary.frame (RepairOrdinary.frame code ++ RepairOrdinary.frame (List.replicate N true)) =
      [] ++ (code.flatMap f2 ++ (f1 false ++ ((List.replicate N true).flatMap f2 ++ [true, false, false]))) ∧
    RepairOrdinary.frame (RepairOrdinary.frame code ++ RepairOrdinary.frame (List.replicate N true)) =
      (code.flatMap f2 ++ f1 false) ++ ((List.replicate N true).flatMap f2 ++ [true, false, false]) := by
  rw [frame_eq_fpre, fpre_append, fpre_frame, fpre_frame]
  constructor <;> simp [f1]

/-- **Parse the input pair**: `CODE := fr(code)`, `NU := 1^N`; counters `RI RC RN`. -/
def parseP (IN CODE NU : Fin (ns + 1)) (RI RC RN : Fin nr) : WMX ns nr :=
  .seq (WMX.fwd IN) (.seq (WMX.inc RI)
  (.seq (forQ IN RI (.ifs IN (em1 CODE RC true) (em1 CODE RC false)))
  (.seq (WMX.wr CODE false) (.seq (rew CODE RC)
  (.seq (WMX.fwd IN) (.seq (WMX.fwd IN) (.seq (WMX.inc RI) (.seq (WMX.inc RI)
  (.seq (forQ IN RI (.ifs IN (wb NU RN true) (wb NU RN false)))
  (.seq (rew NU RN) (rew IN RI)))))))))))

theorem flatMap_single (l : List Bool) : l.flatMap (fun b => [b]) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

set_option maxHeartbeats 400000 in
theorem parse_spec (IN CODE NU : Fin (ns + 1)) (RI RC RN : Fin nr) (h1 : IN ≠ CODE) (h2 : IN ≠ NU) (h3 : CODE ≠ NU)
    (r1 : RI ≠ RC) (r2 : RI ≠ RN) (r3 : RC ≠ RN) (σ : WState ns nr) (code : List Bool) (N : ℕ)
    (hIN : σ.st IN = RepairOrdinary.frame (RepairOrdinary.frame code ++ RepairOrdinary.frame (List.replicate N true)))
    (hCODE : σ.st CODE = []) (hNU : σ.st NU = []) (sIN : σ.sh IN = 0) (sCODE : σ.sh CODE = 0) (sNU : σ.sh NU = 0)
    (vI : σ.val RI = 0) (vC : σ.val RC = 0) (vN : σ.val RN = 0) (hcap : 4 * (code.length + N + 2) ≤ cap) :
    WXExec cap (parseP IN CODE NU RI RC RN) σ
      ((σ.sets CODE (RepairOrdinary.frame code)).sets NU (List.replicate N true)) (100 * (code.length + N + 1)) := by
  obtain ⟨hc1, hc2⟩ := in_cells code N
  set c := code.length with hc
  -- the first walk
  have e1 := WXExec.fwd cap IN σ
  have e2 := WXExec.inc cap RI (σ.seth IN (σ.sh IN + 1)) (by simp [vI]; omega)
  have e12 : (σ.seth IN (σ.sh IN + 1)).setv RI ((σ.seth IN (σ.sh IN + 1)).val RI + 1) = mv2 σ IN RI (0 + 1) 1 := by
    unfold mv2; wst
  rw [e12] at e2
  have e3 := forQ_act cap (em1_act cap CODE RC) IN RI h1 r1 σ [] code _ 0 1 rfl (by rw [hIN]; exact hc1)
    (by simp [readTapeBit, f1]) (by rw [sCODE, hCODE]; rfl) (fun b => by simp) (by rw [vC]; omega) (by omega)
  set σ3 := mv2 (app σ CODE RC (code.flatMap fun b => [true, b])) IN RI (0 + 4 * c + 1) (1 + 4 * c) with hσ3
  have hfp : (code.flatMap fun b => [true, b]) = fpre code := rfl
  have e4 := WXExec.wr cap CODE false σ3
  have w4 : writeTapeBit (σ3.st CODE) (σ3.sh CODE) false = RepairOrdinary.frame code := by
    simp only [hσ3, mv2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne h1.symm, app_st_D, app_sh_D, hCODE, sCODE, List.nil_append, Nat.zero_add, hfp]
    rw [show (fpre code).length = (fpre code).length from rfl, wtb_append, frame_eq_fpre]
  rw [w4] at e4
  have e5 := rew_spec cap CODE RC (σ3.sets CODE (RepairOrdinary.frame code)) (2 * c)
    (by simp [hσ3, mv2, Function.update_of_ne r1.symm, vC, hfp, hc]) (by omega)
  -- the second walk
  set σ5 := ((σ3.sets CODE (RepairOrdinary.frame code)).setv RC 0).seth CODE
    ((σ3.sets CODE (RepairOrdinary.frame code)).sh CODE - 2 * c) with hσ5
  have e6 := WXExec.fwd cap IN σ5
  have e7 := WXExec.fwd cap IN (σ5.seth IN (σ5.sh IN + 1))
  have e8 := WXExec.inc cap RI ((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1))
    (by simp [hσ5, hσ3, mv2, Function.update_of_ne r1, Function.update_apply]; omega)
  have e9 := WXExec.inc cap RI (((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1)).setv RI
    (((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1)).val RI + 1))
    (by simp [hσ5, hσ3, mv2, Function.update_of_ne r1, Function.update_apply]; omega)
  set ρ := (σ.sets CODE (RepairOrdinary.frame code)) with hρ
  have e69 : (((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1)).setv RI
      (((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1)).val RI + 1)).setv RI
      ((((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1)).setv RI
      (((σ5.seth IN (σ5.sh IN + 1)).seth IN ((σ5.seth IN (σ5.sh IN + 1)).sh IN + 1)).val RI + 1)).val RI + 1) =
      mv2 ρ IN RI (4 * c + 2 + 1) (4 * c + 3) := by
    simp only [hσ5, hσ3, hρ]; unfold mv2 app; rw [hfp]; wst
  rw [e69] at e9
  have hlenpre : (code.flatMap f2 ++ f1 false).length = 4 * c + 2 := by
    simp only [List.length_append, flatMap_f2_length, f1, List.length_cons, List.length_nil]; omega
  have e10 := forQ_act cap (wb_act cap NU RN) IN RI h2 r2 ρ (code.flatMap f2 ++ f1 false) (List.replicate N true)
    [true, false, false] (4 * c + 2) (4 * c + 3) hlenpre (by simp only [hρ, WState.sets_st, Function.update_of_ne h1]; rw [hIN]; exact hc2)
    (by simp [readTapeBit]) (by simp [hρ, Function.update_of_ne h3.symm, hNU, sNU]) (fun b => by simp)
    (by simp [hρ, vN]; omega) (by simp; omega)
  rw [List.length_replicate, flatMap_single] at e10
  set σ10 := mv2 (app ρ NU RN (List.replicate N true)) IN RI (4 * c + 2 + 4 * N + 1) (4 * c + 3 + 4 * N) with hσ10
  have e11 := rew_spec cap NU RN σ10 N (by simp [hσ10, mv2, Function.update_of_ne r2.symm, hρ, vN]) (by omega)
  have e12' := rew_spec cap IN RI ((σ10.setv RN 0).seth NU (σ10.sh NU - N)) (4 * c + 3 + 4 * N)
    (by simp [hσ10, mv2, Function.update_of_ne r2]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7
    (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 (WXExec.seq e11 e12'))))))))))).cast cap ?_ (by nlinarith)
  simp only [hσ10, hρ]
  unfold mv2 app
  wst

/-! ## The time constructor's input `fr(1^N)` -/

/-- `K0 := fr(1^N)` from `NU = 1^N`. -/
def tcinP (NU K0 : Fin (ns + 1)) (R1 RK : Fin nr) : WMX ns nr :=
  .seq (forU NU R1 (em1 K0 RK true)) (.seq (WMX.wr K0 false) (rew K0 RK))

theorem tcin_spec (NU K0 : Fin (ns + 1)) (R1 RK : Fin nr) (h : NU ≠ K0) (hr : R1 ≠ RK) (σ : WState ns nr) (N : ℕ)
    (hNU : σ.st NU = List.replicate N true) (sNU : σ.sh NU = 0) (hK : σ.st K0 = []) (sK : σ.sh K0 = 0)
    (v1 : σ.val R1 = 0) (vK : σ.val RK = 0) (hcap : 2 * N + 1 ≤ cap) :
    WXExec cap (tcinP NU K0 R1 RK) σ (σ.sets K0 (RepairOrdinary.frame (List.replicate N true))) (40 * (N + 1)) := by
  have e1 := forU_act cap (em1_act cap K0 RK) true NU R1 h hr σ N hNU sNU v1 (by rw [sK, hK]; rfl)
    (by simp [vK]; omega) (by omega)
  have hfp : ((List.replicate N true).flatMap fun b => [true, b]) = fpre (List.replicate N true) := rfl
  rw [hfp] at e1
  have e2 := WXExec.wr cap K0 false (app σ K0 RK (fpre (List.replicate N true)))
  have w : writeTapeBit ((app σ K0 RK (fpre (List.replicate N true))).st K0)
      ((app σ K0 RK (fpre (List.replicate N true))).sh K0) false = RepairOrdinary.frame (List.replicate N true) := by
    simp only [app_st_D, app_sh_D, hK, sK, List.nil_append, Nat.zero_add]
    rw [wtb_append, frame_eq_fpre]
  rw [w] at e2
  have e3 := rew_spec cap K0 RK ((app σ K0 RK (fpre (List.replicate N true))).sets K0
    (RepairOrdinary.frame (List.replicate N true))) (2 * N) (by simp [vK]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by nlinarith)
  unfold app
  wst

end NearCubicGates.Adapters.Refuter.RM
