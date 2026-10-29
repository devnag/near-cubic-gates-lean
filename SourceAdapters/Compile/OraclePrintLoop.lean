import SourceAdapters.Compile.OraclePrintStep

/-!
# The printer's vectors, rounds and verdict

proof of `thm:short-pcp-ours`: the initial formulas, then `fuel` rounds (query address bits, one oracle gate, transition formulas on
the extended wires), then the verdict. On the token machine representation:
* `vecCopyP T`: the vector of template `T` over `clockBits` members, its outputs become the wire map;
* `roundP`: one round (`roundPS`); `roundsP`: all `fuel` rounds (`roundsPS`);
* `verdictP`: the verdict template, its output wire in `OUTR` (`planPS`).
`Cfg` collects the run-wide side conditions (register width, value bound `V`, token bound `L`).
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Compile (OracleCompilationRequest)
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicGates.Adapters.Compile.OracleExpressions (wireStream vectorStream)

set_option autoImplicit false

/-! ## Static sizes of the fixed templates -/

theorem U.orList_depth (l : List U) (h : ∀ u ∈ l, u.depth = 0) : (U.orList l).depth = 0 := by
  induction l with
  | nil => rfl
  | cons u l ih => simp only [U.orList, U.depth]; rw [h u (by simp), ih (fun v hv => h v (by simp [hv]))]; rfl

theorem U.orList_tneed (l : List U) (K : ℕ) (hK : 1 ≤ K) (h : ∀ u ∈ l, u.tneed ≤ K) : (U.orList l).tneed ≤ K := by
  induction l with
  | nil => simp [U.orList, U.ofBool, U.tneed, Tm.ofBool, Tm.need]; omega
  | cons u l ih => simp only [U.orList, U.tneed]; exact max_le (h u (by simp)) (ih (fun v hv => h v (by simp [hv])))

theorem addrT_size (p : OrdinaryOracleProgram) : (addrT p).depth ≤ 11 ∧ (addrT p).tneed ≤ 16 := by
  simp [addrT, addrU, prefixU, cellU, allocU, U.depth, U.tneed, Tm.need, cellT, lenT, U.ofBool, Tm.ofBool]

theorem verdU_size (p : OrdinaryOracleProgram) : (verdU p).depth ≤ 12 ∧ (verdU p).tneed ≤ 16 := by
  simp only [verdU, U.depth, U.tneed]
  rw [U.orList_depth _ (by simp [U.depth, U.ofBool])]
  refine ⟨by simp, ?_⟩
  refine max_le (U.orList_tneed _ 16 (by omega) (by simp [U.tneed, U.ofBool, Tm.ofBool, Tm.need])) ?_
  simp [cellT, lenT, Tm.need]

/-! ## Token budget of a vector -/

variable {n arity : ℕ}

theorem vec_tok_le {width : ℕ} (w : List ℕ) (ρ : Fin width → ℕ) (count : ℕ) (exprs : Fin count → BoolExpr width)
    (tf : ℕ → List Tok) (S : PS n arity) (h : ∀ j : Fin count, tf j.val = postR ρ (exprs j)) :
    S.cnt + ((List.range count).flatMap tf).length ≤ 2 * (PS.vec w tf count S).1.cnt + count := by
  obtain ⟨h1, -⟩ := vec_stream w ρ count exprs tf S h
  have h2 := vec_tokens_le (n := n) (arity := arity) ρ (fun i => w.getD (ρ i) 0) count exprs tf S.cnt h
  rw [h1]
  dsimp only
  omega

theorem take_overwrite (old new : List ℕ) : (overwrite old new).take new.length = new := by
  simp [overwrite]

/-! ## The run configuration -/

variable {C : Ctx}

/-- The run-wide side conditions for request `r`. -/
structure Cfg (C : Ctx) (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) (V L : ℕ) :
    Prop where
  hV : 2 * V + 2 ≤ 2 ^ C.Wd
  hV1 : 1 ≤ V
  hL : 2 * L + 2 ≤ 2 ^ C.Wd
  h8 : 8 ≤ 2 ^ C.Wd
  hLN : 2 * (planPS p T r).cnt + clockBits p (requestWidth r) r.fuel + r.ell + (reqD r).length + 4 ≤ L
  hcV : clockBits p (requestWidth r) r.fuel + r.ell ≤ V
  okA : ∀ j < r.ell, (addrT p).okV V (reqD r) (reqEnv r ++ [j])
  okI : ∀ j < clockBits p (requestWidth r) r.fuel, T.init.okV V (reqD r) (reqEnv r ++ [j])
  okT : ∀ j < clockBits p (requestWidth r) r.fuel, T.trans.okV V (reqD r) (reqEnv r ++ [j])
  okV : (verdU p).okV V (reqD r) (reqEnv r)

section Run

variable {p : OrdinaryOracleProgram} {T : Templates p} {r : OracleCompilationRequest} {V L : ℕ}

theorem Cfg.gk (cf : Cfg C p T r V L) (w : List ℕ) (hw : w.length ≤ L) : Gk C w (reqD r) V L :=
  ⟨cf.hV, cf.hV1, cf.hL, hw, by have := cf.hLN; omega, cf.h8⟩

theorem Gl.keep {Tr R M : ℕ → Prop} {a b : DS VV MM} (hg : Gl p r a) (k : Keep Tr R M a b)
    (hT : ∀ y, Tr y → y < 20 ∨ (22 < y ∧ y < 64) ∨ 80 ≤ y) : Gl p r b :=
  ⟨fun j hj => by rw [k.env (Sl j) (fun h => by have := hT _ h; rw [Sl_val hj] at this; omega), hg.slots j hj],
    by rw [k.env ELR (fun h => by have := hT _ h; simp at this), hg.ell],
    by rw [k.env FUR (fun h => by have := hT _ h; simp at this), hg.fuel],
    by rw [k.env CBR (fun h => by have := hT _ h; simp at this), hg.cb], by rw [k.out, hg.out]⟩

theorem scr4_ok (y : ℕ) (h : Scr 4 y) : y < 20 ∨ (22 < y ∧ y < 64) ∨ 80 ≤ y := by
  unfold Scr MachT at h; omega

/-- A vector of `T` over `clockBits` members, moved to the wire map. -/
def vecCopyP (Tv : U) : St VV MM := .seq (.op (.copy VC CBR)) (.seq (vecP Tv) copyW)

theorem vecCopy_spec (cf : Cfg C p T r V L) (Tv : U) (hd : 5 + Tv.depth ≤ 16) (ht : Tv.tneed ≤ 16)
    (hok : ∀ j < clockBits p (requestWidth r) r.fuel, Tv.okV V (reqD r) (reqEnv r ++ [j]))
    (S : PS r.ell r.ell) (w : List ℕ) (a : DS VV MM) (h : Rep w (reqD r) S a) (hg : Gl p r a)
    (hwL : w.length ≤ L) (hrc : a.rc W2 ≤ L)
    (h1 : S.cnt + ((List.range (clockBits p (requestWidth r) r.fuel)).flatMap (tokF Tv (reqD r) (reqEnv r))).length ≤ L)
    (h2 : S.stk.length +
      ((List.range (clockBits p (requestWidth r) r.fuel)).flatMap (tokF Tv (reqD r) (reqEnv r))).length ≤ L) :
    Hx C (vecCopyP Tv) a (fun b c =>
      Rep (overwrite w (PS.vec w (tokF Tv (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel) S).2) (reqD r)
        (PS.vec w (tokF Tv (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel) S).1 b ∧ Gl p r b ∧
      b.rc W2 = clockBits p (requestWidth r) r.fuel ∧
      (∀ y : Fin VV, 14 ≤ y.val → y.val < 40 → y.val ≠ 24 → b.env y = a.env y) ∧
      c ≤ (Tv.ucost + Qc L) * L + (12 * L + 40) * L + 10 * L + 30) := by
  set cb := clockBits p (requestWidth r) r.fuel with hcb
  set tok := (List.range cb).flatMap (tokF Tv (reqD r) (reqEnv r)) with htok
  have hcbL : cb + 1 ≤ L := by have := cf.hLN; omega
  refine Hx.seq' (Hx.ofHs (hs_copy C VC CBR a (by decide))) (fun a1 c1 ⟨hc1, ha1⟩ => ?_)
  subst ha1
  have h1' : Rep w (reqD r) S (a.set VC (a.env CBR)) :=
    h.of_regs (Keep.set (T := (· = 96)) (R := fun _ => False) (M := fun _ => False) _ VC _ rfl) (fun y hy => by omega)
  have hg1 : Gl p r (a.set VC (a.env CBR)) :=
    hg.keep (Keep.set (T := (· = 96)) (R := fun _ => False) (M := fun _ => False) _ VC _ rfl) (fun y hy => by omega)
  have hVC : (a.set VC (a.env CBR)).env VC = cb := by rw [DS.set_env_self, hg.cb]
  have hok' : ∀ j < cb, Tv.okV V (reqD r) (reqEnv r ++ [j]) := hok
  refine Hx.seq' (vecP_spec (cf.gk w hwL) Tv (reqEnv r) (by simp) hd ht cb hok' (by have := cf.hcV; omega) S _ h1'
    hg1.slots hVC h1 h2) (fun b c ⟨r1', r2', r3, r4, r5⟩ => ?_)
  have r1 : Rep w (reqD r) (PS.vec w (tokF Tv (reqD r) (reqEnv r)) cb S).1 b := r1'
  have r2 : b.ram W2 = overwrite ((a.set VC (a.env CBR)).ram W2) (PS.vec w (tokF Tv (reqD r) (reqEnv r)) cb S).2 := r2'
  have hgb : Gl p r b := hg1.keep r4 scr4_ok
  have hVCb : b.env VC = cb := by rw [r4.env VC (by unfold Scr MachT; simp), hVC]
  obtain ⟨-, -, e3⟩ := PS.vec_bounds w (tokF Tv (reqD r) (reqEnv r)) cb S
  have hW2l : cb ≤ (b.ram W2).length := by
    rw [r2]
    have := overwrite_length_ge ((a.set VC (a.env CBR)).ram W2) (PS.vec w (tokF Tv (reqD r) (reqEnv r)) cb S).2
    omega
  refine Hx.mono' (copyW_spec _ _ _ b r1 cb hVCb hW2l (by have := cf.hL; omega)) (fun d k ⟨d1, d2, d3, d4⟩ => ?_)
  have htake : (b.ram W2).take cb = (PS.vec w (tokF Tv (reqD r) (reqEnv r)) cb S).2 := by
    rw [r2]
    have := take_overwrite ((a.set VC (a.env CBR)).ram W2) (PS.vec w (tokF Tv (reqD r) (reqEnv r)) cb S).2
    rwa [e3] at this
  rw [htake] at d1
  refine ⟨d1, hgb.keep d3 (fun y hy => by unfold CwT at hy; omega), d2, fun y h1 h2 h3 => ?_, ?_⟩
  · rw [d3.env y (by unfold CwT; omega), r4.env y (by unfold Scr MachT; omega), DS.set_env_ne _ _ (ne_of_val (by simp; omega))]
  have hwc : b.rc WM ≤ w.length := r1.base.wc
  have hrc1 : (a.set VC (a.env CBR)).rc W2 ≤ L := hrc
  have htokL : tok.length ≤ L := by omega
  have hm : (Tv.ucost + Qc L) * ((List.range cb).flatMap (fun j => Tv.toks (reqD r) (reqEnv r ++ [j]))).length ≤
      (Tv.ucost + Qc L) * L := Nat.mul_le_mul_left _ htokL
  have hm2 : (12 * L + 40) * cb ≤ (12 * L + 40) * L := Nat.mul_le_mul_left _ (by omega)
  rw [r3] at d4
  omega

theorem Rep.of_regs' {w : List ℕ} {D : List Bool} {S : PS n arity} {Tr : ℕ → Prop} {a b : DS VV MM}
    (h : Rep w D S a) (k : Keep Tr (fun _ => False) (fun _ => False) a b)
    (hT : ∀ y, Tr y → 3 ≤ y ∧ (y < 101 ∨ 104 < y)) : Rep w D S b := by
  have hk : ∀ y : Fin VV, (y.val < 3 ∨ (101 ≤ y.val ∧ y.val ≤ 104)) → b.env y = a.env y :=
    fun y hy => k.env y (fun h' => by have := hT _ h'; omega)
  obtain ⟨⟨c, cn, ns, nsc, wm, wl, wc, dsr, dl, dc⟩, s1, s2, s3⟩ := h
  exact ⟨⟨⟨by rw [hk vZ (by left; decide), c.z], by rw [hk v1 (by left; decide), c.one],
    by rw [hk v2 (by left; decide), c.two]⟩, by rw [hk CNT (by simp), cn], by rw [k.ram NS id, ns],
    by rw [k.rc NS id, k.ram NS id, nsc], by rw [k.ram WM id, wm], by rw [hk WL (by simp), wl],
    by rw [k.rc WM id]; exact wc, by rw [k.ram DSt id, dsr], by rw [hk DL (by simp), dl],
    by rw [k.rc DSt id]; exact dc⟩, by rw [hk HR (by simp), s1], by rw [k.rc STK id, s2], by rw [k.ram STK id, s3]⟩

/-! ## One round -/

/-- One clock round: the address vector, the oracle gate and its answer wire, the transition vector. -/
def roundP (Tt Ta : U) : St VV MM := .seq (.op (.copy VC ELR)) (.seq (vecP Ta) (.seq oracleP (vecCopyP Tt)))

/-- The cost bound of one round. -/
def roundCost (uA uT L : ℕ) : ℕ := (uA + Qc L) * L + (uT + Qc L) * L + 2 * ((12 * L + 40) * L) + 30 * L + 120

theorem roundPS_cnt_ge (S : PS r.ell r.ell) (w : List ℕ) :
    (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt + 1 ≤
      (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).1.cnt :=
  PS.vec_cnt_ge (putAt w (clockBits p (requestWidth r) r.fuel)
    (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt) (tokF T.trans (reqD r) (reqEnv r))
    (clockBits p (requestWidth r) r.fuel)
    ((PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.oracle (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2)

theorem roundP_spec (cf : Cfg C p T r V L) (S : PS r.ell r.ell) (w : List ℕ) (a : DS VV MM)
    (h : Rep w (reqD r) S a) (hg : Gl p r a) (hS : S.stk = []) (hw1 : clockBits p (requestWidth r) r.fuel ≤ w.length)
    (hw2 : w.length ≤ clockBits p (requestWidth r) r.fuel + r.ell + 1) (hrc : a.rc W2 ≤ L)
    (hfin : (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).1.cnt ≤
      (planPS p T r).cnt) :
    Hx C (roundP T.trans (addrT p)) a (fun b c =>
      Rep (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).2 (reqD r)
        (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).1 b ∧ Gl p r b ∧
      b.rc W2 = clockBits p (requestWidth r) r.fuel ∧
      (∀ y : Fin VV, 14 ≤ y.val → y.val < 40 → y.val ≠ 24 → b.env y = a.env y) ∧
      c ≤ roundCost (addrT p).ucost T.trans.ucost L) := by
  have hLN := cf.hLN
  have hLW := cf.hL
  have hq : ∀ j : Fin r.ell, tokF (addrT p) (reqD r) (reqEnv r) j.val =
      postR (qρ p (requestWidth r) r.fuel) (queryAddressExpression (requestWidth r) j.val) :=
    fun j => (addr_eq p (requestWidth r) r.fuel (reqD r) ((reqEnv r) ++ [j.val]) (by simp) (by simp [reqEnv]) j.val
      (by simp [reqEnv])).symm
  obtain ⟨q1, -⟩ := vec_stream (n := r.ell) (arity := r.ell) w (qρ p (requestWidth r) r.fuel) r.ell
    (fun bit : Fin r.ell => queryAddressExpression (requestWidth r) bit.val) (tokF (addrT p) (reqD r) (reqEnv r)) S hq
  have hqstk : (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.stk = [] := by rw [q1]; exact hS
  have htokA := vec_tok_le w (qρ p (requestWidth r) r.fuel) r.ell
    (fun bit : Fin r.ell => queryAddressExpression (requestWidth r) bit.val) (tokF (addrT p) (reqD r) (reqEnv r)) S hq
  have hqc := roundPS_cnt_ge (p := p) (T := T) (r := r) S w
  -- copy VC ELR
  refine Hx.seq' (Hx.ofHs (hs_copy C VC ELR a (by decide))) (fun a1 c1 ⟨hc1, ha1⟩ => ?_)
  subst ha1
  have kv : Keep (· = 96) (fun _ => False) (fun _ => False) a (a.set VC (a.env ELR)) := Keep.set _ VC _ rfl
  have h1' : Rep w (reqD r) S (a.set VC (a.env ELR)) := h.of_regs kv (fun y hy => by omega)
  have hg1 : Gl p r (a.set VC (a.env ELR)) := hg.keep kv (fun y hy => by omega)
  have hVC : (a.set VC (a.env ELR)).env VC = r.ell := by rw [DS.set_env_self, hg.ell]
  -- the address vector
  have hwL : w.length ≤ L := by omega
  refine Hx.seq' (vecP_spec (cf.gk w hwL) (addrT p) (reqEnv r) (by simp) (by have := (addrT_size p).1; omega)
    (addrT_size p).2 r.ell cf.okA (by have := cf.hcV; omega) S _ h1' hg1.slots hVC
    (show S.cnt + ((List.range r.ell).flatMap (tokF (addrT p) (reqD r) (reqEnv r))).length ≤ L by omega)
    (show S.stk.length + ((List.range r.ell).flatMap (tokF (addrT p) (reqD r) (reqEnv r))).length ≤ L by
      rw [hS]; simp only [List.length_nil, Nat.zero_add]; omega))
    (fun b1 c2 ⟨r1', r2', r3, r4, r5⟩ => ?_)
  have r1 : Rep w (reqD r) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1 b1 := r1'
  have r2 : b1.ram W2 = overwrite ((a.set VC (a.env ELR)).ram W2) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2 := r2'
  have hg2 : Gl p r b1 := hg1.keep r4 scr4_ok
  obtain ⟨-, -, e3⟩ := PS.vec_bounds w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S
  have hW2l : r.ell ≤ (b1.ram W2).length := by
    rw [r2]; have := overwrite_length_ge ((a.set VC (a.env ELR)).ram W2) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2; omega
  have htake : (b1.ram W2).take r.ell = (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2 := by
    rw [r2]; have := take_overwrite ((a.set VC (a.env ELR)).ram W2) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2; rwa [e3] at this
  -- the oracle gate
  refine Hx.seq' (oracleP_spec (C := C) w (reqD r) r.ell (clockBits p (requestWidth r) r.fuel) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1 b1 r1 hg2.ell hg2.cb hW2l hw1 (by omega))
    (fun b2 c3 ⟨o1, o2, o3, o4⟩ => ?_)
  rw [htake] at o1
  have hg3 : Gl p r b2 := hg2.keep o2 (fun y hy => by unfold OrT at hy; omega)
  have hlenP := putAt_length_le w (clockBits p (requestWidth r) r.fuel) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt hw1
  have hw1L : (putAt w (clockBits p (requestWidth r) r.fuel) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt).length ≤ L := by rw [hlenP]; split_ifs <;> omega
  -- the transition vector
  have ht : ∀ j : Fin (clockBits p (requestWidth r) r.fuel), tokF T.trans (reqD r) (reqEnv r) j.val =
      postR (fun i => i.val) (clockTransitionExpression p (requestWidth r) r.fuel j) := fun j => (T.trans_eq r j).symm
  have htokT := vec_tok_le (putAt w (clockBits p (requestWidth r) r.fuel) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt) (fun i : Fin ((clockBits p (requestWidth r) r.fuel) + 1) => i.val) (clockBits p (requestWidth r) r.fuel)
    (clockTransitionExpression p (requestWidth r) r.fuel) (tokF T.trans (reqD r) (reqEnv r)) ((PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.oracle (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2) ht
  have hfin' : (PS.vec (putAt w (clockBits p (requestWidth r) r.fuel) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt) (tokF T.trans (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel) ((PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.oracle (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2)).1.cnt ≤ (planPS p T r).cnt :=
    hfin
  refine Hx.mono' (vecCopy_spec cf T.trans (by have := T.trans_depth; omega) T.trans_tneed cf.okT ((PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.oracle (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2)
    (putAt w (clockBits p (requestWidth r) r.fuel) (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt) b2 o1 hg3 hw1L (by omega) (by omega)
    (by simp only [PS.oracle, hqstk, List.length_nil, Nat.zero_add]; omega)) (fun b3 c4 ⟨v1, v2, v3, v4, v5⟩ => ?_)
  refine ⟨v1, v2, v3, fun y h1 h2 h3 => ?_, ?_⟩
  · rw [v4 y h1 h2 h3, o2.env y (by unfold OrT; omega), r4.env y (by unfold Scr MachT; omega),
      DS.set_env_ne _ _ (ne_of_val (by simp; omega))]
  · have hrcw : b1.rc WM ≤ w.length := r1.base.wc
    have hmA : ((addrT p).ucost + Qc L) * ((List.range r.ell).flatMap
        (fun j => (addrT p).toks (reqD r) ((reqEnv r) ++ [j]))).length ≤ ((addrT p).ucost + Qc L) * L :=
      Nat.mul_le_mul_left _ (show _ ≤ L by
        have : ((List.range r.ell).flatMap (fun j => (addrT p).toks (reqD r) ((reqEnv r) ++ [j]))).length =
          ((List.range r.ell).flatMap (tokF (addrT p) (reqD r) (reqEnv r))).length := rfl
        omega)
    have hm2 : (12 * L + 40) * r.ell ≤ (12 * L + 40) * L := Nat.mul_le_mul_left _ (by omega)
    have hrc1 : (a.set VC (a.env ELR)).rc W2 ≤ L := hrc
    unfold roundCost
    omega

/-! ## All rounds -/

/-- The state after the input gates and the initial vector. -/
abbrev x0 (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) := startPS p T r

theorem roundPS_len (S : PS r.ell r.ell) (w : List ℕ) (hw : clockBits p (requestWidth r) r.fuel ≤ w.length) :
    (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).2.length ≤
      max w.length (clockBits p (requestWidth r) r.fuel + 1) := by
  simp only [roundPS]
  rw [overwrite_length, putAt_length_le _ _ _ hw]
  obtain ⟨-, -, e3⟩ := PS.vec_bounds (putAt w (clockBits p (requestWidth r) r.fuel)
    (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.cnt) (tokF T.trans (reqD r) (reqEnv r))
    (clockBits p (requestWidth r) r.fuel)
    ((PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).1.oracle (PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S).2)
  rw [e3]
  split_ifs <;> omega

/-- Facts about the state after `i` rounds. -/
theorem rounds_facts (i : ℕ) :
    let x := roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) i (startPS p T r)
    x.1.stk = [] ∧ clockBits p (requestWidth r) r.fuel ≤ x.2.length ∧
      x.2.length ≤ clockBits p (requestWidth r) r.fuel + r.ell + 1 := by
  intro x
  obtain ⟨s1, s2⟩ := startPS_eq p T r
  obtain ⟨e1, e2⟩ := roundsPS_eq p T r i (startPS p T r).1 (startPS p T r).2 _ (by rw [s1]) s2
  refine ⟨by rw [show x = _ from rfl, e1], e2.1, ?_⟩
  clear e1 e2
  induction i with
  | zero =>
      show (overwrite (List.range r.ell) _).length ≤ _
      rw [overwrite_length]
      obtain ⟨-, -, e3⟩ := PS.vec_bounds (List.range r.ell) (tokF T.init (reqD r) (reqEnv r))
        (clockBits p (requestWidth r) r.fuel) (initPS r.ell)
      rw [e3]; simp; omega
  | succ i ih =>
      obtain ⟨f1, f2⟩ := roundsPS_eq p T r i (startPS p T r).1 (startPS p T r).2 _ (by rw [s1]) s2
      have hx : roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + 1) (startPS p T r) =
          roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel)
            (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) i (startPS p T r)).1
            (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) i (startPS p T r)).2 :=
        roundsPS_succ _ _ _ _ _ i _
      have hl := roundPS_len (p := p) (T := T) (r := r)
        (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) i (startPS p T r)).1
        (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) i (startPS p T r)).2 f2.1
      show (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + 1)
        (startPS p T r)).2.length ≤ _
      rw [hx]
      have := ih
      omega

theorem roundsPS_cnt_mono (i j : ℕ) (x : PS r.ell r.ell × List ℕ) :
    (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) i x).1.cnt ≤
      (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + j) x).1.cnt := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [← Nat.add_assoc, roundsPS_succ]
      refine ih.trans ?_
      have := roundPS_cnt_ge (p := p) (T := T) (r := r)
        (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + j) x).1
        (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + j) x).2
      have := PS.vec_cnt_ge (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + j) x).2
        (tokF (addrT p) (reqD r) (reqEnv r)) r.ell
        (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) (i + j) x).1
      omega

theorem roundsEnd_le_plan : (roundsEnd p T r).1.cnt ≤ (planPS p T r).cnt := PS.run_cnt_ge _ _ _

/-- All `fuel` rounds. -/
def roundsP (Tt Ta : U) : St VV MM := .seq (.op (.zero RDR)) (.loop (.lt RDR FUR) (.seq (roundP Tt Ta) (.op (.inc RDR))))

theorem roundsP_spec (cf : Cfg C p T r V L) (a : DS VV MM) (h : Rep (startPS p T r).2 (reqD r) (startPS p T r).1 a)
    (hg : Gl p r a) (hrc : a.rc W2 ≤ L) :
    Hx C (roundsP T.trans (addrT p)) a (fun b c => Rep (roundsEnd p T r).2 (reqD r) (roundsEnd p T r).1 b ∧
      Gl p r b ∧ c ≤ r.fuel * (roundCost (addrT p).ucost T.trans.ucost L + 4) + 4) := by
  set cb := clockBits p (requestWidth r) r.fuel with hcb
  set RS := fun i => roundsPS p T.trans (reqD r) (reqEnv r) cb i (startPS p T r) with hRS
  refine Hx.seq' (Hx.ofHs (hs_zero C RDR a)) (fun a1 c1 ⟨hc1, ha1⟩ => ?_)
  subst ha1
  let I : ℕ → DS VV MM → ℕ → Prop := fun i b cc => Rep (RS i).2 (reqD r) (RS i).1 b ∧ Gl p r b ∧ b.rc W2 ≤ L ∧
    b.env RDR = i ∧ cc ≤ i * (roundCost (addrT p).ucost T.trans.ucost L + 4)
  have hfuel : ∀ b, Gl p r b → b.env FUR = r.fuel := fun b hb => hb.fuel
  have step : ∀ i < r.fuel, ∀ b cc, I i b cc → Cnd.eval b (.lt RDR FUR) = true ∧
      Hx C (.seq (roundP T.trans (addrT p)) (.op (.inc RDR))) b (fun d c1 => I (i + 1) d (cc + c1 + 2)) := by
    intro i hi b cc ⟨b1, b2, b3, b4, b5⟩
    refine ⟨by simp [Cnd.eval, b4, hfuel b b2, hi], ?_⟩
    obtain ⟨f1', f2', f3'⟩ := rounds_facts (p := p) (T := T) (r := r) i
    have f1 : (RS i).1.stk = [] := f1'
    have f2 : cb ≤ (RS i).2.length := f2'
    have f3 : (RS i).2.length ≤ cb + r.ell + 1 := f3'
    have hcbf : r.fuel + 1 ≤ cb := by rw [hcb]; unfold clockBits; omega
    have hLN := cf.hLN
    have hfin : (roundPS p T.trans (reqD r) (reqEnv r) cb (RS i).1 (RS i).2).1.cnt ≤ (planPS p T r).cnt := by
      have e := roundsPS_succ p T.trans (reqD r) (reqEnv r) cb i (startPS p T r)
      have m := roundsPS_cnt_mono (p := p) (T := T) (r := r) (i + 1) (r.fuel - (i + 1)) (startPS p T r)
      rw [show i + 1 + (r.fuel - (i + 1)) = r.fuel by omega, e] at m
      exact m.trans roundsEnd_le_plan
    refine Hx.seq' (roundP_spec cf (RS i).1 (RS i).2 b b1 b2 f1 f2 f3 b3 hfin) (fun d c2 ⟨d1, d2, d3, d4, d5⟩ => ?_)
    have hRd : d.env RDR = i := by rw [d4 RDR (by simp) (by simp) (by simp), b4]
    refine Hx.mono' (Hx.ofHs (hs_inc C RDR d (by rw [hRd]; have := cf.hL; omega)))
      (fun e c3 ⟨hc3, he⟩ => ?_)
    subst he
    have kR : Keep (· = 23) (fun _ => False) (fun _ => False) d (d.set RDR (d.env RDR + 1)) := Keep.set _ _ _ rfl
    refine ⟨?_, d2.keep kR (fun y hy => by omega), by rw [DS.set_rc]; omega, by rw [DS.set_env_self, hRd], ?_⟩
    · rw [show RS (i + 1) = roundPS p T.trans (reqD r) (reqEnv r) cb (RS i).1 (RS i).2 from
        roundsPS_succ p T.trans (reqD r) (reqEnv r) cb i (startPS p T r)]
      exact d1.of_regs' kR (fun y hy => by omega)
    · rw [Nat.succ_mul]; omega
  have stop : ∀ b cc, I r.fuel b cc → Cnd.eval b (.lt RDR FUR) = false := by
    intro b cc ⟨_, b2, _, b4, _⟩
    simp [Cnd.eval, b4, hfuel b b2]
  have hI0 : I 0 (a.set RDR 0) 0 := by
    have kR : Keep (· = 23) (fun _ => False) (fun _ => False) a (a.set RDR 0) := Keep.set _ _ _ rfl
    exact ⟨h.of_regs' kR (fun y hy => by omega), hg.keep kR (fun y hy => by omega), by rw [DS.set_rc]; exact hrc,
      DS.set_env_self _ _ _, by simp⟩
  refine Hx.mono' (Hx.loopAcc (show Cnd.wf (Cnd.lt RDR FUR) from (by decide : RDR ≠ FUR)) I r.fuel step stop _ hI0)
    (fun b c ⟨cf', ⟨b1, b2, _, _, b5⟩, hc⟩ => ⟨b1, b2, by omega⟩)

/-! ## The verdict -/

/-- The verdict template, its output wire popped to `OUTR`. -/
def verdictP (Tv : U) : St VV MM := .seq (compU 4 Tv) (.seq (pop XA) (.op (.copy OUTR XA)))

theorem verdictP_spec (cf : Cfg C p T r V L) (a : DS VV MM)
    (h : Rep (roundsEnd p T r).2 (reqD r) (roundsEnd p T r).1 a) (hg : Gl p r a) :
    Hx C (verdictP (verdU p)) a (fun b c =>
      b.ram NS = (OracleExpressions.requestStream p r).1.flatMap nodeRec ∧
      b.rc NS = (b.ram NS).length ∧ b.env CNT = (OracleExpressions.requestStream p r).1.length ∧
      b.env OUTR = (OracleExpressions.requestStream p r).2 ∧ Gl p r b ∧ Cst b ∧
      c ≤ ((verdU p).ucost + Qc L) * L + 12 * L + 40) := by
  obtain ⟨n1, n2, n3⟩ := plan_eq p T r
  have hLN := cf.hLN
  obtain ⟨f1, f2, f3⟩ := rounds_facts (p := p) (T := T) (r := r) r.fuel
  change (roundsEnd p T r).1.stk = [] at f1
  change clockBits p (requestWidth r) r.fuel ≤ (roundsEnd p T r).2.length at f2
  change (roundsEnd p T r).2.length ≤ clockBits p (requestWidth r) r.fuel + r.ell + 1 at f3
  set S := (roundsEnd p T r).1
  set w := (roundsEnd p T r).2
  have hSstk : S.stk = [] := f1
  have hv : (verdU p).toks (reqD r) (reqEnv r) = postR (fun i => i.val)
      (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r)) :=
    (verd_eq p (requestWidth r) r.fuel (requestWidth_three r) (reqD r) (reqEnv r) rfl).symm
  have htv := postR_length_le (n := r.ell) (arity := r.ell) (fun i : Fin (clockBits p (requestWidth r) r.fuel) => i.val)
    (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r)) S.cnt (fun i => w.getD i.val 0)
  have hrun := run_postR (n := r.ell) (arity := r.ell) w (fun i : Fin (clockBits p (requestWidth r) r.fuel) => i.val)
    (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r)) S
  have hplan : planPS p T r = S.run w ((verdU p).toks (reqD r) (reqEnv r)) := rfl
  have hcnt : S.cnt + (wireStream (n := r.ell) (arity := r.ell) S.cnt (fun i => w.getD i.val 0)
      (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r))).1.length = (planPS p T r).cnt := by
    rw [hplan, hv, hrun]
  have htok : ((verdU p).toks (reqD r) (reqEnv r)).length ≤ 2 * (wireStream (n := r.ell) (arity := r.ell) S.cnt
      (fun i => w.getD i.val 0) (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r))).1.length + 1 := by
    rw [hv]; exact htv
  refine Hx.seq' (compU_spec (cf.gk w (by omega)) (verdU p) 4 (reqEnv r) S a (by simp)
    (by have := (verdU_size p).1; omega) (verdU_size p).2 cf.okV h hg.slots (by omega)
    (by rw [hSstk]; simp only [List.length_nil, Nat.zero_add]; omega)) (fun b1 c1 ⟨r1, k1, hc1⟩ => ?_)
  rw [← hplan] at r1
  have hg1 : Gl p r b1 := hg.keep k1 (fun y hy => by unfold Scr MachT at hy; omega)
  refine Hx.seq' (Hx.ofHs (pop_spec (C := C) XA (pop_ok XA (by simp)) _ b1 r1.base.cst r1.stk
    (by rw [n2]; have := cf.hL; simp only [List.length_singleton]; omega))) (fun b2 c2 ⟨hc2, p1, p2, p3⟩ => ?_)
  refine Hx.mono' (Hx.ofHs (hs_copy C OUTR XA b2 (by decide))) (fun b3 c3 ⟨hc3, hb3⟩ => ?_)
  subst hb3
  have kO : Keep (· = 25) (fun _ => False) (fun _ => False) b2 (b2.set OUTR (b2.env XA)) := Keep.set _ _ _ rfl
  have r2 : RepB w (reqD r) (planPS p T r) b2 := r1.base.pop (by simp) p3
  refine ⟨by rw [DS.set_ram, r2.ns, n1], by rw [DS.set_rc, DS.set_ram]; exact r2.nsc,
    by rw [DS.set_env_ne _ _ (by decide), r2.cnt, n3], by rw [DS.set_env_self, p1, n2]; rfl,
    (hg1.keep p3 (fun y hy => by unfold PopT SkT at hy; simp only [XA_val] at hy; omega)).keep kO
      (fun y hy => by omega),
    kO.cst (by omega) r2.cst, ?_⟩
  have hm : ((verdU p).ucost + Qc L) * ((verdU p).toks (reqD r) (reqEnv r)).length ≤ ((verdU p).ucost + Qc L) * L :=
    Nat.mul_le_mul_left _ (by omega)
  rw [n2] at hc2
  simp at hc2
  omega

end Run

end NearCubicGates.Adapters.Compile.OraclePrint
