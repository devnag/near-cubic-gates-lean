import SourceAdapters.ShortPCP.Machines.FLangMainD

/-!
# Single-run time, machine layer 33: emitting framed words

The query half (stage 2 of `Time.singleRunTime_of_stages`) outputs `frame (readerWord s L xs w)`; an `FL` program
emits a framed word bit by bit: `frame w = dbl w ++ [0]` with `dbl w` = `1 b` per bit `b`. `Em W s t w`: the run from
`s` to `t` appended `dbl w` to the output and changed only the variables `W`. The address entries
`1 1 0 0 ++ frame (binary L a)` of the reader word (proof of `thm:short-pcp-ours`) are emitted by `entryE`, the `f` entries of one
proof element `k` (bits `k·f, …, k·f + f − 1`, proof of `thm:short-pcp-ours`) by `elemE`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable {G : Glob}

/-- Each bit `b` as `1 b`. -/
def dbl (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

theorem dbl_append (u w : List Bool) : dbl (u ++ w) = dbl u ++ dbl w := by simp [dbl]

theorem frame_dbl : ∀ w : List Bool, frame w = dbl w ++ [false]
  | [] => rfl
  | b :: w => by simp [frame, dbl, frame_dbl w]

/-- The run appended `dbl w` to the output and changed only `W`. -/
structure Em (W : List Var) (s t : FS) (w : List Bool) : Prop where
  env : ∀ j, j ∉ W → t.env j = s.env j
  out : t.out = s.out ++ dbl w
  fl : t.fl = s.fl
  fp : t.fp = s.fp
  ip : t.ip = s.ip
  bad : t.bad = s.bad

theorem Em.trans {W : List Var} {s t u : FS} {w w' : List Bool} (h1 : Em W s t w) (h2 : Em W t u w') :
    Em W s u (w ++ w') :=
  ⟨fun j hj => (h2.env j hj).trans (h1.env j hj), by rw [h2.out, h1.out, dbl_append, List.append_assoc],
    h2.fl.trans h1.fl, h2.fp.trans h1.fp, h2.ip.trans h1.ip, h2.bad.trans h1.bad⟩

theorem Em.mono {W W' : List Var} {s t : FS} {w : List Bool} (h : Em W s t w) (hW : ∀ x ∈ W, x ∈ W') : Em W' s t w :=
  ⟨fun j hj => h.env j (fun h' => hj (hW j h')), h.out, h.fl, h.fp, h.ip, h.bad⟩

theorem Em.wr {W : List Var} {s t : FS} {w : List Bool} (h : Em W s t w) (hw : w = []) : Wr W s t :=
  ⟨h.env, by rw [h.out, hw]; simp [dbl], h.fl, h.fp, h.bad⟩

theorem Em.setv (s : FS) {W : List Var} {i : Var} (hi : i ∈ W) (v : ℕ) : Em W s (s.setv i v) [] :=
  ⟨fun j hj => by simp [Function.update_of_ne (show j ≠ i from fun h => hj (h ▸ hi))], by simp [dbl], rfl, rfl, rfl,
    rfl⟩

theorem evalE_out (s : FS) (o : List Bool) : ∀ e : E, evalE G { s with out := o } e = evalE G s e := by
  intro e; induction e <;> simp only [evalE, *]

/-- Emit the framed bit `e ≠ 0`. -/
def emitF (e : E) : S := .seq (.emit (.k 1)) (.emit e)

theorem emitF_spec (s : FS) (e : E) (W : List Var) (h1 : 1 ≤ G.cap) :
    Em W s (evalS G (emitF e) s) [evalE G s e != 0] := by
  have : min 1 G.cap = 1 := min_eq_left h1
  refine ⟨fun j _ => rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [emitF, evalS_seq, evalS_emit, evalE_out, evalE, this, dbl]; simp

theorem emitF_env (s : FS) (e : E) : (evalS G (emitF e) s).env = s.env := rfl

/-- The bits of `binary L a`, each framed (`L` in `2`, loop variable `8`). -/
def bitsE (a : E) : S := .loop 8 (.v 2) (.seq (emitF (.k 1)) (emitF (.md (.shr a (.v 8)) (.k 2))))

theorem binary_getD (L n j : ℕ) (hj : j < L) : (binary L n).getD j false = (n / 2 ^ j % 2 == 1) := by
  induction L generalizing n j with
  | zero => omega
  | succ L ih =>
    rcases j with _ | j
    · simp [binary]
    · simp only [binary, List.getD_cons_succ]; rw [ih (n / 2) j (by omega), Nat.div_div_eq_div_mul, ← pow_succ']

theorem binary_eq_map (L n : ℕ) : binary L n = (List.range L).map fun j => (n / 2 ^ j % 2 == 1) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have := binary_getD L n j (by simpa using h1)
  rw [List.getD_eq_getElem _ _ h1] at this
  simp [this]

theorem bitsE_spec (s : FS) (a : E) (L av : ℕ) (h2 : s.env 2 = L)
    (hL : L ≤ G.N) (ha : ∀ t : FS, (∀ j, j ≠ 8 → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t a = av)
    (h1 : 2 ≤ G.cap) :
    Em [8] s (evalS G (bitsE a) s) (dbl (binary L av)) := by
  have hm : min (evalE G s (.v 2)) G.N = L := by rw [eE_v, h2]; exact min_eq_left hL
  have hl := loop_inv G (i := 8) (n := .v 2) (body := .seq (emitF (.k 1)) (emitF (.md (.shr a (.v 8)) (.k 2))))
    (s := s) (fun j t => Em [8] s t (dbl ((List.range j).map fun j => (av / 2 ^ j % 2 == 1))))
    ⟨fun _ _ => rfl, by simp [dbl], rfl, rfl, rfl, rfl⟩ (by
      intro j hj t ht
      have e0 : Em [8] t (t.setv 8 j) [] := Em.setv t (by simp) j
      have e1 := emitF_spec (G := G) (t.setv 8 j) (.k 1) [8] (by omega)
      generalize hu1 : evalS G (emitF (.k 1)) (t.setv 8 j) = u1 at e1
      have hv : evalE G u1 (.md (.shr a (.v 8)) (.k 2)) = av / 2 ^ j % 2 := by
        have hs : ∀ jj, jj ≠ 8 → u1.env jj = s.env jj := by
          intro jj hjj
          rw [e1.env jj (by simp [hjj]), e0.env jj (by simp [hjj]), ht.env jj (by simp [hjj])]
        have ha' := ha u1 hs (by rw [e1.fl, e0.fl, ht.fl]) (by rw [e1.fp, e0.fp, ht.fp])
        have h8 : u1.env 8 = j := by rw [← hu1, emitF_env]; simp
        rw [eE_md (eE_shr ha' (eE_v 8 |>.trans h8)) (eE_k (by omega))]
      have e2 := emitF_spec (G := G) u1 (.md (.shr a (.v 8)) (.k 2)) [8] (by omega)
      have := (ht.trans (e0.trans (e1.trans e2)))
      have hk1 : evalE G (t.setv 8 j) (.k 1) = 1 := min_eq_left (by omega)
      rw [hv, hk1] at this
      show Em [8] s (evalS G (emitF (.md (.shr a (.v 8)) (.k 2))) (evalS G (emitF (.k 1)) (t.setv 8 j))) _
      rw [hu1]
      convert this using 1
      rw [List.range_succ, List.map_append, dbl_append]
      simp only [List.nil_append, List.map_singleton]
      have hb : (av / 2 ^ j % 2 != 0) = (av / 2 ^ j % 2 == 1) := by
        rcases Nat.mod_two_eq_zero_or_one (av / 2 ^ j) with h | h <;> simp [h]
      rw [hb]; simp [dbl])
  rw [hm, ← binary_eq_map] at hl
  exact hl

/-- One address entry `1 1 0 0 ++ frame (binary L a)` of the reader word. -/
def entryE (a : E) : S :=
  .seq (emitF (.k 1)) (.seq (emitF (.k 1)) (.seq (emitF (.k 0)) (.seq (emitF (.k 0)) (.seq (bitsE a) (emitF (.k 0))))))

/-- The reader word's entry of the address `a`. -/
def entryW (L a : ℕ) : List Bool := true :: true :: false :: false :: frame (binary L a)

theorem entryE_spec (s : FS) (a : E) (L av : ℕ) (h2 : s.env 2 = L)
    (hL : L ≤ G.N) (ha : ∀ t : FS, (∀ j, j ≠ 8 → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t a = av)
    (h1 : 2 ≤ G.cap) :
    Em [8] s (evalS G (entryE a) s) (entryW L av) := by
  have c1 : min 1 G.cap = 1 := min_eq_left (by omega)
  have c0 : min 0 G.cap = 0 := Nat.zero_min _
  have f1 := emitF_spec (G := G) s (.k 1) [8] (by omega)
  generalize hu1 : evalS G (emitF (.k 1)) s = u1 at f1
  have f2 := emitF_spec (G := G) u1 (.k 1) [8] (by omega)
  generalize hu2 : evalS G (emitF (.k 1)) u1 = u2 at f2
  have f3 := emitF_spec (G := G) u2 (.k 0) [8] (by omega)
  generalize hu3 : evalS G (emitF (.k 0)) u2 = u3 at f3
  have f4 := emitF_spec (G := G) u3 (.k 0) [8] (by omega)
  generalize hu4 : evalS G (emitF (.k 0)) u3 = u4 at f4
  have g := (f1.trans (f2.trans (f3.trans f4)))
  have f5 := bitsE_spec (G := G) u4 a L av (by rw [g.env 2 (by simp), h2]) hL (fun t ht hfl hfp => ha t
    (fun j hj => (ht j hj).trans (g.env j (by simp [hj]))) (hfl.trans g.fl) (hfp.trans g.fp)) h1
  generalize hu5 : evalS G (bitsE a) u4 = u5 at f5
  have f6 := emitF_spec (G := G) u5 (.k 0) [8] (by omega)
  have ht : evalS G (entryE a) s = evalS G (emitF (.k 0)) u5 := by
    simp only [entryE, evalS_seq]; rw [hu1, hu2, hu3, hu4, hu5]
  rw [ht]
  convert g.trans (f5.trans f6) using 1
  simp only [evalE, c1, c0, entryW, frame_dbl]
  simp

/-- **Loops that emit**: pass `j` emits `g j`. -/
theorem Em_loop (i : Var) (n : E) (body : S) (W : List Var) (hi : i ∈ W) (s : FS) (m : ℕ)
    (hm : min (evalE G s n) G.N = m) (Inv : FS → Prop) (hInv : Inv s) (g : ℕ → List Bool)
    (hstep : ∀ j < m, ∀ t, Inv t → Em W s t ((List.range j).flatMap g) →
      Inv (evalS G body (t.setv i j)) ∧ Em W (t.setv i j) (evalS G body (t.setv i j)) (g j)) :
    Inv (evalS G (.loop i n body) s) ∧ Em W s (evalS G (.loop i n body) s) ((List.range m).flatMap g) := by
  have := loop_inv G (i := i) (n := n) (body := body) (s := s)
    (fun j t => Inv t ∧ Em W s t ((List.range j).flatMap g)) ⟨hInv, ⟨fun _ _ => rfl, by simp [dbl], rfl, rfl, rfl, rfl⟩⟩
    (by
      rw [hm]
      rintro j hj t ⟨ti, te⟩
      obtain ⟨a, b⟩ := hstep j hj t ti te
      refine ⟨a, ?_⟩
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact te.trans ((Em.setv t hi j).trans b))
  rw [hm] at this; exact this

/-- The `f` entries of proof element `13` (bits `13·f + b`, `b < f`). -/
def elemE : S := .loop 5 (.v 23) (entryE (.add (.mul (.v 13) (.v 23)) (.v 5)))

/-- The entries of element `k`. -/
def elemW (L f k : ℕ) : List Bool := (List.range f).flatMap fun b => entryW L (k * f + b)

theorem elemE_spec (s : FS) (L f k : ℕ) (h2 : s.env 2 = L) (h13 : s.env 13 = k) (h23 : s.env 23 = f)
    (hL : L ≤ G.N) (hf : f ≤ G.N) (hk : (k + 1) * f ≤ G.cap) (h1 : 2 ≤ G.cap) :
    Em [5, 8] s (evalS G elemE s) (elemW L f k) := by
  have hm : min (evalE G s (.v 23)) G.N = f := by rw [eE_v, h23]; exact min_eq_left hf
  exact (Em_loop 5 (.v 23) _ [5, 8] (by simp) s f hm (fun _ => True) trivial _ (by
    intro j hj t _ te
    refine ⟨trivial, ?_⟩
    have hb : ∀ jj, jj ≠ 5 → jj ≠ 8 → t.env jj = s.env jj := fun jj h5 h8 => te.env jj (by simp [h5, h8])
    have := entryE_spec (G := G) (t.setv 5 j) (.add (.mul (.v 13) (.v 23)) (.v 5)) L (k * f + j)
      (by simp [hb 2 (by decide) (by decide), h2]) hL (by
        intro u hu _ _
        have e13 : u.env 13 = k := by rw [hu 13 (by decide)]; simp [hb 13 (by decide) (by decide), h13]
        have e23 : u.env 23 = f := by rw [hu 23 (by decide)]; simp [hb 23 (by decide) (by decide), h23]
        have e5 : u.env 5 = j := by rw [hu 5 (by decide)]; simp
        have : k * f + j ≤ G.cap := by
          have : k * f + f = (k + 1) * f := by ring
          omega
        exact eE_add (eE_mul (eE_v 13 |>.trans e13) (eE_v 23 |>.trans e23) (by omega)) (eE_v 5 |>.trans e5) this) h1
    exact this.mono (by simp))).2

/-- Emit `frame` of the low `n` bits of `a` (`n` in `nv`; loop variable `5`). -/
def copyE (a : Var) (nv : Var) : S :=
  .seq (.loop 5 (.v nv) (.seq (emitF (.k 1)) (emitF (.md (.shr (.v a) (.v 5)) (.k 2))))) (emitF (.k 0))

theorem bits_of_bitsValue (u : List Bool) : (List.range u.length).map (fun j => bitsValue u / 2 ^ j % 2 == 1) = u := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have := testBit_bitsValue u j
  rw [List.getD_eq_getElem _ _ h2] at this
  rw [this]; cases u[j] <;> rfl

theorem copyE_spec (s : FS) (a nv : Var) (u : List Bool) (ha : s.env a = bitsValue u) (hn : s.env nv = u.length)
    (ha5 : a ≠ 5) (hN : u.length ≤ G.N) (h1 : 2 ≤ G.cap) :
    Em [5] s (evalS G (copyE a nv) s) (frame u) := by
  have hm : min (evalE G s (.v nv)) G.N = u.length := by rw [eE_v, hn]; exact min_eq_left hN
  have hl := (Em_loop 5 (.v nv) (.seq (emitF (.k 1)) (emitF (.md (.shr (.v a) (.v 5)) (.k 2)))) [5] (by simp) s
    u.length hm (fun _ => True) trivial (fun j => [true, bitsValue u / 2 ^ j % 2 == 1]) (by
      intro j hj t _ te
      refine ⟨trivial, ?_⟩
      have e1 := emitF_spec (G := G) (t.setv 5 j) (.k 1) [5] (by omega)
      have e2 := emitF_spec (G := G) (evalS G (emitF (.k 1)) (t.setv 5 j)) (.md (.shr (.v a) (.v 5)) (.k 2)) [5]
        (by omega)
      have hv : evalE G (evalS G (emitF (.k 1)) (t.setv 5 j)) (.md (.shr (.v a) (.v 5)) (.k 2)) =
          bitsValue u / 2 ^ j % 2 := by
        simp only [evalE, emitF_env, FS.setv_env, Function.update_self, Function.update_of_ne ha5]
        rw [te.env a (by simp [ha5]), ha, min_eq_left (show 2 ≤ G.cap from h1)]
      have hk1 : evalE G (t.setv 5 j) (.k 1) = 1 := min_eq_left (by omega)
      have := e1.trans e2
      rw [hv, hk1] at this
      have hb : (bitsValue u / 2 ^ j % 2 != 0) = (bitsValue u / 2 ^ j % 2 == 1) := by
        rcases Nat.mod_two_eq_zero_or_one (bitsValue u / 2 ^ j) with h | h <;> simp [h]
      rw [hb] at this
      exact this)).2
  have e3 := emitF_spec (G := G) (evalS G (.loop 5 (.v nv) (.seq (emitF (.k 1)) (emitF (.md (.shr (.v a) (.v 5))
    (.k 2))))) s) (.k 0) [5] (by omega)
  have := hl.trans e3
  have ht : evalS G (copyE a nv) s = evalS G (emitF (.k 0)) (evalS G (.loop 5 (.v nv) (.seq (emitF (.k 1))
    (emitF (.md (.shr (.v a) (.v 5)) (.k 2))))) s) := rfl
  rw [ht]
  convert this using 1
  rw [frame_dbl]
  have e : (List.range u.length).flatMap (fun j => [true, bitsValue u / 2 ^ j % 2 == 1]) =
      dbl ((List.range u.length).map fun j => bitsValue u / 2 ^ j % 2 == 1) := by
    simp [dbl, List.flatMap_map]
  rw [e, bits_of_bitsValue, show evalE G _ (.k 0) = 0 from Nat.zero_min _]
  simp [dbl]

/-- `7 := n` for the clamp exponent `K = 2·64^n`. -/
def sizeP : S :=
  .seq (.set 8 (.div .gk (.k 2))) (.seq (.set 7 (.k 0))
    (.whl (.lt (.k 1) (.v 8)) (.seq (.set 8 (.div (.v 8) (.k 64))) (.set 7 (.add (.v 7) (.k 1))))))

/-- The width prefix `1^n 0` of the reader word. -/
def prefE : S := .seq sizeP (.seq (.loop 3 (.v 7) (emitF (.k 1))) (emitF (.k 0)))

theorem range_flatMap_true (n : ℕ) : (List.range n).flatMap (fun _ => [true]) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; rfl

theorem prefE_spec (s : FS) (n : ℕ) (hK : G.K = 2 * 64 ^ n) (hN : n ≤ G.N) (hn : n + 2 ≤ G.cap)
    (hc : 64 ≤ G.cap) :
    Em [3, 7, 8] s (evalS G prefE s) (List.replicate n true ++ [false]) := by
  have c0 : min 0 G.cap = 0 := Nat.zero_min _
  have c1 : min 1 G.cap = 1 := min_eq_left (by omega)
  have c2 : min 2 G.cap = 2 := min_eq_left (by omega)
  have c64 : min 64 G.cap = 64 := min_eq_left hc
  have hp : 0 < 64 ^ n := by positivity
  set s1 := (s.setv 8 (64 ^ n)).setv 7 0 with hs1
  have e1 : Em [3, 7, 8] s s1 [] := by
    have := (Em.setv (W := [3, 7, 8]) s (i := 8) (by simp) (64 ^ n)).trans
      (Em.setv (W := [3, 7, 8]) (s.setv 8 (64 ^ n)) (i := 7) (by simp) 0)
    simpa using this
  have hw := whl_inv G (c := .lt (.k 1) (.v 8)) (body := .seq (.set 8 (.div (.v 8) (.k 64))) (.set 7 (.add (.v 7) (.k 1))))
    (fun t => t.env 7 ≤ n ∧ t.env 8 = 64 ^ (n - t.env 7) ∧ Em [3, 7, 8] s t []) (fun t => n - t.env 7) s1
    ⟨by simp [s1], by simp [s1], e1⟩ (by simp [s1]; omega) (by
      rintro t ⟨t7, t8, te⟩ hc'
      have hi : t.env 7 < n := by
        by_contra h
        have : n - t.env 7 = 0 := by omega
        apply hc'; simp only [evalE, c1, t8, this, pow_zero]; simp
      have hd : 64 ^ (n - t.env 7) / 64 = 64 ^ (n - (t.env 7 + 1)) := by
        rw [show n - t.env 7 = (n - (t.env 7 + 1)) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      have ev8 : evalE G t (.div (.v 8) (.k 64)) = 64 ^ (n - (t.env 7 + 1)) := by
        simp only [evalE, c64, t8, hd]
      have ev7 : evalE G (t.setv 8 (64 ^ (n - (t.env 7 + 1)))) (.add (.v 7) (.k 1)) = t.env 7 + 1 := by
        simp only [evalE, c1, FS.setv_env, Function.update_of_ne (by decide : (7 : Var) ≠ 8)]
        exact min_eq_left (by omega)
      simp only [evalS_seq, evalS_set, ev8, ev7]
      refine ⟨⟨by simp; omega, by simp, ?_⟩, by simp; omega⟩
      have := (te.trans (Em.setv (W := [3, 7, 8]) t (i := 8) (by simp) (64 ^ (n - (t.env 7 + 1))))).trans
        (Em.setv (W := [3, 7, 8]) (t.setv 8 (64 ^ (n - (t.env 7 + 1)))) (i := 7) (by simp) (t.env 7 + 1))
      simpa using this)
  obtain ⟨⟨w7, w8, we⟩, wc⟩ := hw
  generalize hs2 : evalS G (.whl (.lt (.k 1) (.v 8)) (.seq (.set 8 (.div (.v 8) (.k 64)))
      (.set 7 (.add (.v 7) (.k 1))))) s1 = s2 at w7 w8 we wc
  have hn7 : s2.env 7 = n := by
    by_contra h
    have h1 : 1 < 64 ^ (n - s2.env 7) := Nat.one_lt_pow (by omega) (by norm_num)
    have : evalE G s2 (.lt (.k 1) (.v 8)) = 1 := by simp only [evalE, c1, w8, if_pos h1]
    rw [this] at wc; exact absurd wc one_ne_zero
  have hl := (Em_loop 3 (.v 7) (emitF (.k 1)) [3, 7, 8] (by simp) s2 n (by rw [eE_v, hn7]; exact min_eq_left hN)
    (fun _ => True) trivial (fun _ => [true]) (fun j _ t _ _ => ⟨trivial, by
      have := emitF_spec (G := G) (t.setv 3 j) (.k 1) [3, 7, 8] (by omega)
      simpa [evalE, c1] using this⟩)).2
  have e3 := emitF_spec (G := G) (evalS G (.loop 3 (.v 7) (emitF (.k 1))) s2) (.k 0) [3, 7, 8] (by omega)
  have ht : evalS G prefE s = evalS G (emitF (.k 0)) (evalS G (.loop 3 (.v 7) (emitF (.k 1))) s2) := by
    show evalS G (.seq sizeP _) s = _
    simp only [sizeP, evalS_seq, evalS_set]
    rw [show evalE G s (.div .gk (.k 2)) = 64 ^ n by simp only [evalE, c2, hK]; omega,
      show evalE G (s.setv 8 (64 ^ n)) (.k 0) = 0 from c0, ← hs1, hs2]
  rw [ht]
  have := (we.trans hl).trans e3
  simpa [range_flatMap_true, evalE, c0] using this

end NearCubicGates.Adapters.ShortPCP.Machines.FL
