import SourceAdapters.ShortPCP.Machines.FLangRun
import SourceAdapters.ShortPCP.Machines.FLangEmit
import SourceAdapters.ShortPCP.Machines.WidthPrefix

/-!
# The generator's runner: `FL` programs with a callee, and the width boost

Paper: `lem:generator` and `cor:short-pcp-clock`. One ordinary program
writes the padded input and the serialized affine instance within a fixed
polynomial in `n + |bits t| + 1`; the computation itself does not test the
runtime promise.

The generator is one program of L's cell language (`Close.Cells`) with one callee: the `FL` prelude (`FL.preP`, which
reads the leading ones of the input and fixes `K = N = 2·64^L`), then compiled `FL` statements (`FL.compS`) with cell
glue between them for the calls. This module gives the two generic facts this needs:
- **transport**: a cell run that neither emits into nor calls the callee (`noK`) depends on the context only through
  the width and the input word, and keeps the callee input `kin` (`Ex.transport`, `Ex.kin_eq`); so the proved
  prelude of `FLangRun` (`pre_ok`, context `ctxOf noCallee zF inp`) runs unchanged in the generator's context
  `ctxOf K (zM …) inp` (same width `4·64^L`), with an empty `kin` (`preM_ok`);
- **the width boost**: an `FL` stage (`boostFL c`) mapping `1^L 0 ++ frame x ++ frame y` to
  `frame (1^(c + L) 0 ++ frame x ++ frame y)`, so that the generator's `K = N = 2·64^(c+L)` dominates every
  constant of the verifier `V` (`app:affine-embedding`: `C = 2^d·w` with `w ≥ c_V`; the bank has `16C` entries) on EVERY request,
  not only on long ones.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

/-! ## Programs that never touch the callee -/

/-- No `kem`, no `kcall`. -/
def noKo : Op VV MM → Bool
  | .kem _ => false
  | .kcall => false
  | _ => true

/-- No `kem`, no `kcall` anywhere in the program. -/
def noK : St VV MM → Bool
  | .op o => noKo o
  | .seq s t => noK s && noK t
  | .ite _ s t => noK s && noK t
  | .loop _ s => noK s

theorem OpEx.transport {C C' : Ctx} {o : Op VV MM} {a b : DS VV MM} {k : ℕ} (h : OpEx C o a b k)
    (hW : C'.Wd = C.Wd) (hi : C'.inp = C.inp) (ho : noKo o = true) : OpEx C' o a b k := by
  cases h with
  | zero x a => exact OpEx.zero x a
  | inc x a h => exact OpEx.inc x a (by rw [hW]; exact h)
  | add x y a h1 h2 => exact OpEx.add x y a h1 (by rw [hW]; exact h2)
  | sub x y a h1 h2 => exact OpEx.sub x y a h1 h2
  | copy x y a h => exact OpEx.copy x y a h
  | half x a => exact OpEx.half x a
  | shl x a h => exact OpEx.shl x a (by rw [hW]; exact h)
  | mul x y z a h1 h2 h3 h4 => exact OpEx.mul x y z a h1 h2 h3 (by rw [hW]; exact h4)
  | dm x y q r a h1 h2 h3 h4 h5 h6 h7 h8 => exact OpEx.dm x y q r a h1 h2 h3 h4 h5 h6 h7 (by rw [hW]; exact h8)
  | rdI x a h => rw [← hi]; exact OpEx.rdI x a (by rw [hi]; exact h)
  | bkI a h => exact OpEx.bkI a h
  | emit b a => exact OpEx.emit b a
  | rdM m x a h => exact OpEx.rdM m x a h
  | wrM m x a h => exact OpEx.wrM m x a h
  | rwM m a => exact OpEx.rwM m a
  | srtM m a h => exact OpEx.srtM m a h
  | kem b a h => simp [noKo] at ho
  | kcall s a h1 h2 => simp [noKo] at ho
  | rdK x a h => exact OpEx.rdK x a h

theorem OpEx.kin_eq {C : Ctx} {o : Op VV MM} {a b : DS VV MM} {k : ℕ} (h : OpEx C o a b k)
    (ho : noKo o = true) : b.kin = a.kin := by
  cases h <;> first | rfl | simp [noKo] at ho

/-- **Transport** of a run that never touches the callee to a context with the same width and input. -/
theorem Ex.transport {C C' : Ctx} (hW : C'.Wd = C.Wd) (hi : C'.inp = C.inp) :
    ∀ {p : St VV MM} {a b : DS VV MM} {n : ℕ}, Ex C p a b n → noK p = true → Ex C' p a b n := by
  intro p a b n h
  induction h with
  | op h => intro hp; exact Ex.op (OpEx.transport h hW hi hp)
  | seq _ _ ih1 ih2 =>
    intro hp; simp only [noK, Bool.and_eq_true] at hp; exact Ex.seq (ih1 hp.1) (ih2 hp.2)
  | iteT hc he _ ih => intro hp; simp only [noK, Bool.and_eq_true] at hp; exact Ex.iteT hc he (ih hp.1)
  | iteF hc he _ ih => intro hp; simp only [noK, Bool.and_eq_true] at hp; exact Ex.iteF hc he (ih hp.2)
  | loopF hc he => intro _; exact Ex.loopF hc he
  | loopT hc he _ _ ih1 ih2 => intro hp; exact Ex.loopT hc he (ih1 hp) (ih2 hp)
  | mono _ hle ih => intro hp; exact Ex.mono (ih hp) hle

/-- A run that never touches the callee keeps `kin`. -/
theorem Ex.kin_eq {C : Ctx} :
    ∀ {p : St VV MM} {a b : DS VV MM} {n : ℕ}, Ex C p a b n → noK p = true → b.kin = a.kin := by
  intro p a b n h
  induction h with
  | op h => intro hp; exact OpEx.kin_eq h hp
  | seq _ _ ih1 ih2 =>
    intro hp; simp only [noK, Bool.and_eq_true] at hp; exact (ih2 hp.2).trans (ih1 hp.1)
  | iteT _ _ _ ih => intro hp; simp only [noK, Bool.and_eq_true] at hp; exact ih hp.1
  | iteF _ _ _ ih => intro hp; simp only [noK, Bool.and_eq_true] at hp; exact ih hp.2
  | loopF _ _ => intro _; rfl
  | loopT _ _ _ _ ih1 ih2 => intro hp; exact (ih2 hp).trans (ih1 hp)
  | mono _ _ ih => intro hp; exact ih hp

/-! ## The generator's context and its prelude -/

/-- The size parameters of the generator's run: width `4·64^L` (as `FLangRun.zF`), call room `a2·2^(c2·L)`, call
budget `a3·2^(c3·L)`. -/
def zM (a2 c2 a3 c3 : ℕ) : Sz := ⟨4, 6, a2, c2, a3, c3⟩

theorem zM_W (a2 c2 a3 c3 : ℕ) (K : Callee) (inp : List Bool) :
    (ctxOf K (zM a2 c2 a3 c3) inp).Wd = (ctxOf noCallee zF inp).Wd := rfl

theorem noK_preP : noK FL.preP = true := rfl

/-- **The prelude in the generator's context**: the fixed registers of `globOf inp`, the variables zero, no output,
input position after the prefix, and an empty callee input. -/
theorem preM_ok (K : Callee) (a2 c2 a3 c3 : ℕ) (inp : List Bool) (hlt : leadOnes inp < inp.length) :
    Hs (ctxOf K (zM a2 c2 a3 c3) inp) FL.preP (a0 : DS VV MM) (preCost inp)
      (fun b => PreOk inp b ∧ b.kin = []) := by
  obtain ⟨b, n, hx, hn, hb⟩ := pre_ok inp hlt
  exact ⟨b, n, Ex.transport (zM_W a2 c2 a3 c3 K inp) rfl hx noK_preP, hn, hb,
    (Ex.kin_eq hx noK_preP).trans rfl⟩

/-- The run constants fit the generator's context. -/
theorem gokM (K : Callee) (a2 c2 a3 c3 : ℕ) (inp : List Bool) (h1 : 1 ≤ leadOnes inp) :
    GOk (ctxOf K (zM a2 c2 a3 c3) inp) (globOf inp) := gok inp h1

/-! ## The width boost -/

/-- `c` framed ones. -/
def onesFL : ℕ → S
  | 0 => .skip
  | c + 1 => .seq (emitF (.k 1)) (onesFL c)

theorem onesFL_spec {G : Glob} (h1 : 1 ≤ G.cap) : ∀ (c : ℕ) (s : FS),
    Em [] s (evalS G (onesFL c) s) (List.replicate c true)
  | 0, s => ⟨fun _ _ => rfl, by simp [onesFL, dbl], rfl, rfl, rfl, rfl⟩
  | c + 1, s => by
    have e1 := emitF_spec (G := G) s (.k 1) [] h1
    have e2 := onesFL_spec h1 c (evalS G (emitF (.k 1)) s)
    have hk : evalE G s (.k 1) = 1 := min_eq_left h1
    rw [hk] at e1
    have := e1.trans e2
    simpa [onesFL, List.replicate_succ] using this

/-- **The boost stage**: `1^L 0 ++ frame x ++ frame y ↦ frame (1^(c+L) 0 ++ frame x ++ frame y)` (read from position
`L + 1`). -/
def boostFL (c : ℕ) : S :=
  .seq (onesFL c) (.seq prefE (.seq rdFrame (.seq (copyE 0 1) (.seq rdFrame (.seq (copyE 0 1) (.emit (.k 0)))))))

/-- The boosted word. -/
def boostWord (c : ℕ) (w : List Bool) : List Bool := List.replicate (c + Nat.size w.length) true ++ false :: w

theorem frame_eq_dbl (w : List Bool) : frame w = dbl w ++ [false] := frame_dbl w

theorem two_pow_size_gt (n : ℕ) : n < 2 ^ Nat.size n := Nat.lt_size_self n

theorem drop_prefix_word (L : ℕ) (w : List Bool) : (List.replicate L true ++ false :: w).drop (L + 1) = w := by
  rw [show List.replicate L true ++ false :: w = (List.replicate L true ++ [false]) ++ w by simp]
  exact List.drop_left' (by simp)

/-- The run constants of a prefixed word `1^L 0 ++ w` with `L = size |w|`. -/
theorem glob_prefix (w : List Bool) (hw : 1 ≤ w.length) :
    let G := globOf (Time.prefixWord w)
    let L := Nat.size w.length
    leadOnes (Time.prefixWord w) = L ∧ G.K = 2 * 64 ^ L ∧ G.N = 2 * 64 ^ L ∧ w.length < 2 ^ L ∧
      2 ^ L ≤ 64 ^ L ∧ G.cap + 1 = 2 ^ G.K ∧ 1 ≤ L ∧ 128 ≤ G.K := by
  intro G L
  have hlead : leadOnes (Time.prefixWord w) = L := NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _
  have hK : G.K = 2 * 64 ^ L := by show kOf (Time.prefixWord w) = _; unfold kOf; rw [hlead]
  have hL1 : 1 ≤ L := Nat.size_pos.mpr (by omega)
  have h64 : 64 ≤ 64 ^ L := by
    calc 64 = 64 ^ 1 := by norm_num
      _ ≤ 64 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
  exact ⟨hlead, hK, hK, Nat.lt_size_self _, Nat.pow_le_pow_left (by norm_num) L, cap_add G, hL1, by omega⟩

/-- The boost stage's semantics. -/
theorem boostFL_spec (c : ℕ) (x y : List Bool) :
    (evalS (globOf (Time.prefixWord (frame x ++ frame y))) (boostFL c)
        (FL.s0 (Time.prefixWord (frame x ++ frame y)))).out = frame (boostWord c (frame x ++ frame y)) ∧
      (evalS (globOf (Time.prefixWord (frame x ++ frame y))) (boostFL c)
        (FL.s0 (Time.prefixWord (frame x ++ frame y)))).bad = false := by
  generalize hw : frame x ++ frame y = w
  have hwl : 1 ≤ w.length := by rw [← hw]; simp [FL.frame_len]; omega
  have hxl : x.length < w.length := by rw [← hw]; simp [FL.frame_len]; omega
  have hyl : y.length < w.length := by rw [← hw]; simp [FL.frame_len]; omega
  obtain ⟨hlead, hK, hN, hwL, h64, hcapK, hL1, hK128⟩ := glob_prefix w hwl
  generalize hinp : Time.prefixWord w = inp at hlead hK hN hcapK hK128
  generalize hG : globOf inp = G at hK hN hcapK hK128
  generalize hL : Nat.size w.length = L at hlead hK hN hwL h64 hL1
  have hGinp : G.inp = List.replicate L true ++ false :: w := by
    rw [← hG, ← hinp, ← hL]; rfl
  have hcap64 : 64 ≤ G.cap := by
    have : 2 * 64 ^ L < 2 ^ G.K := by rw [hK]; exact Nat.lt_two_pow_self
    omega
  have hs0ip : (FL.s0 inp).ip = L + 1 := by simp [FL.s0, hlead]
  have hL2 : L < 2 ^ L := Nat.lt_two_pow_self
  have hKlt : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have hcapw : ∀ u : List Bool, u.length < w.length → 2 * 2 ^ u.length ≤ G.cap := by
    intro u hu
    have h1 : u.length + 1 < G.K := by rw [hK]; omega
    have h2 : 2 ^ (u.length + 1) < 2 ^ G.K := Nat.pow_lt_pow_right (by norm_num) h1
    rw [pow_succ] at h2
    omega
  -- step 1: the extra ones
  have e1 := onesFL_spec (G := G) (by omega) c (FL.s0 inp)
  generalize hs1 : evalS G (onesFL c) (FL.s0 inp) = s1 at e1
  -- step 2: the prefix `1^L 0`
  have e2 := prefE_spec (G := G) s1 L hK (by omega) (by omega) hcap64
  generalize hs2 : evalS G prefE s1 = s2 at e2
  have hs2ip : s2.ip = L + 1 := by rw [e2.ip, e1.ip, hs0ip]
  -- step 3: `frame x`
  have hd2 : G.inp.drop s2.ip = frame x ++ (frame y ++ []) := by
    rw [hs2ip, hGinp, drop_prefix_word, ← hw, List.append_nil]
  obtain ⟨r3a, r3b, r3c, r3W⟩ := rdFrame_spec G s2 x (frame y ++ []) hd2 (hcapw x hxl) (by omega)
  generalize hs3 : evalS G rdFrame s2 = s3 at r3a r3b r3c r3W
  have e4 := copyE_spec (G := G) s3 0 1 x r3a r3b (by decide) (by omega) (by omega)
  generalize hs4 : evalS G (copyE 0 1) s3 = s4 at e4
  have hs4ip : s4.ip = (L + 1) + (2 * x.length + 1) := by rw [e4.ip, r3c, hs2ip]; ring
  -- step 4: `frame y`
  have hd4 : G.inp.drop s4.ip = frame y ++ [] := by
    rw [hs4ip, hGinp, ← List.drop_drop, drop_prefix_word, ← hw, List.append_nil,
      List.drop_left' (by simp [FL.frame_len])]
  obtain ⟨r5a, r5b, r5c, r5W⟩ := rdFrame_spec G s4 y [] hd4 (hcapw y hyl) (by omega)
  generalize hs5 : evalS G rdFrame s4 = s5 at r5a r5b r5c r5W
  have e6 := copyE_spec (G := G) s5 0 1 y r5a r5b (by decide) (by omega) (by omega)
  generalize hs6 : evalS G (copyE 0 1) s5 = s6 at e6
  have ht : evalS G (boostFL c) (FL.s0 inp) = { s6 with out := s6.out ++ [evalE G s6 (.k 0) != 0] } := by
    rw [← hs6, ← hs5, ← hs4, ← hs3, ← hs2, ← hs1]; rfl
  have h0 : evalE G s6 (.k 0) = 0 := Nat.zero_min _
  rw [ht, h0]
  have hbad : s6.bad = false := by
    rw [e6.bad, r5W.bad, e4.bad, r3W.bad, e2.bad, e1.bad]; rfl
  refine ⟨?_, hbad⟩
  show s6.out ++ [false] = _
  rw [e6.out, r5W.out, e4.out, r3W.out, e2.out, e1.out]
  have hout0 : (FL.s0 inp).out = [] := rfl
  rw [hout0, frame_eq_dbl (boostWord c w), boostWord, hL, ← hw]
  simp only [List.replicate_add, dbl_append, List.nil_append, List.append_assoc, frame_eq_dbl x, frame_eq_dbl y]
  simp [dbl]

end NearCubicGates.Adapters.RAMACSP.Gen
