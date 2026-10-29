import SourceAdapters.Compile.OraclePrintCompile
import SourceAdapters.Compile.OraclePrintStream

/-!
# The vector loop of the oracle circuit printer

proof of `thm:short-pcp-ours`: each vector of formulas (initial formulas, query address bits, transition formulas) is compiled member
by member on the current wire map. `vecP T` runs the template `T` once per member index `j < VC` (the index in slot
`4`, the template at level `5`), moves each output wire off the stack and writes it to store `W2` from position `0`.
`vecP_spec`: exactly `PS.vec` of the template's tokens (hence `vectorStream` by `vec_stream`), the outputs
in `W2`, cost linear in the tokens.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicGates.Close.Cells

set_option autoImplicit false

/-- The next wire map. -/
def W2 : Fin MM := ⟨4, by decide⟩
/-- The member count. -/
def VC : Fin VV := ⟨96, by decide⟩

@[simp] theorem W2_val : W2.val = 4 := rfl
@[simp] theorem VC_val : VC.val = 96 := rfl

/-- Write `new` over the front of `old`. -/
def overwrite (old new : List ℕ) : List ℕ := new ++ old.drop new.length

theorem putAt_overwrite (old new : List ℕ) (v : ℕ) :
    putAt (overwrite old new) new.length v = overwrite old (new ++ [v]) := by
  unfold putAt overwrite
  split_ifs with h
  · simp only [List.length_append, List.length_singleton]
    rw [List.set_append_right _ _ (by omega), Nat.sub_self]
    have hd : old.drop new.length ≠ [] := by
      intro e; simp [e] at h
    obtain ⟨x, rest, hx⟩ := List.exists_cons_of_ne_nil hd
    rw [hx]
    have : old.drop (new.length + 1) = rest := by
      rw [← List.drop_drop, hx]; rfl
    simp [this]
  · simp only [List.length_append, List.length_singleton] at h ⊢
    have h1 : old.drop new.length = [] := List.drop_eq_nil_of_le (by simp at h; omega)
    have h2 : old.drop (new.length + 1) = [] := List.drop_eq_nil_of_le (by simp at h; omega)
    simp [h1, h2]

theorem overwrite_length_ge (old new : List ℕ) : new.length ≤ (overwrite old new).length := by
  simp [overwrite]

variable {n arity : ℕ}

theorem PS.vec_bounds (w : List ℕ) (tf : ℕ → List Tok) (i : ℕ) (S : PS n arity) :
    (PS.vec w tf i S).1.cnt ≤ S.cnt + ((List.range i).flatMap tf).length ∧
      (PS.vec w tf i S).1.stk.length ≤ S.stk.length + ((List.range i).flatMap tf).length ∧
      (PS.vec w tf i S).2.length = i := by
  induction i with
  | zero => simp [PS.vec]
  | succ i ih =>
      rw [PS.vec_succ, flat_succ_len]
      have e1 := PS.run_cnt_le w (tf i) (PS.vec w tf i S).1
      have e2 := PS.run_stk_le w (tf i) (PS.vec w tf i S).1
      simp only [PS.drop1, List.length_tail, List.length_append, List.length_singleton]
      omega

theorem Rep.put_W2 {w : List ℕ} {D : List Bool} {S : PS n arity} {a : DS VV MM} (h : Rep w D S a) (v : ℕ) :
    Rep w D S (a.put W2 v) := by
  obtain ⟨⟨c, cn, ns, nsc, wm, wl, wc, dsr, dl, dc⟩, s1, s2, s3⟩ := h
  have hr : ∀ m : Fin MM, m ≠ W2 → (a.put W2 v).ram m = a.ram m := fun m hm => by
    simp only [DS.put]; exact Function.update_of_ne hm _ _
  have hc : ∀ m : Fin MM, m ≠ W2 → (a.put W2 v).rc m = a.rc m := fun m hm => by
    simp only [DS.put]; exact Function.update_of_ne hm _ _
  exact ⟨⟨⟨c.z, c.one, c.two⟩, cn, by rw [hr NS (by decide), ns], by rw [hc NS (by decide), hr NS (by decide), nsc],
    by rw [hr WM (by decide), wm], wl, by rw [hc WM (by decide)]; exact wc, by rw [hr DSt (by decide), dsr], dl,
    by rw [hc DSt (by decide)]; exact dc⟩, s1, by rw [hc STK (by decide), s2], by rw [hr STK (by decide), s3]⟩

/-- **The vector loop**: member `j < VC` of template `T` at level `5` (index in slot `4`), outputs to `W2`. -/
def vecP (T : U) : St VV MM :=
  .seq (.op (.rwM W2)) (.seq (.op (.zero (Sl 4)))
    (.seq (.loop (.lt (Sl 4) VC) (.seq (compU 5 T) (.seq (pop XA) (.seq (.op (.wrM W2 XA)) (.op (.inc (Sl 4)))))))
      (.op (.zero (Sl 4)))))

/-- The vector loop's register frame (`Sl 4` is restored). -/
def VScr (y : ℕ) : Prop := Scr 4 y ∨ y = 68

variable {C : Ctx}

theorem vecP_spec {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (T : U) (env : List ℕ)
    (henv : env.length = 4) (hd : 5 + T.depth ≤ 16) (ht : T.tneed ≤ 16) (count : ℕ)
    (hok : ∀ j < count, T.okV V D (env ++ [j])) (hcV : count ≤ V) (S : PS n arity) (a : DS VV MM)
    (h : Rep w D S a) (hs : ∀ j < 16, a.env (Sl j) = env.getD j 0) (hVC : a.env VC = count)
    (h1 : S.cnt + ((List.range count).flatMap (fun j => T.toks D (env ++ [j]))).length ≤ L)
    (h2 : S.stk.length + ((List.range count).flatMap (fun j => T.toks D (env ++ [j]))).length ≤ L) :
    Hx C (vecP T) a (fun b c => Rep w D (PS.vec w (fun j => T.toks D (env ++ [j])) count S).1 b ∧
      b.ram W2 = overwrite (a.ram W2) (PS.vec w (fun j => T.toks D (env ++ [j])) count S).2 ∧ b.rc W2 = count ∧
      Keep (Scr 4) (fun m => m ≤ 1 ∨ m = 4) (fun m => m ≤ 4) a b ∧
      c ≤ a.rc W2 + (T.ucost + Qc L) * ((List.range count).flatMap (fun j => T.toks D (env ++ [j]))).length +
        (12 * L + 40) * count + 10) := by
  set tf : ℕ → List Tok := fun j => T.toks D (env ++ [j]) with htf
  have hVW := G.hV
  have hLW := G.hL
  have hS4 : Sl 4 ≠ VC := by decide
  have hSl4 : (Sl 4).val = 68 := Sl_val (by omega)
  refine Hx.seq' (Hx.ofHs (hs_rwM C W2 a)) (fun b0 c0 ⟨hc0, hb0⟩ => ?_)
  subst hb0
  refine Hx.seq' (Hx.ofHs (hs_zero C (Sl 4) _)) (fun b1 c1 ⟨hc1, hb1⟩ => ?_)
  subst hb1
  set a1 := (a.rew W2).set (Sl 4) 0 with ha1
  have hr1 : Rep w D S a1 := by
    have : Rep w D S (a.rew W2) := by
      obtain ⟨⟨c, cn, ns, nsc, wm, wl, wc, dsr, dl, dc⟩, s1, s2, s3⟩ := h
      have hc : ∀ m : Fin MM, m ≠ W2 → (a.rew W2).rc m = a.rc m := fun m hm => by
        simp only [DS.rew]; exact Function.update_of_ne hm _ _
      exact ⟨⟨⟨c.z, c.one, c.two⟩, cn, ns, by rw [hc NS (by decide)]; exact nsc, wm, wl, by rw [hc WM (by decide)]; exact wc, dsr, dl,
        by rw [hc DSt (by decide)]; exact dc⟩, s1, by rw [hc STK (by decide)]; exact s2, s3⟩
    exact this.of_regs (Keep.set (T := (· = 68)) (R := fun _ => False) (M := fun _ => False) _ (Sl 4) 0 rfl)
      (fun y hy => by omega)
  have hs1 : ∀ j < 16, a1.env (Sl j) = (env ++ [0]).getD j 0 :=
    slots_set henv (by omega) (slots_ext henv (fun j hj => by
      rw [show (a.rew W2).env = a.env from rfl]; exact hs j hj)) 0
  have k1 : Keep (fun y => Scr 4 y ∨ y = 68) (fun m => m ≤ 1 ∨ m = 4) (fun m => m ≤ 4) a a1 :=
    ⟨fun y hy => DS.set_env_ne _ _ (neP (P := fun y => Scr 4 y ∨ y = 68) hy (Or.inr rfl)), fun _ _ => rfl,
      fun m hm => by simp only [ha1, DS.set_rc, DS.rew]; exact Function.update_of_ne (neM (by simp at hm ⊢; omega)) _ _,
      rfl, rfl, rfl, rfl, rfl⟩
  let I : ℕ → DS VV MM → ℕ → Prop := fun i b c0 =>
    Rep w D (PS.vec w tf i S).1 b ∧ b.env VC = count ∧ (∀ j < 16, b.env (Sl j) = (env ++ [i]).getD j 0) ∧
    b.ram W2 = overwrite (a.ram W2) (PS.vec w tf i S).2 ∧ b.rc W2 = i ∧
    Keep (fun y => Scr 4 y ∨ y = 68) (fun m => m ≤ 1 ∨ m = 4) (fun m => m ≤ 4) a b ∧
    c0 ≤ (T.ucost + Qc L) * ((List.range i).flatMap tf).length + (12 * L + 40) * i
  have step : ∀ i < count, ∀ b c0, I i b c0 → Cnd.eval b (.lt (Sl 4) VC) = true ∧
      Hx C (.seq (compU 5 T) (.seq (pop XA) (.seq (.op (.wrM W2 XA)) (.op (.inc (Sl 4)))))) b
        (fun b' c1 => I (i + 1) b' (c0 + c1 + 2)) := by
    intro i hi b c0 ⟨rb, hVb, hsb, hWb, hcb, kb, hc0b⟩
    have hSl : b.env (Sl 4) = i := by rw [hsb 4 (by omega), getD_snoc]; simp [henv]
    refine ⟨by simp [Cnd.eval, hSl, hVb, hi], ?_⟩
    obtain ⟨e1, e2, e3⟩ := PS.vec_bounds w tf i S
    have hfl := flat_le tf (show i + 1 ≤ count by omega)
    have hsl := flat_succ_len tf i
    have htfi : (tf i).length = (T.toks D (env ++ [i])).length := rfl
    rw [htfi] at hsl
    refine Hx.seq' (compU_spec G T 5 (env ++ [i]) _ b (by simp [henv]) (by omega) ht (hok i hi) rb hsb
      (by omega) (by omega)) (fun b1 c1 ⟨r1, k1', hc1⟩ => ?_)
    have e4 := PS.run_stk_le w (tf i) (PS.vec w tf i S).1
    have e4' := PS.run_stk_le w (T.toks D (env ++ [i])) (PS.vec w tf i S).1
    refine Hx.seq' (Hx.ofHs (pop_spec (C := C) XA (pop_ok XA (by simp)) _ b1 r1.base.cst r1.stk (by omega)))
      (fun b2 c2 ⟨hc2, ⟨v2, s2, k2⟩⟩ => ?_)
    have rb2 : Rep w D ((PS.vec w tf i S).1.run w (tf i)).drop1 b2 :=
      ⟨(r1.base.pop (by simp) k2).congr rfl rfl, s2⟩
    have hW2c : b2.rc W2 = i := by rw [k2.rc W2 (by simp), k1'.rc W2 (by simp [CurM]), hcb]
    have hW2r : b2.ram W2 = overwrite (a.ram W2) (PS.vec w tf i S).2 := by
      rw [k2.ram W2 id, k1'.ram W2 (by simp [MachR]), hWb]
    have hle : b2.rc W2 ≤ (b2.ram W2).length := by
      rw [hW2c, hW2r]
      have := overwrite_length_ge (a.ram W2) (PS.vec w tf i S).2
      omega
    refine Hx.seq' (Hx.ofHs (hs_wrM C W2 XA b2 hle)) (fun b3 c3 ⟨hc3, hb3⟩ => ?_)
    subst hb3
    have hSl2 : (b2.put W2 (b2.env XA)).env (Sl 4) = i := by
      show b2.env (Sl 4) = i
      rw [k2.env (Sl 4) (by unfold PopT SkT; rw [hSl4]; simp), k1'.env (Sl 4) (by unfold Scr MachT; rw [hSl4]; omega),
        hSl]
    refine Hx.mono' (Hx.ofHs (hs_inc C (Sl 4) _ (by rw [hSl2]; omega))) (fun b4 c4 ⟨hc4, hb4⟩ => ?_)
    subst hb4
    have hvs := PS.vec_succ w i tf S
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hvs]
      exact (rb2.put_W2 _).of_regs (Keep.set (T := (· = 68)) (R := fun _ => False) (M := fun _ => False) _ (Sl 4) _
        rfl) (fun y hy => by omega)
    · show b2.env VC = count
      rw [k2.env VC (by unfold PopT SkT; simp), k1'.env VC (by unfold Scr MachT; simp), hVb]
    · have hs3 : ∀ j < 16, (b2.put W2 (b2.env XA)).env (Sl j) = (env ++ [i]).getD j 0 := fun j hj => by
        show b2.env (Sl j) = _
        rw [k2.env (Sl j) (by rw [Sl_val hj]; unfold PopT SkT; simp; omega), k1'.slots _ hsb j hj]
      have := slots_set henv (by omega) hs3 ((b2.put W2 (b2.env XA)).env (Sl 4) + 1)
      rw [hSl2] at this ⊢
      exact this
    · rw [DS.set_ram]
      simp only [DS.put, Function.update_self]
      have hp := putAt_overwrite (a.ram W2) (PS.vec w tf i S).2 (b2.env XA)
      rw [e3] at hp
      rw [hW2c, hW2r, hp, hvs, v2]
    · simp only [DS.set_rc, DS.put, Function.update_self, hW2c]
    · have kA : Keep (fun y => Scr 4 y ∨ y = 68) (fun m => m ≤ 1 ∨ m = 4) (fun m => m ≤ 4) b b1 :=
        k1'.mono (fun y hy => Or.inl hy.mono) (fun m hm => Or.inl hm) (fun m hm => by unfold CurM at hm; omega)
      have kB : Keep (fun y => Scr 4 y ∨ y = 68) (fun m => m ≤ 1 ∨ m = 4) (fun m => m ≤ 4) b1 b2 :=
        k2.mono (fun y hy => by unfold PopT SkT at hy; simp only [XA_val] at hy; unfold Scr MachT; omega)
          (fun _ h => h.elim)
          (fun m hm => by omega)
      have kC : Keep (fun y => Scr 4 y ∨ y = 68) (fun m => m ≤ 1 ∨ m = 4) (fun m => m ≤ 4) b2
          (b2.put W2 (b2.env XA)) :=
        (keep_put b2 W2 _).mono (fun _ h => h.elim) (fun m hm => Or.inr hm) (fun m hm => by simp at hm; omega)
      exact kb.trans (kA.trans (kB.trans (kC.trans (Keep.set _ _ _ (Or.inr hSl4)))))
    · rw [hsl, Nat.mul_add]
      have : ((PS.vec w tf i S).1.run w (tf i)).stk.length ≤ L := by omega
      nlinarith
  have stop : ∀ b c0, I count b c0 → Cnd.eval b (.lt (Sl 4) VC) = false := by
    intro b c0 ⟨_, hVb, hsb, _, _, _, _⟩
    have hSl : b.env (Sl 4) = count := by rw [hsb 4 (by omega), getD_snoc]; simp [henv]
    simp [Cnd.eval, hSl, hVb]
  have hVC1 : a1.env VC = count := by rw [ha1, DS.set_env_ne _ _ hS4.symm]; exact hVC
  refine Hx.seq' (Hx.loopAcc (show Cnd.wf (.lt (Sl 4) VC) from hS4) I count step stop a1
    ⟨hr1, hVC1, hs1, by simp [ha1, DS.rew, PS.vec, overwrite], by simp [ha1, DS.rew], k1, by simp⟩)
    (fun b5 c5 ⟨c0f, ⟨r5, hV5, hs5, hW5, hc5, k5, hcf⟩, hc5'⟩ => ?_)
  refine Hx.mono' (Hx.ofHs (hs_zero C (Sl 4) b5)) (fun b6 c6 ⟨hc6, hb6⟩ => ?_)
  subst hb6
  have hz : (b5.set (Sl 4) 0).env (Sl 4) = a.env (Sl 4) := by
    rw [DS.set_env_self, hs 4 (by omega), List.getD_eq_default _ _ (by omega)]
  refine ⟨r5.of_regs (Keep.set (T := (· = 68)) (R := fun _ => False) (M := fun _ => False) _ (Sl 4) 0 rfl)
    (fun y hy => by omega), by rw [DS.set_ram]; exact hW5, by rw [DS.set_rc]; exact hc5,
    Keep.restore (ℓ := 4) (by omega) (k5.trans (Keep.set _ _ _ (Or.inr rfl))) hz, ?_⟩
  subst hc5'
  omega

end NearCubicGates.Adapters.Compile.OraclePrint
