import SourceAdapters.RAMACSP.GenEmit

/-!
# Printing programs: lists of numbers, each printed as `natWord`

Paper: `lem:generator`. The machine-item program prints the selector and
equation of each active catalog template, with all iterations over the
polynomial-size index ranges.

A printing program `P` prints numbers (`num`), in sequence (`seq`), in counted loops (`loop`), under local bindings
(`bind`) and branches (`ite`). Its denotation `den G s p` is the list of numbers it prints, read with the `FL`
semantics (`evalE`). `comp p` is the `FL` statement; `comp_spec`: run from `s`, it appends
`dbl ((den G s p).flatMap natWord)` to the output and keeps every variable the program may read (`WF`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP.Gen
open NearCubicWires (natBitLength)
open NearCubicWires.RepairRepresentation (natWord)

/-- Printing programs. -/
inductive P where
  | nil
  | num (e : E)
  | seq (a b : P)
  | loop (i : Var) (n : E) (body : P)
  | bind (i : Var) (e : E) (body : P)
  | ite (c : E) (a b : P)

/-- The scratch variable that holds the number being printed. -/
def nv : Var := 7

/-- The `FL` statement of a printing program. -/
def comp : P → S
  | .nil => .skip
  | .num e => .seq (.set nv e) (emitNatV nv)
  | .seq a b => .seq (comp a) (comp b)
  | .loop i n b => .loop i n (comp b)
  | .bind i e b => .seq (.set i e) (comp b)
  | .ite c a b => .ite c (comp a) (comp b)

/-- The numbers a printing program prints from the state `s`. -/
noncomputable def den (G : Glob) : FS → P → List ℕ
  | _, .nil => []
  | s, .num e => [evalE G s e]
  | s, .seq a b => den G s a ++ den G s b
  | s, .loop i n b => (List.range (min (evalE G s n) G.N)).flatMap fun j => den G (s.setv i j) b
  | s, .bind i e b => den G (s.setv i (evalE G s e)) b
  | s, .ite c a b => if evalE G s c = 0 then den G s b else den G s a

/-! ## Variables read -/

/-- An expression reads only variables in `A`. -/
def RdE (A : Var → Prop) : E → Prop
  | .v i => A i
  | .k _ | .gk => True
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => RdE A a ∧ RdE A b
  | .finv a => RdE A a

/-- A program reads only variables in `A` and the variables it binds; it binds only variables `≥ 20` outside `A`. -/
def WF (A : Var → Prop) : P → Prop
  | .nil => True
  | .num e => RdE A e
  | .seq a b => WF A a ∧ WF A b
  | .loop i n b => RdE A n ∧ 20 ≤ i.val ∧ ¬ A i ∧ WF (fun x => A x ∨ x = i) b
  | .bind i e b => RdE A e ∧ 20 ≤ i.val ∧ ¬ A i ∧ WF (fun x => A x ∨ x = i) b
  | .ite c a b => RdE A c ∧ WF A a ∧ WF A b

/-- Two states agree on `A` (and on the field). -/
def Agree (A : Var → Prop) (s t : FS) : Prop := (∀ x, A x → t.env x = s.env x) ∧ t.fl = s.fl ∧ t.fp = s.fp

theorem Agree.setv {A : Var → Prop} {s t : FS} (h : Agree A s t) (i : Var) (v : ℕ) :
    Agree (fun x => A x ∨ x = i) (s.setv i v) (t.setv i v) := by
  refine ⟨fun x hx => ?_, h.2.1, h.2.2⟩
  by_cases hxi : x = i
  · subst hxi; simp
  · simp only [FS.setv_env, Function.update_of_ne hxi]
    exact h.1 x (hx.resolve_right hxi)

theorem Agree.weaken {A B : Var → Prop} {s t : FS} (h : Agree A s t) (hBA : ∀ x, B x → A x) : Agree B s t :=
  ⟨fun x hx => h.1 x (hBA x hx), h.2⟩

variable {G : Glob}

theorem evalE_agree {A : Var → Prop} {s t : FS} (h : Agree A s t) : ∀ e : E, RdE A e → evalE G t e = evalE G s e
  | .v i, he => h.1 i he
  | .k _, _ => rfl
  | .gk, _ => rfl
  | .add a b, he | .sub a b, he | .mul a b, he | .div a b, he | .md a b, he | .shl a b, he | .shr a b, he
  | .bxor a b, he | .lt a b, he | .eq a b, he => by
    simp only [evalE, evalE_agree h a he.1, evalE_agree h b he.2]
  | .fadd a b, he | .fmul a b, he | .fpow a b, he => by
    simp only [evalE, evalE_agree h a he.1, evalE_agree h b he.2, h.2.1, h.2.2]
  | .finv a, he => by simp only [evalE, evalE_agree h a he, h.2.1, h.2.2]

/-- **Congruence**: the denotation depends only on the variables the program may read. -/
theorem den_agree : ∀ (p : P) (A : Var → Prop) (s t : FS), WF A p → Agree A s t → den G t p = den G s p
  | .nil, _, _, _, _, _ => rfl
  | .num e, A, s, t, hw, h => by simp only [den, evalE_agree h e hw]
  | .seq a b, A, s, t, hw, h => by
    simp only [den, den_agree a A s t hw.1 h, den_agree b A s t hw.2 h]
  | .loop i n b, A, s, t, hw, h => by
    simp only [den, evalE_agree h n hw.1]
    congr 1; funext j
    exact den_agree b _ _ _ hw.2.2.2 (h.setv i j)
  | .bind i e b, A, s, t, hw, h => by
    simp only [den, evalE_agree h e hw.1]
    exact den_agree b _ _ _ hw.2.2.2 (h.setv i _)
  | .ite c a b, A, s, t, hw, h => by
    simp only [den, evalE_agree h c hw.1, den_agree a A s t hw.2.1 h, den_agree b A s t hw.2.2 h]

/-! ## The output theorem -/

/-- The run of a printing program: it appended `dbl (u.flatMap natWord)` and kept `A`, the field, the input position
and the flag. -/
structure Out (A : Var → Prop) (s t : FS) (u : List ℕ) : Prop where
  out : t.out = s.out ++ dbl (u.flatMap natWord)
  env : ∀ x, A x → t.env x = s.env x
  fl : t.fl = s.fl
  fp : t.fp = s.fp
  ip : t.ip = s.ip
  bad : t.bad = s.bad

theorem Out.trans {A : Var → Prop} {s t t' : FS} {u u' : List ℕ} (h1 : Out A s t u) (h2 : Out A t t' u') :
    Out A s t' (u ++ u') :=
  ⟨by rw [h2.out, h1.out, List.flatMap_append, dbl_append, List.append_assoc], fun x hx => (h2.env x hx).trans
    (h1.env x hx), h2.fl.trans h1.fl, h2.fp.trans h1.fp, h2.ip.trans h1.ip, h2.bad.trans h1.bad⟩

theorem Out.agree {A : Var → Prop} {s t : FS} {u : List ℕ} (h : Out A s t u) : Agree A s t := ⟨h.env, h.fl, h.fp⟩

theorem nv_val : nv.val = 7 := rfl

/-- **The output theorem**: a well-formed printing program prints its denotation, each number as `natWord`, when every
printed number has `natBitLength + 2 ≤ K`. -/
theorem comp_spec (hN : G.K ≤ G.N) : ∀ (p : P) (A : Var → Prop) (s : FS), (∀ x, A x → 20 ≤ x.val) → WF A p →
    (∀ x ∈ den G s p, natBitLength x + 2 ≤ G.K) → Out A s (evalS G (comp p) s) (den G s p)
  | .nil, A, s, _, _, _ => ⟨by simp [comp, den, dbl], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | .num e, A, s, hA, hw, hb => by
    have hv := hb (evalE G s e) (by simp [den])
    have e1 := emitNatV_spec (G := G) (s.setv nv (evalE G s e)) nv (by decide) (by decide)
      (by simpa [nv] using hv) hN
    have hval : (s.setv nv (evalE G s e)).env nv = evalE G s e := by simp
    rw [hval] at e1
    show Out A s (evalS G (emitNatV nv) (s.setv nv (evalE G s e))) [evalE G s e]
    refine ⟨by rw [e1.out]; simp, fun x hx => ?_, e1.fl, e1.fp, e1.ip, e1.bad⟩
    have h20 := hA x hx
    have hx7 : x ≠ nv := fun h => by subst h; exact absurd h20 (by decide)
    have hx5 : x ≠ 5 := fun h => by subst h; exact absurd h20 (by decide)
    have hx6 : x ≠ 6 := fun h => by subst h; exact absurd h20 (by decide)
    rw [e1.env x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => h.elim hx5 hx6)]
    simp [Function.update_of_ne hx7]
  | .seq a b, A, s, hA, hw, hb => by
    have ha := comp_spec hN a A s hA hw.1 (fun x hx => hb x (by simp [den, hx]))
    have hag := ha.agree
    have hdb : den G (evalS G (comp a) s) b = den G s b := den_agree b A s _ hw.2 hag
    have hb' := comp_spec hN b A (evalS G (comp a) s) hA hw.2 (fun x hx => hb x (by rw [hdb] at hx; simp [den, hx]))
    rw [hdb] at hb'
    exact ha.trans hb'
  | .loop i n b, A, s, hA, hw, hb => by
    obtain ⟨hn, hi20, hiA, hwb⟩ := hw
    have hA' : ∀ x, (A x ∨ x = i) → 20 ≤ x.val := fun x hx => hx.elim (hA x) (fun h => h ▸ hi20)
    have := loop_inv G (i := i) (n := n) (body := comp b) (s := s)
      (fun j t => Out A s t ((List.range j).flatMap fun j => den G (s.setv i j) b))
      ⟨by simp [dbl], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ (by
        intro j hj t ht
        have hag : Agree (fun x => A x ∨ x = i) (s.setv i j) (t.setv i j) := ht.agree.setv i j
        have hd : den G (t.setv i j) b = den G (s.setv i j) b := den_agree b _ _ _ hwb hag
        have hbj : ∀ x ∈ den G (t.setv i j) b, natBitLength x + 2 ≤ G.K := by
          intro x hx; rw [hd] at hx
          exact hb x (by simp only [den, List.mem_flatMap, List.mem_range]; exact ⟨j, hj, hx⟩)
        have hr := comp_spec hN b _ (t.setv i j) hA' hwb hbj
        rw [hd] at hr
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        refine ht.trans ⟨hr.out, fun x hx => ?_, hr.fl, hr.fp, hr.ip, hr.bad⟩
        have hxi : x ≠ i := fun h => hiA (h ▸ hx)
        rw [hr.env x (Or.inl hx)]
        simp [Function.update_of_ne hxi])
    exact this
  | .bind i e b, A, s, hA, hw, hb => by
    obtain ⟨he, hi20, hiA, hwb⟩ := hw
    have hA' : ∀ x, (A x ∨ x = i) → 20 ≤ x.val := fun x hx => hx.elim (hA x) (fun h => h ▸ hi20)
    have hr := comp_spec hN b _ (s.setv i (evalE G s e)) hA' hwb (fun x hx => hb x (by simpa [den] using hx))
    show Out A s (evalS G (comp b) (s.setv i (evalE G s e))) (den G (s.setv i (evalE G s e)) b)
    refine ⟨hr.out, fun x hx => ?_, hr.fl, hr.fp, hr.ip, hr.bad⟩
    have hxi : x ≠ i := fun h => hiA (h ▸ hx)
    rw [hr.env x (Or.inl hx)]
    simp [Function.update_of_ne hxi]
  | .ite c a b, A, s, hA, hw, hb => by
    show Out A s (if evalE G s c = 0 then evalS G (comp b) s else evalS G (comp a) s) (den G s (.ite c a b))
    by_cases hc : evalE G s c = 0
    · simp only [hc, if_true, den] at hb ⊢
      exact comp_spec hN b A s hA hw.2.2 hb
    · simp only [hc, if_false, den] at hb ⊢
      exact comp_spec hN a A s hA hw.2.1 hb

/-! ## Well-formedness for the compiler (`wfS`) -/

/-- The depth conditions of the compiled statement at loop depth `d`. -/
def Ok : ℕ → P → Prop
  | _, .nil => True
  | d, .num e => dE e < 16 ∧ d < 8
  | d, .seq a b => Ok d a ∧ Ok d b
  | d, .loop _ n b => dE n < 16 ∧ d < 8 ∧ Ok (d + 1) b
  | d, .bind _ e b => dE e < 16 ∧ Ok d b
  | d, .ite c a b => dE c < 16 ∧ Ok d a ∧ Ok d b

theorem wfS_emitNatV (d : ℕ) (hd : d < 8) : wfS (emitNatV nv) d = true := by
  simp only [emitNatV, natLenP, emitF, wfS, dE, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem wfS_comp : ∀ (d : ℕ) (p : P), Ok d p → wfS (comp p) d = true
  | _, .nil, _ => rfl
  | d, .num e, h => by
    simp only [comp, wfS, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h.1, wfS_emitNatV d h.2⟩
  | d, .seq a b, h => by simp only [comp, wfS, Bool.and_eq_true]; exact ⟨wfS_comp d a h.1, wfS_comp d b h.2⟩
  | d, .loop _ n b, h => by
    simp only [comp, wfS, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h.1, h.2.1⟩, wfS_comp (d + 1) b h.2.2⟩
  | d, .bind _ e b, h => by
    simp only [comp, wfS, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h.1, wfS_comp d b h.2⟩
  | d, .ite c a b, h => by
    simp only [comp, wfS, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h.1, wfS_comp d a h.2.1⟩, wfS_comp d b h.2.2⟩

/-! ## Sequences of programs -/

/-- A list of programs in sequence. -/
def seqL : List P → P
  | [] => .nil
  | p :: ps => .seq p (seqL ps)

theorem den_seqL (s : FS) : ∀ ps : List P, den G s (seqL ps) = ps.flatMap (den G s)
  | [] => rfl
  | p :: ps => by simp [seqL, den, den_seqL s ps]

theorem WF_seqL {A : Var → Prop} : ∀ ps : List P, (∀ p ∈ ps, WF A p) → WF A (seqL ps)
  | [], _ => trivial
  | p :: ps, h => ⟨h p (by simp), WF_seqL ps (fun q hq => h q (by simp [hq]))⟩

theorem Ok_seqL {d : ℕ} : ∀ ps : List P, (∀ p ∈ ps, Ok d p) → Ok d (seqL ps)
  | [], _ => trivial
  | p :: ps, h => ⟨h p (by simp), Ok_seqL ps (fun q hq => h q (by simp [hq]))⟩

/-- A loop whose pass `j` prints `g j` prints `(List.range n).flatMap g`. -/
theorem den_loop (s : FS) (i : Var) (n : E) (b : P) (m : ℕ) (hm : min (evalE G s n) G.N = m) (g : ℕ → List ℕ)
    (hg : ∀ j < m, den G (s.setv i j) b = g j) : den G s (.loop i n b) = (List.range m).flatMap g := by
  simp only [den, hm]
  exact List.flatMap_congr (fun j hj => hg j (List.mem_range.mp hj))

end NearCubicGates.Adapters.RAMACSP.Gen.Items
