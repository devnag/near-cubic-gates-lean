import SourceAdapters.RAMACSP.GenItemsTBlock

/-!
# Pieces of the item stream; variables read and depths of the printers

Paper: the proof of `lem:generator`. The printing loops range over bit
indices, code positions, registers, coordinates, neighbors or patterns;
none enumerates H or the steps of the computation.

- `Pc`: a piece of a block: a count, the bit index of pass `i`, and an item printer; `den_pc`: it prints the
  concatenation of its passes' items, for any invariant of the state that survives the two loop variables.
- `SX.All`, `Good`: every expression of a tree reads only the given variables and has depth at most `3`; this gives
  the conditions of `comp_spec` (`WF`) and of the compiler (`Ok`) for the item printers (`WF_itemT`, `Ok_itemT`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP.RamCodeWord
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

variable {G : Glob} (V : Verifier)

attribute [local irreducible] refList

/-! ## Pieces -/

/-- A piece: count, bit index of pass `i`, item printer. -/
structure Pc where
  c : Cnt
  jk : JK
  body : P

/-- Its printer. -/
def Pc.prog (pc : Pc) : P := .loop vI pc.c.e (.bind vJ pc.jk.e pc.body)

/-- **A piece prints its passes.** -/
theorem den_pc (r : ClockRequest) (hR : Room V r G) (Inv : FS → Prop)
    (hInv : ∀ s i v, Inv s → Inv ((s.setv vI i).setv vJ v)) {s : FS} (hb : Base V r s) (hs : Inv s) (pc : Pc)
    (sem : ℕ → List ℕ)
    (h : ∀ i < pc.c.val (dims (ownRam V r) (tau V r.2)), ∀ s', Base V r s' → Inv s' → s'.env vJ = pc.jk.val i →
      den G s' pc.body = sem i) :
    den G s pc.prog = (List.range (pc.c.val (dims (ownRam V r) (tau V r.2)))).flatMap sem := by
  rw [Pc.prog, den_loop s vI _ _ _ (cnt_eval V r hR hb pc.c) sem]
  intro i hi
  have hiw : i + 1 ≤ G.cap := by
    have h1 := cnt_le_w V r pc.c
    have h2 := wordW_lt_dom V r.2
    have h3 : 2 ^ domExp V r.2 ≤ 2 ^ (domExp V r.2 + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc := hR.cap
    omega
  simp only [den]
  rw [jk_eval i hiw]
  exact h i hi _ ((hb.setv V vI not_baseA_vI i).setv V vJ not_baseA_vJ _) (hInv s i _ hs) (by simp)

/-! ## Variables read and depths -/

/-- Every expression of a tree satisfies `Pr`. -/
def SX.All (Pr : E → Prop) : SX → Prop
  | .zero | .one => True
  | .var c => Pr c.bit
  | .add a b | .mul a b => SX.All Pr a ∧ SX.All Pr b
  | .ite c a b => Pr c ∧ SX.All Pr a ∧ SX.All Pr b

/-- An expression reads only `A` and has depth at most `3`. -/
def Good (A : Var → Prop) (e : E) : Prop := RdE A e ∧ dE e ≤ 3

theorem SX.All.rd {A : Var → Prop} : ∀ {x : SX}, x.All (Good A) → x.Rd A
  | .zero, _ => trivial
  | .one, _ => trivial
  | .var _, h => h.1
  | .add _ _, h => ⟨SX.All.rd h.1, SX.All.rd h.2⟩
  | .mul _ _, h => ⟨SX.All.rd h.1, SX.All.rd h.2⟩
  | .ite _ _ _, h => ⟨h.1.1, SX.All.rd h.2.1, SX.All.rd h.2.2⟩

theorem SX.All.dp {A : Var → Prop} : ∀ {x : SX}, x.All (Good A) → x.Dp
  | .zero, _ => trivial
  | .one, _ => trivial
  | .var _, h => h.2
  | .add _ _, h => ⟨SX.All.dp h.1, SX.All.dp h.2⟩
  | .mul _ _, h => ⟨SX.All.dp h.1, SX.All.dp h.2⟩
  | .ite _ _ _, h => ⟨h.1.2, SX.All.dp h.2.1, SX.All.dp h.2.2⟩

theorem all_sxSum {α : Type} (Pr : E → Prop) (f : ℕ → α → SX) :
    ∀ (p : ℕ) (l : List α), (∀ i a, a ∈ l → (f i a).All Pr) → (sxSum f p l).All Pr
  | _, [], _ => trivial
  | p, a :: l, h => ⟨h p a (by simp), all_sxSum Pr f (p + 1) l (fun i b hb => h i b (by simp [hb]))⟩

/-- The variables of the item printers: the request numbers, the layout masks, the two loop variables. -/
def itemA (x : Var) : Prop := (baseA x ∨ x = vI) ∨ x = vJ

theorem itemA_base {x : Var} (h : baseA x) : itemA x := Or.inl (Or.inl h)
theorem itemA_25 : itemA 25 := itemA_base (Or.inl ⟨by decide, by decide⟩)
theorem itemA_26 : itemA 26 := itemA_base (Or.inl ⟨by decide, by decide⟩)
theorem itemA_27 : itemA 27 := itemA_base (Or.inl ⟨by decide, by decide⟩)
theorem itemA_28 : itemA 28 := itemA_base (Or.inl ⟨by decide, by decide⟩)
theorem itemA_21 : itemA 21 := itemA_base (Or.inl ⟨by decide, by decide⟩)
theorem itemA_22 : itemA 22 := itemA_base (Or.inl ⟨by decide, by decide⟩)
theorem itemA_J : itemA vJ := Or.inr rfl
theorem itemA_I : itemA vI := Or.inl (Or.inr rfl)

theorem good_jE : Good itemA jE := ⟨itemA_J, by simp [jE, dE]⟩
theorem good_k0 : Good itemA k0 := ⟨trivial, by simp [k0, dE]⟩
theorem good_jm1E : Good itemA jm1E := ⟨⟨itemA_J, trivial⟩, by simp [jm1E, jE, dE]⟩
theorem good_wm1E : Good itemA wm1E := ⟨⟨itemA_26, trivial⟩, by simp [wm1E, dE]⟩
theorem good_betaE : Good itemA betaE := ⟨⟨itemA_27, itemA_25⟩, by simp [betaE, dE]⟩
theorem good_j0E : Good itemA j0E := ⟨⟨itemA_J, trivial⟩, by simp [j0E, jE, dE]⟩
theorem good_ltτ : Good itemA (.lt jE (.v 27)) := ⟨⟨itemA_J, itemA_27⟩, by simp [jE, dE]⟩
theorem good_bitk (c : ℕ) : Good itemA (.md (.shr (.k c) jE) (.k 2)) := ⟨⟨⟨trivial, itemA_J⟩, trivial⟩, by simp [jE, dE]⟩

theorem all_bitS_k (c : ℕ) : (bitS (.k c)).All (Good itemA) := ⟨good_bitk c, trivial, trivial⟩

theorem all_bitS_val (i : Fin 3) : (bitS (valE i)).All (Good itemA) := by
  refine ⟨⟨⟨⟨?_, itemA_J⟩, trivial⟩, ?_⟩, trivial, trivial⟩
  · fin_cases i
    · exact itemA_21
    · exact itemA_22
    · exact ⟨itemA_28, trivial⟩
  · fin_cases i <;> simp [valE, jE, dE]

theorem all_tS (K L : ℕ) (sl : TSlot) (b : E) (hb : Good itemA b) : (tS K L sl b).All (Good itemA) := hb

theorem all_eSetS (K L : ℕ) (Q : MI V (refW V) → Bool) : (eSetS V K L Q).All (Good itemA) := by
  apply all_sxSum
  intro i a _
  split_ifs
  · exact good_k0
  · trivial

theorem all_opndS (K L : ℕ) : ∀ x : Operand (refW V) (regCount V), (opndS V K L x).All (Good itemA)
  | .reg _ => good_jE
  | .pc => good_jE
  | .const _ => all_bitS_k _

theorem all_srcXS (K L : ℕ) : ∀ d : Desc V, (srcXS V K L d).All (Good itemA)
  | .ins (.arith _ _ x _) => all_opndS V K L x
  | .ins (.je _ _) => good_jE
  | .ins (.jne _ _) => good_jE
  | .ins (.load _ _) => good_jE
  | .ins (.store _ _) => good_jE
  | .ins .nop => trivial
  | .ins (.readA _) => trivial
  | .ins (.readB _) => trivial
  | .ins (.pload _ _) => trivial
  | .ins (.iseof _ _) => trivial
  | .ins (.out _) => trivial
  | .ins (.jmp _) => trivial
  | .hole _ _ => good_jE

theorem all_srcYS (K L : ℕ) : ∀ d : Desc V, (srcYS V K L d).All (Good itemA)
  | .ins (.arith _ _ _ y) => all_opndS V K L y
  | .ins (.store _ x) => all_opndS V K L x
  | .ins (.je _ _) => trivial
  | .ins (.jne _ _) => trivial
  | .ins (.load _ _) => trivial
  | .ins .nop => trivial
  | .ins (.readA _) => trivial
  | .ins (.readB _) => trivial
  | .ins (.pload _ _) => trivial
  | .ins (.iseof _ _) => trivial
  | .ins (.out _) => trivial
  | .ins (.jmp _) => trivial
  | .hole _ i => all_bitS_val i

theorem all_srcXFS (K L : ℕ) : ∀ d : Desc V, (srcXFS V K L d).All (Good itemA)
  | .ins (.iseof _ _) => good_k0
  | .ins (.arith _ _ _ _) => trivial
  | .ins (.store _ _) => trivial
  | .ins (.je _ _) => trivial
  | .ins (.jne _ _) => trivial
  | .ins (.load _ _) => trivial
  | .ins .nop => trivial
  | .ins (.readA _) => trivial
  | .ins (.readB _) => trivial
  | .ins (.pload _ _) => trivial
  | .ins (.out _) => trivial
  | .ins (.jmp _) => trivial
  | .hole _ _ => trivial

theorem all_eDotS (K L : ℕ) (f : Desc V → SX) (hf : ∀ d, (f d).All (Good itemA)) :
    (eDotS V K L f).All (Good itemA) := by
  unfold eDotS
  apply all_sxSum
  intro i d _
  exact ⟨good_k0, hf d⟩

theorem all_pcBranch (p c : ℕ) : SX.All (Good itemA) (.add (.mul (.mul (tS (regCount V) (codeLen V) (.e p) k0)
    (tS (regCount V) (codeLen V) (.OZ 0) wm1E)) (bitS (.k c))) (.mul (.add (tS (regCount V) (codeLen V) (.e p) k0)
    (.mul (tS (regCount V) (codeLen V) (.e p) k0) (tS (regCount V) (codeLen V) (.OZ 0) wm1E))) (bitS (.k p)))) :=
  ⟨⟨⟨good_k0, good_wm1E⟩, all_bitS_k _⟩, ⟨good_k0, ⟨good_k0, good_wm1E⟩⟩, all_bitS_k _⟩

theorem all_pcTermS (K L p : ℕ) : ∀ d : Desc V, (pcTermS V K L p d).All (Good itemA)
  | .ins (.out _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.jmp _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.je _ _) => ⟨⟨⟨good_k0, good_wm1E⟩, all_bitS_k _⟩, ⟨good_k0, ⟨good_k0, good_wm1E⟩⟩, all_bitS_k _⟩
  | .ins (.jne _ _) => ⟨⟨⟨good_k0, good_wm1E⟩, all_bitS_k _⟩, ⟨good_k0, ⟨good_k0, good_wm1E⟩⟩, all_bitS_k _⟩
  | .ins (.arith _ _ _ _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.store _ _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.load _ _) => ⟨good_k0, all_bitS_k _⟩
  | .ins .nop => ⟨good_k0, all_bitS_k _⟩
  | .ins (.readA _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.readB _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.pload _ _) => ⟨good_k0, all_bitS_k _⟩
  | .ins (.iseof _ _) => ⟨good_k0, all_bitS_k _⟩
  | .hole _ _ => ⟨good_k0, all_bitS_k _⟩

/-- **Every TIME template reads only the item variables, at depth at most `3`.** -/
theorem all_tmplT (K L : ℕ) (q : TEq) : (tmplT V K L q).All (Good itemA) := by
  have e := all_eSetS V K L
  cases q <;> simp only [tmplT, SX.All, tS, rS, tj, t0, eS, caS, boS, tcS, acS, bcS, cmpS, complS, majS, sumS] <;>
    simp only [e, good_jE, good_k0, good_jm1E, good_wm1E, good_betaE, good_j0E, good_ltτ, and_true, true_and,
      and_self]
  case decPc =>
    refine all_sxSum (Good itemA) _ 0 (refList V) (fun i d _ => ?_)
    exact ⟨good_bitk i, good_k0, trivial⟩
  case opX => exact all_eDotS V K L (srcXS V K L) (all_srcXS V K L)
  case opY => exact all_eDotS V K L (srcYS V K L) (all_srcYS V K L)
  case opXF => exact all_eDotS V K L (srcXFS V K L) (all_srcXFS V K L)
  case pcNext =>
    exact all_sxSum (Good itemA) _ 0 (refList V) (fun i d _ => all_pcTermS V K L i d)

/-! ## The printers of the TIME items and pieces -/

theorem not_itemA_vA : ¬ itemA vA := by unfold itemA baseA vA vI vJ vKL vUK vP5 vP6 vD; decide

theorem layA_itemA (x : Var) (h : layA x) : itemA x := itemA_base (layA_baseA x h)

theorem rd_knE {A : Var → Prop} (hU : A vUK) (lk : E) (hlk : RdE A lk) : RdE A (knE lk) := ⟨hU, hlk⟩

theorem rd_vaE {A : Var → Prop} (hA : ∀ x, layA x → A x) (h : SC) (hh : h.Rd A) (lv st : E) (hlv : RdE A lv)
    (hst : RdE A st) : RdE A (vaE h lv st) :=
  ⟨⟨⟨⟨⟨⟨trivial, hA 34 (by simp [layA])⟩, RdE_colE (hA 25 (by simp [layA])) h hh⟩, hA 32 (by simp [layA])⟩, hst⟩,
    hA 31 (by simp [layA])⟩, hlv⟩

theorem WF_itemT (q : TEq) : WF itemA (itemT V q) := by
  have hx := all_tmplT V (regCount V) (codeLen V) q
  have hh : (hostT V q).Rd itemA := itemA_J
  exact WF_itemP (itemA_base (Or.inl ⟨by decide, by decide⟩)) not_itemA_vA _ _ _
    (rd_knE (layA_itemA _ (by simp [layA])) _ itemA_28) (rd_vaE layA_itemA _ hh _ _ trivial trivial)
    (WF_tokP layA_itemA _ hh _ hx.rd)

theorem Ok_itemT {d : ℕ} (hd : d + 1 < 8) (q : TEq) : Ok d (itemT V q) := by
  have hx := all_tmplT V (regCount V) (codeLen V) q
  have hh : (hostT V q).Dp := show dE jE ≤ 3 by simp [jE, dE]
  refine Ok_itemP hd _ _ _ (by simp [knE, dE]) (dE_vaE _ _ _ hh (by simp [k0, dE]) (by simp [k0, dE]))
    (Ok_tokP (by omega) _ hh _ hx.dp)

/-- A loop over `vI` with the bit index bound in `vJ`. -/
theorem WF_loopBind (cE jkE : E) (body : P) (hc : RdE baseA cE) (hj : RdE (fun x => baseA x ∨ x = vI) jkE)
    (hb : WF itemA body) : WF baseA (.loop vI cE (.bind vJ jkE body)) :=
  ⟨hc, by decide, not_baseA_vI, hj, by decide, by unfold baseA vI vJ vKL vUK vP5 vP6 vD; decide, hb⟩

theorem Ok_loopBind (cE jkE : E) (body : P) (hc : dE cE < 16) (hj : dE jkE < 16) (hb : Ok 1 body) :
    Ok 0 (.loop vI cE (.bind vJ jkE body)) := ⟨hc, by omega, hj, hb⟩

theorem rd_cnt (c : Cnt) : RdE baseA c.e := by
  cases c <;> simp only [Cnt.e, RdE, betaE, baseA, vKL, vUK, vP5, vP6, vD] <;> decide

theorem dE_cnt (c : Cnt) : dE c.e < 16 := by
  cases c <;> simp [Cnt.e, dE, betaE]

theorem rd_jk (jk : JK) : RdE (fun x => baseA x ∨ x = vI) jk.e := by
  cases jk <;> simp only [JK.e, RdE, k0] <;> simp

theorem dE_jk (jk : JK) : dE jk.e < 16 := by
  cases jk <;> simp [JK.e, dE, k0]

theorem WF_tBlock : WF baseA (tBlockP V) := by
  apply WF_seqL
  intro p hp
  obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hp
  exact WF_loopBind _ _ _ (rd_cnt pc.c) (rd_jk pc.jk) (WF_itemT V _)

theorem Ok_tBlock : Ok 0 (tBlockP V) := by
  apply Ok_seqL
  intro p hp
  obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hp
  exact Ok_loopBind _ _ _ (dE_cnt pc.c) (dE_jk pc.jk) (Ok_itemT V (by norm_num) _)

end NearCubicGates.Adapters.RAMACSP.Gen.Items
