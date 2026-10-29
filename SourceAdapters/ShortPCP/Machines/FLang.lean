import SourceAdapters.Joins.FieldCells

/-!
# Single-run time, machine layer 4: a structured language of field words

proof of `thm:short-pcp-ours` ("V0 runs in time poly(n, log T)") argues the time of `V0` at the level of field operations
(proof of `thm:short-pcp-ours`: "each field operation takes poly(f) steps") and integer bookkeeping. The cell stages of
`TimeStages.lean` (`CellStages`) are programs of the released cell language (`L/Proof/Gates/Cells/Lang.lean`). This
module fixes a small structured language `FL` in which the cell stages are written: variables hold natural numbers
(binary polynomial representatives are words `< 2^f`, with modulus degree specified by `GF.ModulusOk p f`),
expressions are integer and field operations, statements are
assignment, sequencing, branching, counted loops, bounded while loops, output of one bit, and the choice of the field
(`𝔽₂[X]/(p)`, `GF.ModulusOk p f`).

The semantics is total: integer results are clamped at `cap = 2^K − 1` (`K` is fixed by the run's width), loops run
at most `N` passes, and an invalid field choice selects `𝔽₂[X]/(X)`. The compiler `FLangComp.lean` proves that every
program runs in the cell language with exactly this semantics, within the state-independent bound `costS`, which is
a polynomial in `K` and `N` (`costS_le`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 Polynomial

/-- The number of program variables. -/
abbrev NU : ℕ := 56

/-- Program variables. -/
abbrev Var := Fin NU

/-- Expressions. -/
inductive E where
  | v (i : Var)
  | k (n : ℕ)
  | gk
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | div (a b : E)
  | md (a b : E)
  | shl (a b : E)
  | shr (a b : E)
  | bxor (a b : E)
  | fadd (a b : E)
  | fmul (a b : E)
  | fpow (a b : E)
  | finv (a : E)
  | lt (a b : E)
  | eq (a b : E)

/-- Statements. -/
inductive S where
  | skip
  | set (i : Var) (e : E)
  | seq (a b : S)
  | ite (c : E) (a b : S)
  | loop (i : Var) (n : E) (body : S)
  | whl (c : E) (body : S)
  | emit (e : E)
  | field (f p : E)
  | rd (i : Var)

/-- The run constants: the clamp exponent `K` (`cap = 2^K − 1`) and the pass bound `N`. -/
structure Glob where
  K : ℕ
  N : ℕ
  inp : List Bool

/-- The clamp. -/
def Glob.cap (G : Glob) : ℕ := 2 ^ G.K - 1

/-- A state: the variables, the output so far, the field `𝔽₂[X]/(fp)` of degree `fl`, the input position, and
the flag `bad` (an input bit was read past the end of the input). -/
structure FS where
  env : Var → ℕ
  out : List Bool
  fl : ℕ
  fp : ℕ
  ip : ℕ
  bad : Bool

/-- Set one variable. -/
def FS.setv (s : FS) (i : Var) (v : ℕ) : FS := { s with env := Function.update s.env i v }

@[simp] theorem FS.setv_env (s : FS) (i : Var) (v : ℕ) : (s.setv i v).env = Function.update s.env i v := rfl
@[simp] theorem FS.setv_out (s : FS) (i : Var) (v : ℕ) : (s.setv i v).out = s.out := rfl
@[simp] theorem FS.setv_fl (s : FS) (i : Var) (v : ℕ) : (s.setv i v).fl = s.fl := rfl
@[simp] theorem FS.setv_fp (s : FS) (i : Var) (v : ℕ) : (s.setv i v).fp = s.fp := rfl
@[simp] theorem FS.setv_ip (s : FS) (i : Var) (v : ℕ) : (s.setv i v).ip = s.ip := rfl
@[simp] theorem FS.setv_bad (s : FS) (i : Var) (v : ℕ) : (s.setv i v).bad = s.bad := rfl

/-! ## Field words -/

/-- The reduced word of a polynomial (degree `< ℓ` after reduction mod `p`). -/
noncomputable def redW (p ℓ : ℕ) (g : (ZMod 2)[X]) : ℕ := GF.ofPoly (g %ₘ GF.toPoly p) ℓ

/-- The product of two words. -/
noncomputable def mulW (p ℓ a b : ℕ) : ℕ := redW p ℓ (GF.toPoly a * GF.toPoly b)

/-- A power of a word. -/
noncomputable def powW (p ℓ a e : ℕ) : ℕ := redW p ℓ (GF.toPoly a ^ e)

theorem redW_lt (p ℓ : ℕ) (g : (ZMod 2)[X]) : redW p ℓ g < 2 ^ ℓ := GF.ofPoly_lt _ _

theorem rep_redW (p ℓ : ℕ) (hp : GF.ModulusOk p ℓ) (g : (ZMod 2)[X]) :
    GF.rep p (redW p ℓ g) = AdjoinRoot.mk (GF.toPoly p) g := by
  have hm := GF.toPoly_monic p ℓ hp
  have hdeg : (g %ₘ GF.toPoly p).degree < ℓ := by
    have := degree_modByMonic_lt g hm
    rwa [degree_eq_natDegree hm.ne_zero, GF.natDegree_toPoly p ℓ hp] at this
  rw [redW, GF.rep, GF.toPoly_ofPoly _ _ hdeg]
  have := AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk (GF.toPoly p) g)
  rwa [AdjoinRoot.modByMonicHom_mk] at this

theorem rep_mulW (p ℓ a b : ℕ) (hp : GF.ModulusOk p ℓ) : GF.rep p (mulW p ℓ a b) = GF.rep p a * GF.rep p b := by
  rw [mulW, rep_redW p ℓ hp, map_mul]; rfl

theorem rep_powW (p ℓ a e : ℕ) (hp : GF.ModulusOk p ℓ) : GF.rep p (powW p ℓ a e) = GF.rep p a ^ e := by
  rw [powW, rep_redW p ℓ hp, map_pow]; rfl

/-- A reduced word is determined by its field element. -/
theorem eq_of_rep (p ℓ a b : ℕ) (hp : GF.ModulusOk p ℓ) (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : GF.rep p a = GF.rep p b) : a = b := GF.rep_injOn p ℓ a b hp ha hb h

/-! ## Semantics -/

/-- Values of expressions. -/
noncomputable def evalE (G : Glob) (s : FS) : E → ℕ
  | .v i => s.env i
  | .k n => min n G.cap
  | .gk => G.K
  | .add a b => min (evalE G s a + evalE G s b) G.cap
  | .sub a b => evalE G s a - evalE G s b
  | .mul a b => min (evalE G s a * evalE G s b) G.cap
  | .div a b => evalE G s a / evalE G s b
  | .md a b => evalE G s a % evalE G s b
  | .shl a b => min (evalE G s a * 2 ^ evalE G s b) G.cap
  | .shr a b => evalE G s a / 2 ^ evalE G s b
  | .bxor a b => (evalE G s a ^^^ evalE G s b) % 2 ^ G.K
  | .fadd a b => (evalE G s a ^^^ evalE G s b) % 2 ^ s.fl
  | .fmul a b => mulW s.fp s.fl (evalE G s a % 2 ^ s.fl) (evalE G s b % 2 ^ s.fl)
  | .fpow a b => powW s.fp s.fl (evalE G s a % 2 ^ s.fl) (evalE G s b)
  | .finv a => powW s.fp s.fl (evalE G s a % 2 ^ s.fl) (2 ^ s.fl - 2)
  | .lt a b => if evalE G s a < evalE G s b then 1 else 0
  | .eq a b => if evalE G s a = evalE G s b then 1 else 0

/-- A bounded while loop: at most `n` passes of `f` while `c` holds. -/
def whileN (c : FS → Bool) (f : FS → FS) : ℕ → FS → FS
  | 0, s => s
  | n + 1, s => if c s then whileN c f n (f s) else s

/-- A field choice is valid: `1 ≤ f`, `f + 2 ≤ K`, `2^f ≤ p < 2^(f+1)` (so `GF.ModulusOk p f`). -/
def fieldOk (G : Glob) (f p : ℕ) : Bool := decide (1 ≤ f ∧ f + 2 ≤ G.K ∧ 2 ^ f ≤ p ∧ p < 2 * 2 ^ f)

/-- Results of statements. -/
noncomputable def evalS (G : Glob) : S → FS → FS
  | .skip, s => s
  | .set i e, s => s.setv i (evalE G s e)
  | .seq a b, s => evalS G b (evalS G a s)
  | .ite c a b, s => if evalE G s c = 0 then evalS G b s else evalS G a s
  | .loop i n body, s =>
    (List.range (min (evalE G s n) G.N)).foldl (fun s' j => evalS G body (s'.setv i j)) s
  | .whl c body, s => whileN (fun s' => evalE G s' c != 0) (evalS G body) G.N s
  | .emit e, s => { s with out := s.out ++ [evalE G s e != 0] }
  | .field f p, s =>
    if fieldOk G (evalE G s f) (evalE G s p) then { s with fl := evalE G s f, fp := evalE G s p }
    else { s with fl := 1, fp := 2 }
  | .rd i, s =>
    if s.ip < G.inp.length then { s.setv i (G.inp.getD s.ip false).toNat with ip := s.ip + 1 }
    else { s with bad := true }

/-- The field test as an expression (`fieldOk_eval` relates it to `fieldOk`). -/
def okE (f p : E) : E :=
  .mul (.mul (.lt (.k 0) f) (.lt (.add f (.k 1)) .gk))
    (.mul (.lt (.sub (.shl (.k 1) f) (.k 1)) p) (.lt p (.add (.shl (.k 1) f) (.shl (.k 1) f))))

/-! ## Costs (state-independent upper bounds, in cell-language units) -/

/-- A bound on the cost of every primitive operation at clamp exponent `K`. -/
def opc (G : Glob) : ℕ := 400 * (G.K + 1) ^ 3 + 400

/-- The cost bound of an expression. -/
def costE (G : Glob) : E → ℕ
  | .v _ => 2
  | .k n => 4 * n + 4
  | .gk => 2
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => costE G a + costE G b + opc G + 2
  | .finv a => costE G a + opc G + 1

/-- The cost bound of a statement. -/
def costS (G : Glob) : S → ℕ
  | .skip => 2
  | .set _ e => costE G e + 4
  | .seq a b => costS G a + costS G b + 1
  | .ite c a b => costE G c + costS G a + costS G b + 6
  | .loop _ n body => costE G n + 20 + G.N * (costS G body + 10)
  | .whl c body => 10 + G.N * (costE G c + costS G body + 12)
  | .emit e => costE G e + 6
  | .field f p => costE G (okE f p) + costE G (.shl (.k 1) f) + costE G p + 20
  | .rd _ => 3

/-! ## Sizes, nesting, and the polynomial cost bound -/

/-- Expression size (constants count by value). -/
def szE : E → ℕ
  | .v _ => 1
  | .k n => n + 1
  | .gk => 1
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => szE a + szE b + 1
  | .finv a => szE a + 1

/-- Statement size. -/
def szS : S → ℕ
  | .skip => 1
  | .set _ e => szE e + 1
  | .seq a b => szS a + szS b + 1
  | .ite c a b => szE c + szS a + szS b + 1
  | .loop _ n body => szE n + szS body + 1
  | .whl c body => szE c + szS body + 1
  | .emit e => szE e + 1
  | .field f p => szE (okE f p) + szE (.shl (.k 1) f) + szE p + 3
  | .rd _ => 1

/-- Loop nesting depth. -/
def dpS : S → ℕ
  | .seq a b => max (dpS a) (dpS b)
  | .ite _ a b => max (dpS a) (dpS b)
  | .loop _ _ body => dpS body + 1
  | .whl _ body => dpS body + 1
  | _ => 0

theorem opc_ge (G : Glob) : 400 ≤ opc G := by unfold opc; omega

theorem costE_le (G : Glob) : ∀ e : E, costE G e ≤ 4 * szE e * opc G
  | .v _ => by have := opc_ge G; simp only [costE, szE]; omega
  | .k n => by
    have := opc_ge G; simp only [costE, szE]
    have : 4 * (n + 1) * 1 ≤ 4 * (n + 1) * opc G := Nat.mul_le_mul_left _ (by omega)
    omega
  | .gk => by have := opc_ge G; simp only [costE, szE]; omega
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => by
    have ha := costE_le G a; have hb := costE_le G b
    have := opc_ge G
    simp only [costE, szE]
    have : 4 * (szE a + szE b + 1) * opc G = 4 * szE a * opc G + 4 * szE b * opc G + 4 * opc G := by ring
    omega
  | .finv a => by
    have ha := costE_le G a
    have := opc_ge G
    simp only [costE, szE]
    have : 4 * (szE a + 1) * opc G = 4 * szE a * opc G + 4 * opc G := by ring
    omega

theorem le_mul_pos {a b : ℕ} (hb : 1 ≤ b) : a ≤ a * b := Nat.le_mul_of_pos_right _ hb

/-- **The cost bound is polynomial in `K` and `N`.** -/
theorem costS_le (G : Glob) : ∀ p : S, costS G p ≤ 8 * szS p * opc G * (G.N + 1) ^ dpS p
  | .skip => by have := opc_ge G; simp only [costS, szS, dpS, pow_zero, mul_one]; omega
  | .set _ e => by
    have := costE_le G e; have := opc_ge G
    simp only [costS, szS, dpS, pow_zero, mul_one]
    have : 8 * (szE e + 1) * opc G = 2 * (4 * szE e * opc G) + 8 * opc G := by ring
    omega
  | .seq a b => by
    have ha := costS_le G a; have hb := costS_le G b
    have h1 : (G.N + 1) ^ dpS a ≤ (G.N + 1) ^ dpS (.seq a b) := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h2 : (G.N + 1) ^ dpS b ≤ (G.N + 1) ^ dpS (.seq a b) := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp : 1 ≤ (G.N + 1) ^ dpS (.seq a b) := Nat.one_le_pow _ _ (by omega)
    have ho := opc_ge G
    generalize (G.N + 1) ^ dpS (.seq a b) = P at *
    simp only [costS, szS]
    have e1 := Nat.mul_le_mul_left (8 * szS a * opc G) h1
    have e2 := Nat.mul_le_mul_left (8 * szS b * opc G) h2
    have e3 := le_mul_pos (a := 8 * opc G) hp
    have : 8 * (szS a + szS b + 1) * opc G * P = 8 * szS a * opc G * P + 8 * szS b * opc G * P + 8 * opc G * P := by
      ring
    omega
  | .ite c a b => by
    have hc := costE_le G c; have ha := costS_le G a; have hb := costS_le G b
    have h1 : (G.N + 1) ^ dpS a ≤ (G.N + 1) ^ dpS (.ite c a b) := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h2 : (G.N + 1) ^ dpS b ≤ (G.N + 1) ^ dpS (.ite c a b) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp : 1 ≤ (G.N + 1) ^ dpS (.ite c a b) := Nat.one_le_pow _ _ (by omega)
    have ho := opc_ge G
    generalize (G.N + 1) ^ dpS (.ite c a b) = P at *
    simp only [costS, szS]
    have e1 := Nat.mul_le_mul_left (8 * szS a * opc G) h1
    have e2 := Nat.mul_le_mul_left (8 * szS b * opc G) h2
    have e3 := le_mul_pos (a := 8 * opc G) hp
    have e4 := le_mul_pos (a := 4 * szE c * opc G) hp
    have : 8 * (szE c + szS a + szS b + 1) * opc G * P = 2 * (4 * szE c * opc G * P) + 8 * szS a * opc G * P +
        8 * szS b * opc G * P + 8 * opc G * P := by ring
    omega
  | .loop i n body => by
    have hn := costE_le G n; have hb := costS_le G body
    have hp : 1 ≤ (G.N + 1) ^ dpS body := Nat.one_le_pow _ _ (by omega)
    have ho := opc_ge G
    simp only [costS, szS, dpS, pow_succ]
    generalize (G.N + 1) ^ dpS body = P at *
    generalize opc G = O at *
    have e1 : costS G body + 10 ≤ 8 * szS body * O * P + O * P := by
      have := le_mul_pos (a := O) hp; omega
    have e2 : G.N * (costS G body + 10) ≤ (G.N + 1) * (8 * szS body * O * P + O * P) :=
      (Nat.mul_le_mul_right _ (by omega)).trans (Nat.mul_le_mul_left _ e1)
    have hq : 1 ≤ P * (G.N + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e3 : costE G n + 20 ≤ (4 * szE n * O + O) * (P * (G.N + 1)) := by
      have := le_mul_pos (a := 4 * szE n * O + O) hq; omega
    have : 8 * (szE n + szS body + 1) * O * (P * (G.N + 1)) = 2 * ((4 * szE n * O + O) * (P * (G.N + 1))) +
        (G.N + 1) * (8 * szS body * O * P + O * P) + 5 * (O * P * (G.N + 1)) := by ring
    omega
  | .whl c body => by
    have hc := costE_le G c; have hb := costS_le G body
    have hp : 1 ≤ (G.N + 1) ^ dpS body := Nat.one_le_pow _ _ (by omega)
    have ho := opc_ge G
    simp only [costS, szS, dpS, pow_succ]
    generalize (G.N + 1) ^ dpS body = P at *
    generalize opc G = O at *
    have e1 : costE G c + costS G body + 12 ≤ 4 * szE c * O * P + 8 * szS body * O * P + O * P := by
      have := le_mul_pos (a := O) hp; have := le_mul_pos (a := 4 * szE c * O) hp; omega
    have e2 : G.N * (costE G c + costS G body + 12) ≤ (G.N + 1) * (4 * szE c * O * P + 8 * szS body * O * P + O * P) :=
      (Nat.mul_le_mul_right _ (by omega)).trans (Nat.mul_le_mul_left _ e1)
    have hq : 10 ≤ O * P * (G.N + 1) := by
      have : 1 ≤ P * (G.N + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have := le_mul_pos (a := O) this; rw [mul_assoc]; omega
    have : 8 * (szE c + szS body + 1) * O * (P * (G.N + 1)) = 2 * ((G.N + 1) * (4 * szE c * O * P)) +
        (G.N + 1) * (8 * szS body * O * P) + 8 * (O * P * (G.N + 1)) := by ring
    have : (G.N + 1) * (4 * szE c * O * P + 8 * szS body * O * P + O * P) = (G.N + 1) * (4 * szE c * O * P) +
        (G.N + 1) * (8 * szS body * O * P) + O * P * (G.N + 1) := by ring
    omega
  | .emit e => by
    have := costE_le G e; have := opc_ge G
    simp only [costS, szS, dpS, pow_zero, mul_one]
    have : 8 * (szE e + 1) * opc G = 2 * (4 * szE e * opc G) + 8 * opc G := by ring
    omega
  | .field f p => by
    have h1 := costE_le G (okE f p)
    have h2 := costE_le G (.shl (.k 1) f)
    have h3 := costE_le G p
    have ho := opc_ge G
    simp only [costS, szS, dpS, pow_zero, mul_one]
    generalize opc G = O at *
    have : 8 * (szE (okE f p) + szE (.shl (.k 1) f) + szE p + 3) * O = 2 * (4 * szE (okE f p) * O) +
        2 * (4 * szE (.shl (.k 1) f) * O) + 2 * (4 * szE p * O) + 24 * O := by ring
    omega
  | .rd _ => by have := opc_ge G; simp only [costS, szS, dpS, pow_zero, mul_one]; omega

end NearCubicGates.Adapters.ShortPCP.Machines.FL
