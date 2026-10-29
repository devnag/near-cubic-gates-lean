import Proof.Gates.Worker.Estimate
import Proof.Gates.Interfaces.Counter
import Proof.Gates.Transfer.CaseTwo
import Proof.Foundations.OuterPCPRecovery

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

/-- The native width at source length `N` (`sec:gadget-machine`, `q(N)`). -/
noncomputable def width (N : ℕ) : ℕ := Outer.width s.mw (g.sv s) N

/-- The source index `ν` of a length `N = 2^ν`. -/
def nu (N : ℕ) : ℕ := Nat.log 2 N

/-- The outer verifier `D_B` for the guessed pair `B = (B_src, B_pf)` (`sec:gadget-machine`: "Substituting `O_{B_pf}` for every
oracle gate and negating the output gives the outer verifier"). It does not read the source input; CHECK does
(`Guards`). -/
noncomputable def substituted {N : ℕ} (_x : BitInput N) (B : Outer.OuterGuess (width s g N)) : Circuit :=
  Outer.Dat s.mw (g.sv s) (nu N) B

/-- The set-up's guards on a guessed pair (`sec:gadget-machine`): `N = 2^ν`
("the weak machine first rejects unless N = 2^ν is
a power of two"); `ν` past the onset of `𝒱_G` (Lean's `SuccinctVerifier` holds from an onset, a finite set of lengths);
the length guard on the guessed source circuit ("it rejects unless the description of the source circuit B_src guessed
below has at most L_ν bits. By the choice of G′, once ν is large every general circuit with q inputs and at most q^G
gates has such a description, so the last guard rejects at only finitely many lengths"); and CHECK (eq:source-check).
See `Guess.SetupOK`. -/
def PairOK {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) : Prop :=
  N = 2 ^ nu N ∧ (g.sv s).onset ≤ nu N ∧ Outer.SrcFits g.lenExp (nu N) B.src ∧ Outer.CheckAt (nu N) x B.src

/-- The number of systematic coordinates: the outer randomness and its code parities. -/
noncomputable def sysCount {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) : ℕ :=
  (substituted s g x B).n + P.code.length (substituted s g x B).n

/-- The three-query PCPP of the checked substituted verifier (irreducible, to keep elaboration away from the
circuit builder). -/
noncomputable def pcpp {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) :
    RawThreeQueryPCPP (sysCount s P g x B) :=
  P.output (checkedCircuit P.code (substituted s g x B))

theorem pcpp_eq {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) :
    pcpp s P g x B = P.output (checkedCircuit P.code (substituted s g x B)) := by
  rfl

/-- The number of gadgets `M = 2^{cl}`. -/
noncomputable abbrev gadgets (N : ℕ) : ℕ := 2 ^ clauseWidth g.clauseDegree (width s g N)

/-- A guess on native width `q`: the pair `B = (B_src, B_pf)` (field `oracle`), one normalized circuit per auxiliary
name (index `j < proofBits` for
proof coordinate `j`, index `proofBits + a` for the helper of gadget `a`; other indices are unused), and witness
prefixes per gadget and term. -/
structure Guess (q : ℕ) where
  oracle : Outer.OuterGuess q
  circuits : ℕ → NCircuit q
  witnesses : ℕ → Fin 10 → List Bool

/-- An atom: a systematic coordinate `u` (a parity of `r`) or an auxiliary name `j` (a guessed circuit). -/
inductive Atom
  | sys (u : ℕ)
  | aux (j : ℕ)

/-- The sign of a literal. -/
def literalNeg {k : ℕ} : Literal k → Bool
  | .positive _ => false
  | .negative _ => true

namespace Guess
variable {s g} {N : ℕ} (x : BitInput N) (G : Guess (width s g N))

/-- The literal arity: systematic coordinates, then proof coordinates. -/
noncomputable abbrev Arity : ℕ := sysCount s P g x G.oracle + (pcpp s P g x G.oracle).proofBits

/-- The atom of a literal's underlying coordinate. -/
noncomputable def atomOf (v : Fin (G.Arity P x)) : Atom :=
  if v.val < sysCount s P g x G.oracle then .sys v.val else .aux (v.val - sysCount s P g x G.oracle)

/-- Clause `a mod 2^{rb}` of the repeated list. -/
noncomputable def clause (a : ℕ) : Fin 3 → Literal (G.Arity P x) :=
  (pcpp s P g x G.oracle).clause ⟨a % 2 ^ (pcpp s P g x G.oracle).randomBits, Nat.mod_lt _ (by positivity)⟩

/-- The value of an atom at `r`. -/
noncomputable def atomValue (r : BitInput (width s g N)) : Atom → Bool
  | .sys u => if h : u < sysCount s P g x G.oracle then sysEnc P.code (substituted s g x G.oracle).n r ⟨u, h⟩ else false
  | .aux j => (G.circuits j).eval r

/-- A literal as (flip, atom). Written through the arity-generic `literalNeg`/`literalVar`, so that no matcher captures
the guess (the calls of a guess do not read its witness prefixes, definitionally). -/
noncomputable def literalParts (l : Literal (G.Arity P x)) : Bool × Atom := (literalNeg l, G.atomOf P x (literalVar l))

/-- The helper of gadget `a` is auxiliary name `proofBits + a`. -/
noncomputable def helper (a : ℕ) : Atom := .aux ((pcpp s P g x G.oracle).proofBits + a)

/-- The operands of term `t` of gadget `a` (each a flip and an atom; one or two of them), in the order of
`Worker.tenTerms`. -/
noncomputable def operands (a : ℕ) (t : Fin 10) : List (Bool × Atom) :=
  let l := fun i : Fin 3 => G.literalParts P x (G.clause P x a i)
  let h : Bool × Atom := (false, G.helper P x a)
  match t.val with
  | 0 => [h]
  | 1 => [l 0]
  | 2 => [l 1]
  | 3 => [l 2]
  | 4 => [l 0, l 1]
  | 5 => [l 0, l 2]
  | 6 => [l 1, l 2]
  | 7 => [l 0, h]
  | 8 => [l 1, h]
  | _ => [l 2, h]

/-- The gadget family of the guess: literal and helper values at every point. -/
noncomputable def family : GadgetFamily (Fin (gadgets s g N)) (BitInput (width s g N)) where
  x := fun a i r => let p := G.literalParts P x (G.clause P x a.val i); xor p.1 (G.atomValue P x r p.2)
  y := fun a r => G.atomValue P x r (G.helper P x a.val)

end Guess

/-! ## Intervals, the upper estimate, and the meaning -/

/-- The mean of a parity of `r` on support `S`: `1/2` when `S` is nonempty, else `0`. -/
def parityMean {q : ℕ} (S : Finset (Fin q)) : ℚ := if S.Nonempty then 1 / 2 else 0

namespace Guess
variable {s g} {N : ℕ} (x : BitInput N) (G : Guess (width s g N))

/-- The parity support of systematic coordinate `u`: `{u}` for the outer randomness, else the code parity. -/
noncomputable def sysSupport (u : ℕ) : Finset (Fin (width s g N)) :=
  if h : u < width s g N then {⟨u, h⟩}
  else if h' : u - width s g N < P.code.length (substituted s g x G.oracle).n then
    P.code.support (substituted s g x G.oracle).n ⟨u - width s g N, h'⟩
  else ∅

/-- The call for one circuit atom, optionally XORed with a parity, at radius `ω`. -/
noncomputable def singleCall (ω : ℚ) (j : ℕ) (S : Finset (Fin (width s g N))) : Call :=
  if S.Nonempty then
    ⟨width s g N, .parity, G.circuits j, NCircuit.empty _, (canonList S).map Fin.val, ω⟩
  else ⟨width s g N, .single, G.circuits j, NCircuit.empty _, [], ω⟩

/-- The pair call `C_i ⊕ C_j` at radius `ω`. -/
noncomputable def pairCall (ω : ℚ) (i j : ℕ) : Call :=
  ⟨width s g N, .pair, G.circuits i, G.circuits j, [], ω⟩

/-- The interval of an XOR of at most two (flip, atom) operands, with witness `w` (`sec:gadget-transfer`,
eq:gadget-pair-identity): exact for
pure parities and repeated circuits, otherwise the counter's `(p̂, κ̂)` on the call, complemented by the flip. -/
noncomputable def intervalOf {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool)
    (ops : List (Bool × Atom)) : ℚ × ℚ := by
  classical
  exact
    let flip := ops.foldl (fun f o => xor f o.1) false
    let flipI : ℚ × ℚ → ℚ × ℚ := fun pk => if flip then (1 - pk.1, pk.2) else pk
    let ask : Call → ℚ × ℚ := fun c => ctr.value c w
    match ops.map Prod.snd with
    | [.sys u] => flipI (parityMean (G.sysSupport P x u), 0)
    | [.aux j] => flipI (ask (G.singleCall ω j ∅))
    | [.sys u, .sys v] => flipI (parityMean (symmDiff (G.sysSupport P x u) (G.sysSupport P x v)), 0)
    | [.sys u, .aux j] => flipI (ask (G.singleCall ω j (G.sysSupport P x u)))
    | [.aux j, .sys u] => flipI (ask (G.singleCall ω j (G.sysSupport P x u)))
    | [.aux i, .aux j] => if i = j then flipI (0, 0) else flipI (ask (G.pairCall ω i j))
    | _ => (0, 1)

/-- The interval of term `t` of gadget `a`. -/
noncomputable def termInterval {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (a : ℕ) (t : Fin 10) : ℚ × ℚ :=
  G.intervalOf P x ctr ω (G.witnesses a t) (G.operands P x a t)

/-- The certified upper estimate `U` of the guess. -/
noncomputable def upperEstimate {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) : ℝ :=
  upper (fun a : Fin (gadgets s g N) => G.termInterval P x ctr ω a.val)

/-- The number of auxiliary names: proof coordinates and one helper per gadget. -/
noncomputable def auxCount : ℕ := (pcpp s P g x G.oracle).proofBits + gadgets s g N

/-- The set-up's guards (`sec:gadget-machine`, decided by the set-up machine before the term loop): `PairOK` of the guessed
pair — `N = 2^ν`, `ν` past the onset of `𝒱_G`, "the description of the source circuit B_src guessed below has at most
L_ν bits", and CHECK (eq:source-check: `B_src(bin_ν(i)0^{q−ν}) = z_i` for every `i < N`). -/
def SetupOK : Prop := PairOK s g x G.oracle

/-- The guards (`sec:gadget-machine`): the clause count divides `M` ("repeat the whole clause list to exactly M clauses. The
original length divides this number"), `q ≥ 2`, `ν ≥ 1`, the precision guard `γ/L_ν < ε`, and the set-up's guards
`SetupOK`. The size limits are `SizeOK`: they bound the honest guess but need not be tested, since soundness holds for
every guess. -/
def Guards {B1 B2 : ℕ} (_ctr : Counter B1 B2) (_budget : ℕ → ℕ) (ε : ℝ) : Prop :=
  (pcpp s P g x G.oracle).randomBits ≤ clauseWidth g.clauseDegree (width s g N) ∧
    2 ≤ width s g N ∧ 1 ≤ nu N ∧ (P.gamma : ℝ) / (Outer.instLength g.lenExp (nu N) : ℝ) < ε ∧
    G.SetupOK x

/-- The size limits of `sec:gadget-machine` ("All guesses have a fixed polynomial bound in q"), which bound the
honest guess. -/
def SizeOK {B1 B2 : ℕ} (ctr : Counter B1 B2) (budget : ℕ → ℕ) : Prop :=
  G.oracle.src.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N) ∧
    G.oracle.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N) ∧
    (∀ j < G.auxCount P x, (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧
      (G.circuits j).topWeight ≤ budget (width s g N)) ∧
    (∀ a < gadgets s g N, ∀ t, (G.witnesses a t).length ≤ ctr.witnessLength (width s g N))

def Certified {B1 B2 : ℕ} (ctr : Counter B1 B2) (budget : ℕ → ℕ) (ε : ℝ) (ω : ℚ) : Prop :=
  G.Guards P x ctr budget ε ∧ G.upperEstimate P x ctr ω < (P.gamma : ℝ) - ε

end Guess

end NearCubicGates.Close.Worker
