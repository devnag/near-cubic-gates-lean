import Proof.Gates.Worker.Meaning
import Proof.Gates.Worker.VerdictSpec
import Proof.Gates.WorkerArith.UpperL
import Proof.Gates.Counter.Den
import Proof.Gates.Worker.Format

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

namespace Guess
variable {s g} {N : ℕ} (x : BitInput N) (G : Guess (width s g N))

/-- The flip and the raw interval of an XOR of operands (the interval of `intervalOf` before the flip). -/
noncomputable def termParts {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool)
    (ops : List (Bool × Atom)) : Bool × (ℚ × ℚ) := by
  classical
  exact
    let flip := ops.foldl (fun f o => xor f o.1) false
    let ask : Call → ℚ × ℚ := fun c => ctr.value c w
    match ops.map Prod.snd with
    | [.sys u] => (flip, (parityMean (G.sysSupport P x u), 0))
    | [.aux j] => (flip, ask (G.singleCall ω j ∅))
    | [.sys u, .sys v] => (flip, (parityMean (symmDiff (G.sysSupport P x u) (G.sysSupport P x v)), 0))
    | [.sys u, .aux j] => (flip, ask (G.singleCall ω j (G.sysSupport P x u)))
    | [.aux j, .sys u] => (flip, ask (G.singleCall ω j (G.sysSupport P x u)))
    | [.aux i, .aux j] => (flip, if i = j then (0, 0) else ask (G.pairCall ω i j))
    | _ => (false, (0, 1))

theorem flipI_termParts {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool) (ops : List (Bool × Atom)) :
    flipI (G.termParts P x ctr ω w ops) = G.intervalOf P x ctr ω w ops := by
  unfold termParts intervalOf
  generalize ops.map Prod.snd = l
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> first | rfl | (simp only [flipI]; split_ifs <;> rfl)
  · cases a <;> cases b <;> rfl

/-- The flip and raw interval of term `t` of gadget `a`. -/
noncomputable def termRaw {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (a : ℕ) (t : Fin 10) : Bool × (ℚ × ℚ) :=
  G.termParts P x ctr ω (G.witnesses a t) (G.operands P x a t)

theorem flipI_termRaw {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (a : ℕ) (t : Fin 10) :
    flipI (G.termRaw P x ctr ω a t) = G.termInterval P x ctr ω a t :=
  G.flipI_termParts P x ctr ω _ _

noncomputable def termList {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) : List (Bool × (ℚ × ℚ)) :=
  WorkerArith.gmList (fun (a : Fin (gadgets s g N)) t => G.termRaw P x ctr ω a.val t)

theorem termList_length {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) :
    (G.termList P x ctr ω).length = 10 * gadgets s g N :=
  WorkerArith.gmList_length _

/-- `p · 2^{q+1}` is an integer, for `p ∈ {0, 1/2}`. -/
theorem parityMean_den {q : ℕ} (S : Finset (Fin q)) (k : ℕ) : (parityMean S * 2 ^ (k + 1)).den = 1 := by
  unfold parityMean
  split_ifs
  · rw [show (1 / 2 : ℚ) * 2 ^ (k + 1) = ((2 ^ k : ℕ) : ℚ) by push_cast; ring]
    exact Rat.den_natCast _
  · rw [zero_mul]; rfl

theorem singleCall_n (ω : ℚ) (j : ℕ) (S : Finset (Fin (width s g N))) : (G.singleCall ω j S).n = width s g N := by
  unfold singleCall; split_ifs <;> rfl

theorem termParts_den {B1 B2 : ℕ} (ctr : Counter B1 B2) (hD : Counter.DenOK ctr) (ω : ℚ) (w : List Bool)
    (ops : List (Bool × Atom)) :
    ((G.termParts P x ctr ω w ops).2.1 * 2 ^ (width s g N + 1)).den = 1 ∧
      ((G.termParts P x ctr ω w ops).2.2 * 2 ^ (width s g N + 1)).den = 1 := by
  have hs : ∀ (j : ℕ) (S : Finset (Fin (width s g N))),
      ((ctr.value (G.singleCall ω j S) w).1 * 2 ^ (width s g N + 1)).den = 1 ∧
        ((ctr.value (G.singleCall ω j S) w).2 * 2 ^ (width s g N + 1)).den = 1 := by
    intro j S; have h := hD (G.singleCall ω j S) w; rw [G.singleCall_n] at h; exact h
  have z : ((0 : ℚ) * 2 ^ (width s g N + 1)).den = 1 := by rw [zero_mul]; rfl
  unfold termParts
  split
  · exact ⟨parityMean_den _ _, z⟩
  · exact hs _ _
  · exact ⟨parityMean_den _ _, z⟩
  · exact hs _ _
  · exact hs _ _
  · split_ifs
    · exact ⟨z, z⟩
    · exact hD (G.pairCall ω _ _) w
  · refine ⟨z, ?_⟩
    rw [one_mul, show (2 : ℚ) ^ (width s g N + 1) = ((2 ^ (width s g N + 1) : ℕ) : ℚ) by push_cast; rfl]
    exact Rat.den_natCast _

theorem termList_den {B1 B2 : ℕ} (ctr : Counter B1 B2) (hD : Counter.DenOK ctr) (ω : ℚ) :
    ∀ y ∈ G.termList P x ctr ω,
      (y.2.1 * 2 ^ (width s g N + 1)).den = 1 ∧ (y.2.2 * 2 ^ (width s g N + 1)).den = 1 := by
  intro y hy
  unfold termList WorkerArith.gmList at hy
  obtain ⟨a, -, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hy
  exact G.termParts_den P x ctr hD ω _ _

noncomputable def verdictReq {B1 B2 : ℕ} (ctr : Counter B1 B2) (hD : Counter.DenOK ctr) (ω : ℚ) : VerdictReq where
  q := width s g N
  M := gadgets s g N
  N := nu N ^ (g.lenRoot + 1)
  rb := (pcpp s P g x G.oracle).randomBits
  cl := clauseWidth g.clauseDegree (width s g N)
  I := G.termList P x ctr ω
  hlen := G.termList_length P x ctr ω
  hden := G.termList_den P x ctr hD ω

theorem gadgets_pos : 0 < gadgets s g N := Nat.two_pow_pos _

theorem upperL_termList {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) :
    upperL (gadgets s g N) (G.termList P x ctr ω) =
      upperQ (fun (a : Fin (gadgets s g N)) t => G.termInterval P x ctr ω a.val t) := by
  unfold termList
  rw [WorkerArith.upperL_eq]
  congr 1
  funext a t
  exact G.flipI_termRaw P x ctr ω a.val t

theorem upperEstimate_eq {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) :
    G.upperEstimate P x ctr ω = ((upperL (gadgets s g N) (G.termList P x ctr ω) : ℚ) : ℝ) := by
  rw [G.upperL_termList P x ctr ω, upperQ_eq gadgets_pos]
  rfl

/-- **The verdict bit of the guess's request is the test of the meaning** (`Guess.Certified`, `sec:gadget-machine`), once
the set-up's guards hold. -/
theorem verdictBit_iff {B1 B2 : ℕ} (ctr : Counter B1 B2) (hD : Counter.DenOK ctr) (budget : ℕ → ℕ) (εT ω : ℚ)
    (hS : G.SetupOK x) :
    verdictBit P.gamma εT (G.verdictReq P x ctr hD ω) = true ↔ G.Certified P x ctr budget (εT : ℝ) ω := by
  unfold verdictBit Guess.Certified Guess.Guards
  rw [decide_eq_true_iff, G.upperEstimate_eq P x ctr ω]
  simp only [verdictReq]
  have hL : (Outer.instLength g.lenExp (nu N) : ℝ) = ((nu N ^ (g.lenRoot + 1) : ℕ) : ℝ) ^ 10 := by
    rw [GateParams.instLength_eq]; push_cast; rfl
  have hb : 1 ≤ nu N ^ (g.lenRoot + 1) ↔ 1 ≤ nu N := by
    constructor
    · intro h
      by_contra h0
      have : nu N = 0 := by omega
      rw [this, zero_pow (by omega)] at h
      omega
    · intro h
      exact Nat.one_le_pow _ _ h
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have h3' := hb.mp h3
    have hpos : (0 : ℝ) < (Outer.instLength g.lenExp (nu N) : ℝ) := by
      exact_mod_cast Outer.instLength_pos (G := g.lenExp) (nu N) h3'
    refine ⟨⟨h1, h2, h3', ?_, hS⟩, by exact_mod_cast h5⟩
    rw [div_lt_iff₀ hpos, hL]
    exact_mod_cast h4
  · rintro ⟨⟨h1, h2, h3, h4, -⟩, h5⟩
    have hpos : (0 : ℝ) < (Outer.instLength g.lenExp (nu N) : ℝ) := by
      exact_mod_cast Outer.instLength_pos (G := g.lenExp) (nu N) h3
    rw [div_lt_iff₀ hpos, hL] at h4
    exact ⟨h1, h2, hb.mpr h3, by exact_mod_cast h4, by exact_mod_cast h5⟩

end Guess

/-- **What the worker machine computes**: the set-up's flag (`Format.setupFlag`: both circuit fields decode, the set-up's
guards hold), then the verdict machine's bit on the request of the decoded guess (`Format.verdict`). -/
theorem verdict_eq_bit {B1 B2 : ℕ} (ctr : Counter B1 B2) (hD : Counter.DenOK ctr) (budget : ℕ → ℕ) (εT ω : ℚ)
    (N : ℕ) (x : BitInput N) (w : List Bool) :
    verdict s P g ctr budget εT ω N x w =
      (setupFlag s P g N x w && verdictBit P.gamma εT ((decodeGuess s P g N x w).verdictReq P x ctr hD ω)) := by
  classical
  unfold verdict
  cases hf : setupFlag s P g N x w
  · rfl
  · have hS : (decodeGuess s P g N x w).SetupOK x := by
      unfold setupFlag at hf
      rw [Bool.and_eq_true, decide_eq_true_iff] at hf
      exact hf.2
    simp only [Bool.true_and]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Guess.verdictBit_iff P x _ ctr hD budget εT ω hS]

end NearCubicGates.Close.Worker
