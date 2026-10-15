import Proof.Gates.Worker.Calls
import Proof.Gates.Counter.Main
import Proof.Circuits.CanonicalWitnessCodec

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.ExecutableInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.FiniteAverages NearCubicGates.Close.Counter
open NearCubicWires.RepairRepresentation

/-! ## `U` as an exact rational -/

/-- `U = 1 + (Σ_{a,t} (σ_t p̂ + κ̂)) / (2M)`. -/
def upperQ {M : ℕ} (I : Fin M → Fin 10 → ℚ × ℚ) : ℚ :=
  1 + (∑ a, ∑ t, ((tenSigns t : ℚ) * (I a t).1 + (I a t).2)) / (2 * M)

theorem upperQ_eq {M : ℕ} (hM : 0 < M) (I : Fin M → Fin 10 → ℚ × ℚ) : ((upperQ I : ℚ) : ℝ) = upper I := by
  unfold upperQ upper mean
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast
  rw [Fintype.card_fin, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

/-! ## The guess codec -/

/-- The witness prefixes of the `M` gadgets, in the order `(a, t) ↦ 10a + t`. -/
def witnessList {q : ℕ} (G : Guess q) (M : ℕ) : List (List Bool) :=
  (List.range (10 * M)).map fun i => G.witnesses (i / 10) ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The guess codec. -/
noncomputable def guessWordOf (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (N : ℕ) (x : BitInput N)
    (G : Guess (width s g N)) : List Bool :=
  natWord (encodeBooleanCircuit G.oracle.src) ++ natWord (encodeBooleanCircuit G.oracle.pf) ++
    listWord circuitWord ((List.range (G.auxCount P x)).map G.circuits) ++
    listWord (listWord bitWord) (witnessList G (gadgets s g N))

theorem encodeBooleanCircuit_injective {n : ℕ} : Function.Injective (encodeBooleanCircuit (n := n)) := by
  intro a b h
  have ha := CanonicalWitnessCodec.decodeBooleanCircuit_encode a
  have hb := CanonicalWitnessCodec.decodeBooleanCircuit_encode b
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem map_range_eq {α : Type*} {f g : ℕ → α} {n : ℕ} (h : (List.range n).map f = (List.range n).map g) :
    ∀ j < n, f j = g j := by
  intro j hj
  have := congrArg (fun l => l.getD j (f j)) h
  simpa [List.getD_eq_getElem?_getD, hj] using this

/-- Two guesses whose words are both prefixes of `bits` agree on the oracle, on the circuits below `auxCount`, and
on the witnesses of the `M` gadgets. -/
theorem guessWordOf_unique (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (N : ℕ) (x : BitInput N)
    (G G' : Guess (width s g N)) (bits : List Bool)
    (h : guessWordOf s P g N x G <+: bits) (h' : guessWordOf s P g N x G' <+: bits) :
    G.oracle = G'.oracle ∧ (∀ j < G.auxCount P x, G.circuits j = G'.circuits j) ∧
      (∀ a < gadgets s g N, ∀ t, G.witnesses a t = G'.witnesses a t) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨u', hu'⟩ := h'
  have heq := hu.trans hu'.symm
  unfold guessWordOf at heq
  simp only [List.append_assoc] at heq
  obtain ⟨hor, heq0⟩ := natWord_prefixCode _ _ _ _ heq
  obtain ⟨hor', heq1⟩ := natWord_prefixCode _ _ _ _ heq0
  have hO : G.oracle = G'.oracle :=
    Outer.OuterGuess.ext (encodeBooleanCircuit_injective hor) (encodeBooleanCircuit_injective hor')
  have haux : G.auxCount P x = G'.auxCount P x := by unfold Guess.auxCount; rw [hO]
  obtain ⟨hcs, heq2⟩ := listWord_prefixCode (circuitWord_prefixCode _) _ _ _ _ heq1
  obtain ⟨hws, -⟩ := listWord_prefixCode (listWord_prefixCode bitWord_prefixCode) _ _ _ _ heq2
  refine ⟨hO, ?_, ?_⟩
  · intro j hj
    rw [← haux] at hcs
    exact map_range_eq hcs j hj
  · intro a ha t
    have := map_range_eq (f := fun i => G.witnesses (i / 10) ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩)
      (g := fun i => G'.witnesses (i / 10) ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩) hws (10 * a + t.val) (by omega)
    have h1 : (10 * a + t.val) / 10 = a := by omega
    have h2 : (⟨(10 * a + t.val) % 10, Nat.mod_lt _ (by norm_num)⟩ : Fin 10) = t := by ext; simp
    simp only [h1, h2] at this
    exact this

/-! ## Everything the test reads is determined by the encoded data -/

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)

theorem operands_congr (G G' : Guess (width s g N)) (hO : G.oracle = G'.oracle) (a : ℕ) (t : Fin 10) :
    G.operands P x a t = G'.operands P x a t := by
  obtain ⟨o, c, w⟩ := G
  obtain ⟨o', c', w'⟩ := G'
  simp only at hO
  subst hO
  rfl

theorem intervalOf_congr {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (G G' : Guess (width s g N))
    (hO : G.oracle = G'.oracle) (w : List Bool) (ops : List (Bool × Atom))
    (hc : ∀ j, Atom.aux j ∈ ops.map Prod.snd → G.circuits j = G'.circuits j) :
    G.intervalOf P x ctr ω w ops = G'.intervalOf P x ctr ω w ops := by
  obtain ⟨o, c, w0⟩ := G
  obtain ⟨o', c', w0'⟩ := G'
  simp only at hO
  subst hO
  unfold intervalOf singleCall pairCall
  dsimp only
  generalize ops.foldl (fun f o => xor f o.1) false = fl
  generalize ops.map Prod.snd = as at hc ⊢
  simp only at hc
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩
  · rfl
  · cases a₁ with
    | sys u => rfl
    | aux j => simp only; rw [hc j (by simp)]
  · cases a₁ with
    | sys u =>
      cases a₂ with
      | sys v => rfl
      | aux j => simp only; rw [hc j (by simp)]; rfl
    | aux i =>
      cases a₂ with
      | sys u => simp only; rw [hc i (by simp)]; rfl
      | aux j => simp only; rw [hc i (by simp), hc j (by simp)]
  · cases a₁ <;> cases a₂ <;> rfl

theorem termInterval_congr {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (G G' : Guess (width s g N))
    (hO : G.oracle = G'.oracle) (hc : ∀ j < G.auxCount P x, G.circuits j = G'.circuits j)
    (hw : ∀ a < gadgets s g N, ∀ t, G.witnesses a t = G'.witnesses a t) (a : ℕ) (ha : a < gadgets s g N)
    (t : Fin 10) : G.termInterval P x ctr ω a t = G'.termInterval P x ctr ω a t := by
  unfold termInterval
  rw [hw a ha t, ← operands_congr P x G G' hO a t]
  apply intervalOf_congr P x ctr ω G G' hO
  intro j hj
  obtain ⟨o, ho, hoj⟩ := List.mem_map.1 hj
  exact hc j (G.operands_aux_lt P x a ha t o ho j hoj)

theorem guards_congr {B1 B2 : ℕ} (ctr : Counter B1 B2) (budget : ℕ → ℕ) (ε : ℝ) (G G' : Guess (width s g N))
    (hO : G.oracle = G'.oracle) (_hc : ∀ j < G.auxCount P x, G.circuits j = G'.circuits j)
    (_hw : ∀ a < gadgets s g N, ∀ t, G.witnesses a t = G'.witnesses a t) :
    G.Guards P x ctr budget ε ↔ G'.Guards P x ctr budget ε := by
  unfold Guards SetupOK PairOK
  rw [hO]

theorem upperEstimate_congr {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (G G' : Guess (width s g N))
    (hO : G.oracle = G'.oracle) (hc : ∀ j < G.auxCount P x, G.circuits j = G'.circuits j)
    (hw : ∀ a < gadgets s g N, ∀ t, G.witnesses a t = G'.witnesses a t) :
    G.upperEstimate P x ctr ω = G'.upperEstimate P x ctr ω := by
  unfold upperEstimate
  congr 1
  funext a t
  exact termInterval_congr P x ctr ω G G' hO hc hw a.val a.isLt t

end Guess

/-- Two guesses agree on everything the test reads: the oracle, the circuits below `auxCount`, the witnesses of
the `M` gadgets. -/
def Guess.Agree (P : ThreeQueryPCPP) {s : GateSources} {g : GateParams} {N : ℕ} (x : BitInput N)
    (G G' : Guess (width s g N)) : Prop :=
  G.oracle = G'.oracle ∧ (∀ j < G.auxCount P x, G.circuits j = G'.circuits j) ∧
    (∀ a < gadgets s g N, ∀ t, G.witnesses a t = G'.witnesses a t)

/-- **The test reads only the agreed data.** -/
theorem certified_of_agree (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ}
    (ctr : Counter B1 B2) (budget : ℕ → ℕ) (ε : ℝ) (ω : ℚ) {N : ℕ} (x : BitInput N) (G G' : Guess (width s g N))
    (h : Guess.Agree P x G' G) : G'.Certified P x ctr budget ε ω ↔ G.Certified P x ctr budget ε ω := by
  obtain ⟨hO, hc, hw⟩ := h
  unfold Guess.Certified
  rw [Guess.guards_congr P x ctr budget ε _ G hO hc hw, Guess.upperEstimate_congr P x ctr ω _ G hO hc hw]

end NearCubicGates.Close.Worker
