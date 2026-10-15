import Proof.Wire_3_5.SplitFree
import Proof.Wire_3_5.UnionMachineSlack
import Proof.Wire_3_5.UnionMachineSchedLoop
import Proof.Wire_3_5.SelectionMachineContract
import Proof.MachineModel.Layout

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

section Consts
variable (l : Literals)

noncomputable def kU : ℕ := gateDver l + 1

noncomputable def aU : ℕ := gateDver l + 1

theorem haU : aU l ≤ kU l + 1 := by unfold aU kU; omega

end Consts

/-- The rounding precision `p(q) = ⌈log₂(q+2)⌉`: `2^{−p} ≤ 1/(q+2)`, and `2^p ≤ 2(q+2)` keeps the
rounding and the accumulation polynomial in `q`. -/
def unionBits (q : ℕ) : ℕ := Nat.clog 2 (q + 2)

section Worker
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

def workerMeaning (S : UnionSetup I) (P : FusedPrimitive I) (onset : ℕ) (callOk : PrimRequest → Bool) :
    (n : ℕ) → BitInput n → List Bool → Prop :=
  fun n x w => onset ≤ n ∧ unionSlackRun S x UnionGuess.translation callOk P unionBits w = true

structure WorkerAt (S : UnionSetup I) (P : FusedPrimitive I) where
  t : ℕ
  s : ℕ
  p : Machine t s
  ht : 2 ≤ t
  result : Fin t
  fuel : ℕ → ℕ
  onset : ℕ
  callOk : PrimRequest → Bool
  run : WitnessRun p ht result fuel (workerMeaning S P onset callOk)
  hok : ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), ∀ r ∈ (g.checkData g.translation).schedule,
    callOk r = true ↔ I.Call r
  time : ∀ N, B.onset ≤ N → fuel N + 2 ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N)

structure SetupFacts (S : UnionSetup I) (L : Language) : Prop where
  lang : S.language = L
  hη : 0 < (S.params.outerError : ℝ)
  hw : Tendsto (fun N => S.pcp.nativeWidth N) atTop atTop
  hD : ∀ᶠ q : ℕ in atTop, (1 + (S.gridMass q : ℝ)) ^ 4 * ((q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ unionBits q) +
      (slackOf (S.gridMass q) (unionBits q) : ℝ) ≤ (S.params.eps0 : ℝ)

def AcceptsCall (S : UnionSetup I) (P : FusedPrimitive I) : Prop :=
  ∀ N (z : BitInput N) (g : UnionGuess S z), UnionAccepts S P z g → ∃ req, I.Call req

variable {S : UnionSetup I} {P : FusedPrimitive I}

namespace WorkerAt

/-- The worker's weak machine. -/
noncomputable def machine (W : WorkerAt S P) : OrdinaryWeakMachine := weakOf W.p W.ht W.result W.fuel _ W.run

/-- **Slack soundness** of the worker's machine (unionSlackRun_sound). -/
theorem soundForSlack (W : WorkerAt S P) : SoundForSlack S P unionBits W.machine := by
  intro N z hacc
  obtain ⟨w, hon, hrun⟩ := (weakOf_accepts W.p W.ht W.result W.fuel _ W.run N z).1 hacc
  exact unionSlackRun_sound P unionBits W.callOk (W.hok N hon z) _ hrun

/-- **`tr:soundness`**: the worker's machine is one-sided for the setup's language. -/
theorem oneSided (W : WorkerAt S P) {L : Language} (hF : SetupFacts S L) : OneSided W.machine L := by
  have h := oneSided_of_soundForSlack S P unionBits W.machine W.soundForSlack hF.hη hF.hw hF.hD
  rwa [hF.lang] at h

/-- **Eventual `tr:completeness`**: past the worker's onset every accepting guess is accepted
(unionSlackRun_complete at the `⌊N/16⌋`-bit witness). -/
theorem complete (W : WorkerAt S P) : CompleteForEventually S P W.machine := by
  refine ⟨W.onset, fun N hN z g hg => ?_⟩
  obtain ⟨w, hlen, hrun⟩ := unionSlackRun_complete P unionBits W.callOk g (W.hok N hN z g) hg (N / 16) le_rfl
  refine (weakOf_accepts W.p W.ht W.result W.fuel _ W.run N z).2 ⟨fun i => w.get ⟨i.val, by omega⟩, hN, ?_⟩
  have hw : List.ofFn (fun i : Fin (N / 16) => w.get ⟨i.val, by omega⟩) = w := by
    apply List.ext_get
    · simp [hlen]
    · intro n h1 h2; simp
  rw [hw]
  exact hrun

/-- **`tr:time`**: the worker's machine meets the ledger's split. -/
theorem split (W : WorkerAt S P) : B.Split W.machine := fun N hN => W.time N hN

end WorkerAt

end Worker

section Leaf
variable (l : Literals)

/-- The inputs of the union at the gate: clock `kU`, source work `A·(N+1)^{aU}`, coefficient `coef`. -/
noncomputable abbrev IU (F : GateFree l) (coef A : ℕ) := (gate0 l F).inputs (kU l) coef A (aU l) (haU l)

/-- The pinned setup at a language of the clock. -/
noncomputable abbrev SU (F : GateFree l) (coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kU l + 2)) L) :
    UnionSetup (IU l F coef A) :=
  setupF l F (kU l) coef A (aU l) (haU l) L hL

/-- **Residual (setup facts)** at every free choice, coefficient, source work and language. -/
def SetupFactsF : Prop :=
  ∀ (F : GateFree l) (coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kU l + 2)) L),
    SetupFacts (SU l F coef A L hL) L

/-- **Residual (an accepting guess calls)** at every free choice, coefficient, source work, language and primitive. -/
def AcceptsCallF : Prop :=
  ∀ (F : GateFree l) (coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kU l + 2)) L)
    (P : FusedPrimitive (IU l F coef A)), AcceptsCall (SU l F coef A L hL) P

def WorkersF (F : GateFree l) : Type :=
  Σ A : ℕ, Σ' _ : 3 ≤ A, ∀ (coef : ℕ), 1 ≤ coef → ∀ (P : FusedPrimitive (IU l F coef A)) (L : Language)
    (hL : InNTIME (fun n => n ^ (kU l + 2)) L), WorkerAt (SU l F coef A L hL) P

theorem rejectAll_runtime (N : ℕ) : rejectAll.runtime N = 3 := rfl

/-- The coefficient-`0` branch: the machine rejects everything; completeness is vacuous (`Free.coef_pos`). -/
noncomputable def leafAtZero (F : GateFree l) (coef A : ℕ) (hA : 3 ≤ A) (hc : ¬ 1 ≤ coef)
    (acc : AcceptsCallF l) :
    UnionLeafAt (IU l F coef A) (fun L hL => SU l F coef A L hL) where
  build := fun _ _ => rejectAll
  soundness := fun _ _ _ => ⟨0, fun n _ x h => absurd h (rejectAll_rejects n x)⟩
  time := fun _ _ N _ => by
    rw [rejectAll_runtime]
    have h1 : 1 ≤ (N + 1) ^ aU l := Nat.one_le_pow _ _ (Nat.succ_pos N)
    have : 3 ≤ A * (N + 1) ^ aU l := le_trans hA (Nat.le_mul_of_pos_right _ h1)
    exact le_trans this (Nat.le_add_right _ _)
  complete := fun P L hL => ⟨0, fun N _ z g hg => by
    obtain ⟨req, hreq⟩ := acc F coef A L hL P N z g hg
    exact absurd (Free.coef_pos l F P req hreq) hc⟩

/-- The positive-coefficient branch: the worker's machine on the languages of the clock. -/
noncomputable def leafAtPos (F : GateFree l) (coef A : ℕ) (facts : SetupFactsF l)
    (W : ∀ (P : FusedPrimitive (IU l F coef A)) (L : Language) (hL : InNTIME (fun n => n ^ (kU l + 2)) L),
      WorkerAt (SU l F coef A L hL) P) (hA : 3 ≤ A) :
    UnionLeafAt (IU l F coef A) (fun L hL => SU l F coef A L hL) := by
  classical
  exact
  { build := fun P L => if hL : InNTIME (fun n => n ^ (kU l + 2)) L then (W P L hL).machine else rejectAll
    soundness := fun P L hL => by
      rw [dif_pos hL]
      exact (W P L hL).oneSided (facts F coef A L hL)
    time := fun P L N hN => by
      by_cases hL : InNTIME (fun n => n ^ (kU l + 2)) L
      · rw [dif_pos hL]
        exact (W P L hL).split N hN
      · rw [dif_neg hL, rejectAll_runtime]
        have h1 : 1 ≤ (N + 1) ^ aU l := Nat.one_le_pow _ _ (Nat.succ_pos N)
        have : 3 ≤ A * (N + 1) ^ aU l := le_trans hA (Nat.le_mul_of_pos_right _ h1)
        exact le_trans this (Nat.le_add_right _ _)
    complete := fun P L hL => by
      show CompleteForEventually _ P (if hL : InNTIME (fun n => n ^ (kU l + 2)) L then (W P L hL).machine
        else rejectAll)
      rw [dif_pos hL]
      exact (W P L hL).complete }

noncomputable def unionLeafF_of_workers (facts : SetupFactsF l) (acc : AcceptsCallF l)
    (W : ∀ F : GateFree l, GateFreeOK l F → WorkersF l F) : UnionLeafF l := fun F hF =>
  ⟨kU l, (W F hF).1, aU l, haU l, fun coef =>
    if hc : 1 ≤ coef then leafAtPos l F coef (W F hF).1 facts ((W F hF).2.2 coef hc) (W F hF).2.1
    else leafAtZero l F coef (W F hF).1 (W F hF).2.1 hc acc⟩

end Leaf

/-! ## Layer B: the worker from its stages -/

/-! ### C1, at its own envelope -/

/-- **C1's input word**, fixed by the union (which writes it): `n`, `r`, the gates (their weights, then their
threshold), the populations (their gate indices, then their weight `p_X`). -/
def selWord (R : NearCubicWires.WireExponent3_5.Machine.SelectionReq) : List Bool :=
  natWord R.n ++ natWord R.r ++ natWord R.gates.length ++
    R.gates.flatMap (fun g => (List.ofFn fun i => intWord (g.weights i)).flatten ++ intWord g.threshold) ++
    natWord R.pops.length ++ R.pops.flatMap (fun X => natListWord X.1 ++ ratWord X.2)

/-- **C1's output word**, fixed by the union (which reads it): the selected coset's syndrome codes, the same
`natListWord` the request word carries as its translation (`PrimRequest.word`). -/
def cosetWord (c : NearCubicWires.WireExponent3_5.Machine.S0Defs.Coset) : List Bool := natListWord c

def c1sized (d : ℕ) (E₁ : Envelope) (c₁ : ℕ) : NearCubicWires.WireExponent3_5.Machine.MachineContract E₁ :=
  { NearCubicWires.WireExponent3_5.SelectionMachine.c1inst E₁ cosetWord selWord (fun _ => 0) c₁ with
    pre := fun R => (NearCubicWires.WireExponent3_5.SelectionMachine.c1inst E₁ cosetWord selWord (fun _ => 0) c₁).pre R ∧
      (selWord R).length ≤ (R.n + 1) ^ d }

structure C1At (d : ℕ) where
  E₁ : Envelope
  c₁ : ℕ
  impl : NearCubicWires.WireExponent3_5.Machine.Implements (c1sized d E₁ c₁)

def C1Impl : Type := ∀ d : ℕ, C1At d

/-- The budget of one docked C1 call at native width `q`: C1's selection class at its own envelope, at the ledger's
star width `kOf q` (its contract's budget at `n = q`, `r = rOf q`). -/
def C1At.budgetAt {d : ℕ} (c : C1At d) {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ :=
  c.c₁ * classBound c.E₁ .selection q (B.kOf q) 0

/-! ### The stages' layout -/

section Stages
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

noncomputable abbrev NL : ℕ := Sched.NA P + 1 + 1

/-- The worker's tapes: the refuter's input (`0`) and witness (`1`), the loop's bank, then the front's own `tf`. -/
noncomputable abbrev NW (tf : ℕ) : ℕ := 2 + NL P + tf

/-- The loop bank's slots in the worker. -/
noncomputable def lp (tf : ℕ) (i : Fin (NL P)) : Fin (NW P tf) :=
  ⟨2 + i.val, by have := i.isLt; show 2 + i.val < 2 + NL P + tf; omega⟩

theorem two_le_NW (tf : ℕ) : 2 ≤ NW P tf := by show 2 ≤ 2 + NL P + tf; omega

theorem lp_inj (tf : ℕ) : Function.Injective (lp P tf) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [lp] at this
  exact Fin.ext (by omega)

noncomputable def cellSlot : Fin (NL P) := Scrub.inner (Sched.fx P 1)

/-- The loop bank's heads at kept data `K`. -/
noncomputable def bankH (K : Sched.Kept) : Fin (NL P) → ℕ := Scrub.heads (Sched.iterH P K)

/-- The loop bank's tapes at kept data `K`: registers of capacity `cap`, scratch blank at `R`, log `Lg`, driver `R`. -/
noncomputable def bankA (cap R Lg : ℕ) (K : Sched.Kept) : Fin (NL P) → List Bool :=
  Scrub.bank (Scrub.blank (Sched.scr P) (Sched.iterA P cap K) R) R Lg

end Stages

/-- The worker's entry tapes: base's `Verifier.inputTapes` (framed input, framed witness, blank). -/
def entryA {u N : ℕ} (x : BitInput N) (w : List Bool) : Fin u → List Bool :=
  fun i => if i.val = 0 then RepairOrdinary.frame (List.ofFn x) else if i.val = 1 then RepairOrdinary.frame w else []

def decisionOf (acc : Fin 6 → ℕ) : Bool :=
  decide (acc 0 ≤ acc 1) && decide (acc 2 ≤ acc 3) && decide (acc 5 ≤ acc 4)

/-! ### Residual U7: the decision -/

section Decide
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

structure DecideAt (Kd : ℕ) where
  sd : ℕ
  M : Machine (NL P) sd
  cost : ℕ → ℕ
  hcost : ∀ cap, cost cap ≤ Kd * (cap + 1)
  run : ∀ (cap R Lg : ℕ) (K : Sched.Kept), 1 ≤ cap → (∀ i, K.acc i ≤ cap) → ∃ (Hd : Fin (NL P) → ℕ)
    (Ad : Fin (NL P) → List Bool), Step M (cost cap) (bankH P K) (bankA P cap R Lg K) Hd Ad ∧
      readTapeBit (Ad (cellSlot P)) (Hd (cellSlot P)) = decisionOf K.acc

end Decide

/-- **Residual U7** at every ledger and primitive, with one constant `Kd`. -/
def DecideF : Type :=
  Σ Kd : ℕ, ∀ {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I),
    DecideAt P Kd

/-! ### Residual U0–U5: the front -/

section Front
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

structure LoopHyps (cap R Lg p n0 Mm Wm : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (Sched.TEntry I)) : Prop where
  hn : ∀ t ∈ Ls, t.req.1.n = n0
  hM : ∀ t ∈ Ls, t.e.mag ≤ Mm
  hW : ∀ t ∈ Ls, t.e.word.length ≤ Wm
  hcapR : 2 * Wm + Mm + 2 ≤ cap
  hcapD : 4 * (2 * B.callBudget n0 + 3) + 8 * 2 ^ p + 20 ≤ cap
  hcapA : ∀ i, acc0 i + (Ls.length + 2) * (Mm * (8 * 2 ^ p)) ≤ cap
  hR1 : cap + 1 ≤ R
  hR2 : Sched.stageCost Mm Wm (B.callBudget n0) (2 * B.callBudget n0 + 3) p + 1 ≤ R
  hL : R + 1 ≤ Lg

/-- The front's reference output at one input and witness: the call table (admissible entries), the accumulators'
start (the slack thresholds, or the rejecting pattern), the rounding precision in the rounding register (`unionBits q`
on a table the loop runs), the loop's capacities and the table's entry bounds. -/
structure FrontOut (I : PrimitiveInputs B) where
  table : List (Sched.TEntry I)
  acc0 : Fin 6 → ℕ
  p : ℕ
  cap : ℕ
  R : ℕ
  Lg : ℕ
  Mm : ℕ
  Wm : ℕ

variable (P : FusedPrimitive I)

/-- The loop's kept data at its entry. -/
noncomputable def FrontOut.kept (o : FrontOut I) : Sched.Kept := Sched.KOf P o.p o.acc0 o.table 0

/-- The loop's kept data at its exit. -/
noncomputable def FrontOut.keptEnd (o : FrontOut I) : Sched.Kept :=
  Sched.KOf P o.p o.acc0 o.table o.table.length

def FrontOut.loopSteps (o : FrontOut I) (n0 : ℕ) : ℕ :=
  o.table.length * (Sched.loopCost o.Mm o.Wm (B.callBudget n0) o.p o.R + 2) + 1

structure FrontAt (S : UnionSetup I) {d : ℕ} (c1 : C1At d) (Af Kf N₀ : ℕ) where
  tf : ℕ
  sf : ℕ
  M : Machine (NW P tf) sf
  cost : ℕ → ℕ
  onset : ℕ
  honset : N₀ ≤ onset
  callOk : PrimRequest → Bool
  hok : ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), ∀ r ∈ (g.checkData g.translation).schedule,
    callOk r = true ↔ I.Call r
  out : (N : ℕ) → BitInput N → List Bool → FrontOut I
  run : ∀ N (x : BitInput N) (w : List Bool), ∃ (Hf : Fin (NW P tf) → ℕ) (Af' : Fin (NW P tf) → List Bool),
    Step M (cost N) (fun _ => 0) (entryA x w) Hf Af' ∧
    (∀ i, Hf (lp P tf i) = bankH P ((out N x w).kept P) i) ∧
    (∀ i, Af' (lp P tf i) =
      bankA P (out N x w).cap (out N x w).R (out N x w).Lg ((out N x w).kept P) i)
  loop : ∀ N (x : BitInput N) (w : List Bool), (out N x w).table ≠ [] →
    LoopHyps (out N x w).cap (out N x w).R (out N x w).Lg (out N x w).p (B.q N) (out N x w).Mm (out N x w).Wm
      (out N x w).acc0 (out N x w).table
  capPos : ∀ N (x : BitInput N) (w : List Bool), 1 ≤ (out N x w).cap
  accFit : ∀ N (x : BitInput N) (w : List Bool) i,
    ((out N x w).keptEnd P).acc i ≤ (out N x w).cap
  sem : ∀ N (x : BitInput N) (w : List Bool),
    decisionOf ((out N x w).keptEnd P).acc = true ↔ workerMeaning S P onset callOk N x w
  rej : ∀ N (x : BitInput N) (w : List Bool), N < onset → (out N x w).table = [] ∧ (out N x w).cap = 1
  costRej : ∀ N, B.onset ≤ N → N < onset → cost N ≤ Af * (N + 1) ^ B.a
  costAcc : ∀ N, B.onset ≤ N → onset ≤ N → cost N ≤ Af * (N + 1) ^ B.a +
    Kf * (B.q N + 1) ^ (callDegMargin - 1) * (B.callBudget (B.q N) + c1.budgetAt B (B.q N))
  len : ∀ N (x : BitInput N) (w : List Bool), onset ≤ N → (out N x w).table ≠ [] → ∃ g : UnionGuess S x,
    g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) ∧
      (out N x w).table.length ≤ (g.checkData g.translation).schedule.length
  perCall : ∀ N (x : BitInput N) (w : List Bool), onset ≤ N → (out N x w).table ≠ [] →
    Sched.loopCost (out N x w).Mm (out N x w).Wm (B.callBudget (B.q N)) (out N x w).p (out N x w).R + 2 ≤
      Kf * (B.q N + 1) ^ (callDegMargin - 1) * B.callBudget (B.q N)
  capAcc : ∀ N (x : BitInput N) (w : List Bool), onset ≤ N →
    (out N x w).cap + 1 ≤ Kf * (B.q N + 1) ^ (callDegMargin - 1) * B.callBudget (B.q N)

end Front

def FrontsF (l : Literals) (F : GateFree l) : Type :=
  Σ Af : ℕ, ∀ (coef : ℕ), 1 ≤ coef → ∀ (A : ℕ) (P : FusedPrimitive (IU l F coef A)) (L : Language)
    (hL : InNTIME (fun n => n ^ (kU l + 2)) L), Σ d : ℕ, ∀ c1 : C1At d, Σ Kf : ℕ, ∀ N₀ : ℕ,
      FrontAt P (SU l F coef A L hL) c1 Af Kf N₀

def CallCountF (l : Literals) : Prop :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (F : GateFree l) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L),
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (setupF l F kclk coef A a ha L hL) z),
      g.oracle.size ≤ oracleSizeBound (setupF l F kclk coef A a ha L hL).G
        ((setupF l F kclk coef A a ha L hL).pcp.nativeWidth N) → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ ((gate0 l F).budget kclk coef A a ha).q N ^ unionCallDeg l

/-! ### The worker: front, loop, decision -/

section Assembly
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {P : FusedPrimitive I}
  {S : UnionSetup I} {d₁ : ℕ} {c1 : C1At d₁} {Af Kf N₀ Kd : ℕ}

/-- **The worker's machine**: the front, then the schedule loop docked at the bank's slots, then the decision docked
at the same slots. -/
noncomputable def workerMachine (fr : FrontAt P S c1 Af Kf N₀) (dc : DecideAt P Kd) :=
  Composition.machine fr.M (Composition.machine (RecoveryFocus.machine (lp P fr.tf) (Sched.loopM P))
    (RecoveryFocus.machine (lp P fr.tf) dc.M))

theorem loop_step (o : FrontOut I) (n0 : ℕ)
    (h : o.table ≠ [] → LoopHyps o.cap o.R o.Lg o.p n0 o.Mm o.Wm o.acc0 o.table) :
    Step (Sched.loopM P) (o.loopSteps n0) (bankH P (o.kept P)) (bankA P o.cap o.R o.Lg (o.kept P))
      (bankH P (o.keptEnd P)) (bankA P o.cap o.R o.Lg (o.keptEnd P)) := by
  by_cases h0 : o.table = []
  · have hs0 : Sched.scr P (Sched.fx P 0) = false := by simp [Sched.scr, Sched.keptV, Sched.fx_val]
    have hlen : o.table.length = 0 := by rw [h0]; rfl
    have hw := whileRun (Sched.loopBody P) (Scrub.inner (Sched.fx P 0)) 0
      (Sched.loopCost o.Mm o.Wm (B.callBudget n0) o.p o.R)
      (fun j => bankH P (Sched.KOf P o.p o.acc0 o.table j))
      (fun j => bankA P o.cap o.R o.Lg (Sched.KOf P o.p o.acc0 o.table j))
      (fun j hj => absurd hj (Nat.not_lt_zero j))
      (by
        simp only [bankA, bankH, Scrub.bank_inner, Scrub.heads_inner, Scrub.blank, hs0, Bool.false_eq_true,
          ↓reduceIte, Sched.iterA_fx, Sched.iterH_fx, Sched.fixedA, Sched.fixedH, Sched.KOf]
        have := Sched.tbl_end o.table
        rw [hlen] at this
        exact this)
      (fun j hj => absurd hj (Nat.not_lt_zero j))
    unfold FrontOut.loopSteps FrontOut.kept FrontOut.keptEnd
    rw [hlen]
    exact hw
  · have hy := h h0
    exact Sched.sched_loop P o.cap o.R o.Lg o.p n0 o.Mm o.Wm o.acc0 o.table hy.hn hy.hM hy.hW hy.hcapR hy.hcapD
      hy.hcapA hy.hR1 hy.hR2 hy.hL

/-- **The worker's run on one input and witness**: front, loop, decision, with the decision on the result cell. -/
theorem worker_step (fr : FrontAt P S c1 Af Kf N₀) (dc : DecideAt P Kd) (N : ℕ) (x : BitInput N) (w : List Bool) :
    ∃ (Hend : Fin (NW P fr.tf) → ℕ) (Aend : Fin (NW P fr.tf) → List Bool),
      Step (workerMachine fr dc) (fr.cost N + 1 + ((fr.out N x w).loopSteps (B.q N) + 1 +
        dc.cost (fr.out N x w).cap)) (fun _ => 0) (entryA x w) Hend Aend ∧
      readTapeBit (Aend (lp P fr.tf (cellSlot P))) (Hend (lp P fr.tf (cellSlot P))) =
        decisionOf ((fr.out N x w).keptEnd P).acc := by
  obtain ⟨Hf, Af', hfront, hH, hA⟩ := fr.run N x w
  set o := fr.out N x w with ho
  have hinj := lp_inj P fr.tf
  have hloop := (loop_step o (B.q N) (fr.loop N x w)).dock (lp P fr.tf) hinj Hf Af' hH hA
  obtain ⟨Hd, Ad, hdec, hbit⟩ := dc.run o.cap o.R o.Lg (o.keptEnd P) (fr.capPos N x w) (fr.accFit N x w)
  have hdecD := hdec.dock (lp P fr.tf) hinj
    (dockH (lp P fr.tf) Hf (bankH P (o.keptEnd P))) (install (lp P fr.tf) Af' (bankA P o.cap o.R o.Lg (o.keptEnd P)))
    (fun j => dockH_slot (lp P fr.tf) hinj _ _ j) (fun j => install_slot (lp P fr.tf) hinj _ _ j)
  refine ⟨_, _, hfront.seq (hloop.seq hdecD), ?_⟩
  rw [dockH_slot (lp P fr.tf) hinj, install_slot (lp P fr.tf) hinj]
  exact hbit

/-- The per-witness tail of the worker's run: the loop and the decision. -/
def tailSteps (fr : FrontAt P S c1 Af Kf N₀) (dc : DecideAt P Kd) (N : ℕ) (x : BitInput N) (w : List Bool) : ℕ :=
  (fr.out N x w).loopSteps (B.q N) + 1 + dc.cost (fr.out N x w).cap

/-- **The worker's fuel**: the front, then the longest tail over the inputs and `⌊N/16⌋`-bit witnesses. -/
noncomputable def workerFuel (fr : FrontAt P S c1 Af Kf N₀) (dc : DecideAt P Kd) (N : ℕ) : ℕ :=
  fr.cost N + 1 + Finset.univ.sup (fun xw : BitInput N × BitInput (N / 16) => tailSteps fr dc N xw.1 (List.ofFn xw.2))

/-- **The worker realizes its meaning** on every input and witness (the result cell is the loop bank's cell). -/
theorem worker_run (fr : FrontAt P S c1 Af Kf N₀) (dc : DecideAt P Kd) :
    WitnessRun (workerMachine fr dc) (two_le_NW P fr.tf) (lp P fr.tf (cellSlot P)) (workerFuel fr dc)
      (workerMeaning S P fr.onset fr.callOk) := by
  intro n x w
  obtain ⟨Hend, Aend, hstep, hbit⟩ := worker_step fr dc n x (List.ofFn w)
  have hle : fr.cost n + 1 + tailSteps fr dc n x (List.ofFn w) ≤ workerFuel fr dc n :=
    Nat.add_le_add_left (Finset.le_sup (f := fun xw : BitInput n × BitInput (n / 16) =>
      tailSteps fr dc n xw.1 (List.ofFn xw.2)) (Finset.mem_univ (x, w))) _
  obtain ⟨r, hr, hh, ht, _⟩ := hstep.enlarge hle
  refine ⟨r, hr, ?_⟩
  show readTapeBit (r.final.tapes _) (r.final.heads _) = true ↔ _
  rw [hh, ht, hbit]
  exact fr.sem n x (List.ofFn w)

theorem worker_time (fr : FrontAt P S c1 Af Kf N₀) (dc : DecideAt P Kd) (hKd : ∀ cap, dc.cost cap ≤ Kd * (cap + 1))
    (d : ℕ) (hA : Af + 2 * Kd + 8 ≤ B.A)
    (hcount : ∀ N, N₀ ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z),
      g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ B.q N ^ d)
    (habs : ∀ N, N₀ ≤ N → Kf * (3 + Kd) * (B.q N + 1) ^ (d + (callDegMargin - 1)) ≤ B.q N ^ E.callDeg)
    (hsel : ∀ N, N₀ ≤ N → c1.budgetAt B (B.q N) ≤ B.callBudget (B.q N)) :
    ∀ N, B.onset ≤ N → workerFuel fr dc N + 2 ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N) := by
  intro N hN
  have hpow : 1 ≤ (N + 1) ^ B.a := Nat.one_le_pow _ _ (Nat.succ_pos N)
  have h3 : (Af + 2 * Kd + 8) * (N + 1) ^ B.a ≤ B.A * (N + 1) ^ B.a := Nat.mul_le_mul_right _ hA
  have h4 : Af * (N + 1) ^ B.a + (2 * Kd + 8) ≤ (Af + 2 * Kd + 8) * (N + 1) ^ B.a := by
    have : 2 * Kd + 8 ≤ (2 * Kd + 8) * (N + 1) ^ B.a := Nat.le_mul_of_pos_right _ hpow
    nlinarith
  by_cases hon : N < fr.onset
  · -- rejected outright: the empty table, a small bank
    have htail : ∀ xw : BitInput N × BitInput (N / 16), tailSteps fr dc N xw.1 (List.ofFn xw.2) ≤
        2 + 2 * Kd := by
      intro xw
      obtain ⟨hnil, hcap⟩ := fr.rej N xw.1 (List.ofFn xw.2) hon
      have h1 := hKd (fr.out N xw.1 (List.ofFn xw.2)).cap
      rw [hcap] at h1
      unfold tailSteps FrontOut.loopSteps
      rw [hnil, hcap]
      simp only [List.length_nil, zero_mul, zero_add]
      omega
    have hsup := Finset.sup_le (fun xw (_ : xw ∈ Finset.univ) => htail xw)
    have hc := fr.costRej N hN hon
    unfold workerFuel
    have h5 : B.A * (N + 1) ^ B.a ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N) :=
      Nat.le_add_right _ _
    omega
  · -- past the onset: the calls
    have hon' : fr.onset ≤ N := Nat.le_of_not_lt hon
    have hN₀ : N₀ ≤ N := le_trans fr.honset hon'
    obtain ⟨q, hq⟩ : ∃ q, B.q N = q := ⟨_, rfl⟩
    have htail : ∀ xw : BitInput N × BitInput (N / 16), tailSteps fr dc N xw.1 (List.ofFn xw.2) ≤
        2 + (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by
      intro xw
      have hd1 := hKd (fr.out N xw.1 (List.ofFn xw.2)).cap
      have hcapA := fr.capAcc N xw.1 (List.ofFn xw.2) hon'
      rw [hq] at hcapA
      have hd2 : dc.cost (fr.out N xw.1 (List.ofFn xw.2)).cap ≤
          Kd * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) :=
        le_trans hd1 (Nat.mul_le_mul_left _ hcapA)
      have hloop : (fr.out N xw.1 (List.ofFn xw.2)).loopSteps q ≤
          q ^ d * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) + 1 := by
        unfold FrontOut.loopSteps
        by_cases h0 : (fr.out N xw.1 (List.ofFn xw.2)).table = []
        · rw [h0]; simp
        · obtain ⟨g, hsize, hlen⟩ := fr.len N xw.1 (List.ofFn xw.2) hon' h0
          have hc := hcount N hN₀ xw.1 g hsize g.translation
          have hper := fr.perCall N xw.1 (List.ofFn xw.2) hon' h0
          rw [hq] at hc hper
          have := Nat.mul_le_mul (hlen.trans hc) hper
          omega
      unfold tailSteps
      rw [hq]
      have e : (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) =
          q ^ d * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) +
            Kd * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by ring
      omega
    have hsup := Finset.sup_le (fun xw (_ : xw ∈ Finset.univ) => htail xw)
    have hc := fr.costAcc N hN hon'
    have hs := hsel N hN₀
    have hab := habs N hN₀
    rw [hq] at hc hs hab
    -- the calls' part: `(2 + q^d + Kd)·Kf·X·b ≤ Kf(3+Kd)(q+1)^{d+m-1}·b ≤ q^{callDeg}·b`
    have hqd : q ^ d ≤ (q + 1) ^ d := Nat.pow_le_pow_left (Nat.le_succ q) d
    have hqd1 : 1 ≤ (q + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos q)
    have hcalls : Kf * (q + 1) ^ (callDegMargin - 1) * (B.callBudget q + c1.budgetAt B q) +
        (2 + (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q)) ≤
          2 + q ^ E.callDeg * B.callBudget q := by
      have e1 : Kf * (q + 1) ^ (callDegMargin - 1) * (B.callBudget q + c1.budgetAt B q) ≤
          2 * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by
        have := Nat.mul_le_mul_left (Kf * (q + 1) ^ (callDegMargin - 1)) (Nat.add_le_add_left hs (B.callBudget q))
        calc _ ≤ Kf * (q + 1) ^ (callDegMargin - 1) * (B.callBudget q + B.callBudget q) := this
          _ = 2 * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by ring
      have e2 : (2 + (q ^ d + Kd)) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) ≤
          (Kf * (3 + Kd) * (q + 1) ^ (d + (callDegMargin - 1))) * B.callBudget q := by
        rw [pow_add]
        have : 2 + (q ^ d + Kd) ≤ (3 + Kd) * (q + 1) ^ d := by nlinarith
        calc (2 + (q ^ d + Kd)) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q)
            ≤ ((3 + Kd) * (q + 1) ^ d) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) :=
              Nat.mul_le_mul_right _ this
          _ = Kf * (3 + Kd) * ((q + 1) ^ d * (q + 1) ^ (callDegMargin - 1)) * B.callBudget q := by ring
      have e3 := Nat.mul_le_mul_right (B.callBudget q) hab
      have e4 : (2 + (q ^ d + Kd)) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) =
          2 * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) +
            (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by ring
      omega
    unfold workerFuel
    rw [hq]
    omega

end Assembly

/-! ### Layer B at the gate -/

section LeafB
variable (l : Literals)

/-- The worker from its stages at one coefficient, source work, primitive and language. -/
noncomputable def workerOf (F : GateFree l) (coef A : ℕ) (P : FusedPrimitive (IU l F coef A)) (L : Language)
    (hL : InNTIME (fun n => n ^ (kU l + 2)) L) {d₁ : ℕ} (c1 : C1At d₁) (Af Kf N₀ Kd : ℕ)
    (fr : FrontAt P (SU l F coef A L hL) c1 Af Kf N₀) (dc : DecideAt P Kd)
    (hA : Af + 2 * Kd + 8 ≤ A)
    (hcount : ∀ N, N₀ ≤ N → ∀ (z : BitInput N) (g : UnionGuess (SU l F coef A L hL) z),
      g.oracle.size ≤ oracleSizeBound (SU l F coef A L hL).G ((SU l F coef A L hL).pcp.nativeWidth N) →
        ∀ tr : List ℕ, (g.checkData tr).schedule.length ≤
          ((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N ^ unionCallDeg l)
    (habs : ∀ N, N₀ ≤ N → Kf * (3 + Kd) * (((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N + 1) ^
      (unionCallDeg l + (callDegMargin - 1)) ≤ ((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N ^ F.E.callDeg)
    (hsel : ∀ N, N₀ ≤ N → c1.budgetAt ((gate0 l F).budget (kU l) coef A (aU l) (haU l))
      (((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N) ≤
        ((gate0 l F).budget (kU l) coef A (aU l) (haU l)).callBudget
          (((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N)) :
    WorkerAt (SU l F coef A L hL) P where
  t := NW P fr.tf
  s := _
  p := workerMachine fr dc
  ht := two_le_NW P fr.tf
  result := lp P fr.tf (cellSlot P)
  fuel := workerFuel fr dc
  onset := fr.onset
  callOk := fr.callOk
  run := worker_run fr dc
  hok := fr.hok
  time := worker_time fr dc dc.hcost (unionCallDeg l) hA hcount habs hsel

/-- The ledger's width grows (`TimeBudget.growth`). -/
theorem tendsto_q {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : Tendsto B.q atTop atTop :=
  tendsto_atTop_atTop.2 fun m => B.growth m

theorem eventual_time (F : GateFree l) (hF : GateFreeOK l F) (coef A : ℕ) (hc : 1 ≤ coef) (L : Language)
    (hL : InNTIME (fun n => n ^ (kU l + 2)) L) {d₁ : ℕ} (c1 : C1At d₁) (Kf Kd : ℕ) (count : CallCountF l) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (∀ (z : BitInput N) (g : UnionGuess (SU l F coef A L hL) z),
        g.oracle.size ≤ oracleSizeBound (SU l F coef A L hL).G ((SU l F coef A L hL).pcp.nativeWidth N) →
          ∀ tr : List ℕ, (g.checkData tr).schedule.length ≤
            ((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N ^ unionCallDeg l) ∧
      Kf * (3 + Kd) * (((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N + 1) ^
        (unionCallDeg l + (callDegMargin - 1)) ≤ ((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N ^ F.E.callDeg ∧
      c1.budgetAt ((gate0 l F).budget (kU l) coef A (aU l) (haU l))
        (((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N) ≤
          ((gate0 l F).budget (kU l) coef A (aU l) (haU l)).callBudget
            (((gate0 l F).budget (kU l) coef A (aU l) (haU l)).q N) := by
  have hq := tendsto_q ((gate0 l F).budget (kU l) coef A (aU l) (haU l))
  have e1 := count (kU l) coef A (aU l) (haU l) F L hL
  have e2 := hq.eventually (calls_absorb l F hF (Kf * (3 + Kd)))
  have e3 := hq.eventually (Free.selection_le_callBudget l F (kU l) coef A (aU l) (haU l) hc c1.E₁ c1.c₁)
  exact eventually_atTop.1 (e1.and (e2.and e3))

noncomputable def workers_of_stages (c1 : C1Impl) (dec : DecideF)
    (fronts : ∀ F : GateFree l, GateFreeOK l F → FrontsF l F) (count : CallCountF l) :
    ∀ F : GateFree l, GateFreeOK l F → WorkersF l F := fun F hF =>
  ⟨(fronts F hF).1 + 2 * dec.1 + 8, by omega, fun coef hc P L hL =>
    let fd := (fronts F hF).2 coef hc _ P L hL
    let c1d := c1 fd.1
    let fk := fd.2 c1d
    let N₀ := Classical.choose (eventual_time l F hF coef _ hc L hL c1d fk.1 dec.1 count)
    have hN₀ := Classical.choose_spec (eventual_time l F hF coef _ hc L hL c1d fk.1 dec.1 count)
    workerOf l F coef _ P L hL c1d (fronts F hF).1 fk.1 N₀ dec.1 (fk.2 N₀) (dec.2 P) le_rfl
      (fun N hN => (hN₀ N hN).1) (fun N hN => (hN₀ N hN).2.1) (fun N hN => (hN₀ N hN).2.2)⟩

noncomputable def unionLeafF_plan (c1 : C1Impl) (dec : DecideF)
    (fronts : ∀ F : GateFree l, GateFreeOK l F → FrontsF l F) (count : CallCountF l) (acc : AcceptsCallF l)
    (facts : SetupFactsF l) : UnionLeafF l :=
  unionLeafF_of_workers l facts acc (workers_of_stages l c1 dec fronts count)

end LeafB

noncomputable def union_plan (c1 : C1Impl) (dec : DecideF)
    (fronts : ∀ (l : Literals) (F : GateFree l), GateFreeOK l F → FrontsF l F) (count : ∀ l : Literals, CallCountF l)
    (acc : ∀ l : Literals, AcceptsCallF l) (facts : ∀ l : Literals, SetupFactsF l) : ∀ l : Literals, UnionLeafF l :=
  fun l => unionLeafF_plan l c1 dec (fronts l) (count l) (acc l) (facts l)

end NearCubicWires.WireExponent3_5.UnionMachine.Plan
