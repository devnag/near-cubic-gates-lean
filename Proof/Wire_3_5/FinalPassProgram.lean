import Proof.MachineModel.Runs
import Proof.MachineModel.OrdinaryStreamController
import Proof.MachineModel.OrdinaryControlPrefix

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution

variable {t : ℕ}

/-- A bank: the head positions and the contents of the `t` tapes. -/
structure Bank (t : ℕ) where
  H : Fin t → ℕ
  A : Fin t → List Bool

/-- The scanned bit of tape `i`. -/
def Bank.bit (b : Bank t) (i : Fin t) : Bool := readTapeBit (b.A i) (b.H i)

/-- One local action on a bank. -/
def Bank.act (b : Bank t) (w : Fin t → Option Bool) (m : Fin t → HeadMove) : Bank t :=
  ⟨fun i => (m i).apply (b.H i), fun i => match w i with
    | none => b.A i
    | some v => writeTapeBit (b.A i) (b.H i) v⟩

/-- Structured programs on `t` tapes. -/
inductive Prog (t : ℕ) where
  | skip : Prog t
  | act (w : Fin t → Option Bool) (m : Fin t → HeadMove) : Prog t
  | seq (P Q : Prog t) : Prog t
  | ite (i : Fin t) (P Q : Prog t) : Prog t
  | loop (i : Fin t) (P : Prog t) : Prog t

/-! ## The machines -/

/-- The empty program: its start state is halted. -/
def skipMachine : Machine t 1 := ⟨0, 0, fun _ => true, fun _ _ => none⟩

/-- One action, then halt. -/
def actMachine (w : Fin t → Option Bool) (m : Fin t → HeadMove) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, w, m⟩ else none

/-- A state of the left branch inside the branch machine. -/
def iteL {a : ℕ} (b : ℕ) (x : Fin a) : Fin (a + b + 1) := (x.castAdd b).castSucc

/-- A state of the right branch inside the branch machine. -/
def iteR (a : ℕ) {b : ℕ} (x : Fin b) : Fin (a + b + 1) := (x.natAdd a).castSucc

def liftAction {a u : ℕ} (f : Fin a → Fin u) (x : Action t a) : Action t u := ⟨f x.nextControl, x.write, x.move⟩

/-- The branch: a test state reads tape `i` and enters the left or the right program, which then run as themselves. -/
def iteMachine (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) : Machine t (a + b + 1) where
  descriptionBits := 0
  start := Fin.last (a + b)
  halted := Fin.lastCases (motive := fun _ => Bool) false
    (Fin.addCases (motive := fun _ => Bool) p.halted q.halted)
  rule := Fin.lastCases (motive := fun _ => (Fin t → Bool) → Option (Action t (a + b + 1)))
    (fun sc => some ⟨if sc i then iteL b p.start else iteR a q.start, fun _ => none, fun _ => .stay⟩)
    (Fin.addCases (motive := fun _ => (Fin t → Bool) → Option (Action t (a + b + 1)))
      (fun x sc => (p.rule x sc).map (liftAction (iteL b)))
      (fun x sc => (q.rule x sc).map (liftAction (iteR a))))

/-- The number of control states. -/
def Prog.size : Prog t → ℕ
  | .skip => 1
  | .act _ _ => 2
  | .seq P Q => P.size + Q.size
  | .ite _ P Q => P.size + Q.size + 1
  | .loop _ P => P.size + 2

/-- **One machine per program.** -/
def Prog.compile : (P : Prog t) → Machine t P.size
  | .skip => skipMachine
  | .act w m => actMachine w m
  | .seq P Q => Composition.machine P.compile Q.compile
  | .ite i P Q => iteMachine i P.compile Q.compile
  | .loop i P => StreamController.machine P.compile i

/-! ## Big-step execution -/

/-- `Exec P b c n`: the program runs from bank `b` to bank `c` within `n` steps of its machine. -/
inductive Exec : Prog t → Bank t → Bank t → ℕ → Prop where
  | skip (b : Bank t) : Exec .skip b b 0
  | act (b : Bank t) (w : Fin t → Option Bool) (m : Fin t → HeadMove) : Exec (.act w m) b (b.act w m) 1
  | seq {P Q : Prog t} {b c d : Bank t} {n k : ℕ} : Exec P b c n → Exec Q c d k → Exec (.seq P Q) b d (n + 1 + k)
  | iteT {i : Fin t} {P Q : Prog t} {b c : Bank t} {n : ℕ} : b.bit i = true → Exec P b c n → Exec (.ite i P Q) b c (n + 1)
  | iteF {i : Fin t} {P Q : Prog t} {b c : Bank t} {n : ℕ} : b.bit i = false → Exec Q b c n →
      Exec (.ite i P Q) b c (n + 1)
  | loopF {i : Fin t} {P : Prog t} {b : Bank t} : b.bit i = false → Exec (.loop i P) b b 1
  | loopT {i : Fin t} {P : Prog t} {b c d : Bank t} {n k : ℕ} : b.bit i = true → Exec P b c n →
      Exec (.loop i P) c d k → Exec (.loop i P) b d (n + 2 + k)
  | mono {P : Prog t} {b c : Bank t} {n m : ℕ} : Exec P b c n → n ≤ m → Exec P b c m

/-! ## Soundness -/

theorem skip_step (b : Bank t) : Step (Prog.skip : Prog t).compile 0 b.H b.A b.H b.A :=
  ⟨_, runFrom_zero_of_halted _ ⟨(Prog.skip : Prog t).compile.start, b.H, b.A⟩ rfl, rfl, rfl, le_refl _⟩

theorem act_step (b : Bank t) (w : Fin t → Option Bool) (m : Fin t → HeadMove) :
    Step (Prog.act w m).compile 1 b.H b.A (b.act w m).H (b.act w m).A := by
  have hs : step (actMachine w m) ⟨0, b.H, b.A⟩ = some ⟨1, (b.act w m).H, (b.act w m).A⟩ := by
    simp only [step, actMachine]
    rfl
  have hr := runFrom_step (fuel := 0) (actMachine w m) ⟨0, b.H, b.A⟩ ⟨1, (b.act w m).H, (b.act w m).A⟩ _ rfl hs
    (runFrom_zero_of_halted _ _ rfl)
  exact ⟨_, hr, rfl, rfl, by simp⟩

theorem ite_halted_L (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (x : Fin a) :
    (iteMachine i p q).halted (iteL b x) = p.halted x := by
  simp only [iteMachine, iteL]
  rw [Fin.lastCases_castSucc, Fin.addCases_left]

theorem ite_halted_R (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (x : Fin b) :
    (iteMachine i p q).halted (iteR a x) = q.halted x := by
  simp only [iteMachine, iteR]
  rw [Fin.lastCases_castSucc, Fin.addCases_right]

theorem ite_rule_L (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (x : Fin a) (sc : Fin t → Bool) :
    (iteMachine i p q).rule (iteL b x) sc = (p.rule x sc).map (liftAction (iteL b)) := by
  simp only [iteMachine, iteL]
  rw [Fin.lastCases_castSucc, Fin.addCases_left]

theorem ite_rule_R (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (x : Fin b) (sc : Fin t → Bool) :
    (iteMachine i p q).rule (iteR a x) sc = (q.rule x sc).map (liftAction (iteR a)) := by
  simp only [iteMachine, iteR]
  rw [Fin.lastCases_castSucc, Fin.addCases_right]

theorem lift_apply {a u : ℕ} (f : Fin a → Fin u) (c : Configuration t a) (x : Action t a) :
    applyAction (controlConfig f c) (liftAction f x) = controlConfig f (applyAction c x) := rfl

theorem ite_step_L (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (c d : Configuration t a)
    (hs : step p c = some d) : step (iteMachine i p q) (controlConfig (iteL b) c) = some (controlConfig (iteL b) d) := by
  have hsc : (controlConfig (iteL b) c).scanned = c.scanned := rfl
  unfold step at hs ⊢
  rw [hsc]
  show ((iteMachine i p q).rule (iteL b c.control) c.scanned).map (applyAction (controlConfig (iteL b) c)) = _
  rw [ite_rule_L]
  cases h : p.rule c.control c.scanned with
  | none => rw [h] at hs; simp at hs
  | some x =>
    rw [h] at hs
    simp only [Option.map_some, Option.some.injEq] at hs ⊢
    rw [lift_apply, hs]

theorem ite_step_R (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (c d : Configuration t b)
    (hs : step q c = some d) : step (iteMachine i p q) (controlConfig (iteR a) c) = some (controlConfig (iteR a) d) := by
  have hsc : (controlConfig (iteR a) c).scanned = c.scanned := rfl
  unfold step at hs ⊢
  rw [hsc]
  show ((iteMachine i p q).rule (iteR a c.control) c.scanned).map (applyAction (controlConfig (iteR a) c)) = _
  rw [ite_rule_R]
  cases h : q.rule c.control c.scanned with
  | none => rw [h] at hs; simp at hs
  | some x =>
    rw [h] at hs
    simp only [Option.map_some, Option.some.injEq] at hs ⊢
    rw [lift_apply, hs]

theorem ite_test (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (bk : Bank t) :
    step (iteMachine i p q) ⟨Fin.last (a + b), bk.H, bk.A⟩ =
      some ⟨if bk.bit i then iteL b p.start else iteR a q.start, bk.H, bk.A⟩ := by
  simp only [step, iteMachine, Fin.lastCases_last, Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext j; rfl
  · funext j; rfl

/-- The taken branch of a branch machine: one test step, then the branch's own run. -/
theorem ite_branch_step {a b u : ℕ} (i : Fin t) (p : Machine t a) (q : Machine t b) (bk c : Bank t) (n : ℕ)
    (f : Fin u → Fin (a + b + 1)) (r : Machine t u) (hstart : f r.start = if bk.bit i then iteL b p.start else iteR a q.start)
    (hn : ∀ x, (iteMachine i p q).halted (f x) = r.halted x)
    (hstep : ∀ c d : Configuration t u, step r c = some d →
      step (iteMachine i p q) (controlConfig f c) = some (controlConfig f d))
    (hr : Step r n bk.H bk.A c.H c.A) :
    Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A := by
  obtain ⟨rr, hrr, hh, ht, hsteps⟩ := hr
  obtain ⟨hp, hhalt⟩ := prefix_of_run r n _ rr hrr
  have hmap := hp.mapControl f (fun c hc => by rw [hn]; exact hc) (fun c d _ hs => hstep c d hs)
  have htest := ite_test i p q bk
  have e0 : (⟨if bk.bit i then iteL b p.start else iteR a q.start, bk.H, bk.A⟩ : Configuration t (a + b + 1)) =
      controlConfig f ⟨r.start, bk.H, bk.A⟩ := by
    simp only [controlConfig, hstart]
  rw [e0] at htest
  have t1 := Timed.single (p := iteMachine i p q) (by simp [iteMachine]) htest
  have t2 : Timed (iteMachine i p q) rr.steps (controlConfig f ⟨r.start, bk.H, bk.A⟩) (controlConfig f rr.final) :=
    ⟨_, hmap⟩
  obtain ⟨res, hres, hfin, hst⟩ := (t1.trans t2).run (by rw [controlConfig, hn]; exact hhalt)
  have more := runFrom_moreFuel _ (1 + rr.steps) (n - rr.steps) _ res hres
  rw [show 1 + rr.steps + (n - rr.steps) = n + 1 by omega] at more
  refine ⟨res, more, ?_, ?_, by omega⟩
  · rw [hfin]; exact hh
  · rw [hfin]; exact ht

/-- **Soundness**: every derivation is a `Step` of the compiled machine. -/
theorem Exec.step {P : Prog t} {b c : Bank t} {n : ℕ} (h : Exec P b c n) : Step P.compile n b.H b.A c.H c.A := by
  induction h with
  | skip b => exact skip_step b
  | act b w m => exact act_step b w m
  | seq _ _ ih1 ih2 => exact Step.seq ih1 ih2
  | @iteT i P Q b c n hb _ ih =>
    exact ite_branch_step i P.compile Q.compile b c n (iteL Q.size) P.compile (by simp [hb])
      (ite_halted_L i _ _) (ite_step_L i _ _) ih
  | @iteF i P Q b c n hb _ ih =>
    exact ite_branch_step i P.compile Q.compile b c n (iteR P.size) Q.compile (by simp [hb])
      (ite_halted_R i _ _) (ite_step_R i _ _) ih
  | @loopF i P b hb =>
    have hs := StreamController.stop_step P.compile i ⟨P.compile.start, b.H, b.A⟩ hb
    have hr := runFrom_step (fuel := 0) (StreamController.machine P.compile i) _ _ _
      (StreamController.test_halted P.compile i) hs (runFrom_zero_of_halted _ _ (StreamController.stop_halted _ _))
    exact ⟨_, hr, rfl, rfl, by simp⟩
  | @loopT i P b c d n k hb _ _ ih1 ih2 =>
    obtain ⟨r1, hr1, hh1, ht1, hs1⟩ := ih1
    obtain ⟨r2, hr2, hh2, ht2, hs2⟩ := ih2
    have henter := StreamController.enter_step P.compile i ⟨P.compile.start, b.H, b.A⟩ hb
    obtain ⟨hbody, hhalt⟩ := StreamController.body_prefix P.compile i n _ r1 hr1
    have hret := StreamController.return_step P.compile i r1.final hhalt
    have t1 := Timed.single (StreamController.test_halted P.compile i) henter
    have t2 : Timed (StreamController.machine P.compile i) r1.steps
        (controlConfig RecordController.code (Composition.restart ⟨P.compile.start, b.H, b.A⟩ P.compile.start))
        (controlConfig RecordController.code r1.final) := ⟨_, hbody⟩
    have t3 := Timed.single (StreamController.body_halted P.compile i r1.final.control) hret
    have e3 : controlConfig (fun _ => RecordController.test P.size) r1.final =
        (⟨(StreamController.machine P.compile i).start, c.H, c.A⟩ : Configuration t (P.size + 2)) := by
      apply configuration_ext
      · rfl
      · exact hh1
      · exact ht1
    rw [e3] at t3
    obtain ⟨sp, hpre⟩ := (t1.trans t2).trans t3
    obtain ⟨joined, hj, hjf, hjs, _⟩ := hpre.followedBy r2 hr2
    have e1 : controlConfig (fun _ => RecordController.test P.size) (⟨P.compile.start, b.H, b.A⟩ :
        Configuration t P.size) = ⟨(StreamController.machine P.compile i).start, b.H, b.A⟩ := rfl
    rw [e1] at hj
    have more := runFrom_moreFuel _ (1 + r1.steps + 1 + k) (n + 2 + k - (1 + r1.steps + 1 + k)) _ joined hj
    rw [show 1 + r1.steps + 1 + k + (n + 2 + k - (1 + r1.steps + 1 + k)) = n + 2 + k by omega] at more
    refine ⟨joined, more, ?_, ?_, by omega⟩
    · rw [hjf]; exact hh2
    · rw [hjf]; exact ht2
  | mono _ hnm ih => exact ih.enlarge hnm

end NearCubicWires.WireExponent3_5.FinalPass.Tm
