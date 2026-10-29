import SourceAdapters.Compile.OraclePrintAddress
import SourceAdapters.Compile.OraclePrintVector
import SourceAdapters.Compile.OracleStreamBounds

/-!
# The printer's plan on the token machine

 (`thm:short-pcp-ours`, Step 4): "Convert this computation into a circuit in the standard way […] The
algorithm \(A\) computes […] \(C^O_x\) in \(\poly(n,\log T)\) time"; (`cor:short-pcp-clock`): the
clock is input data. The circuit `OracleExpressions.requestCircuit p r` is the input gates, the initial formulas,
`fuel` rounds (the query address bits, one oracle gate, the transition formulas) and the verdict, compiled on shared
wires; `requestStream` lists its nodes (`requestCircuit_stream`).

This module states the printer's plan on the token machine `PS` of `OraclePrintTemplate`:
* `Templates p`: the two expression families supplied as templates (initial formulas, transition
  formulas), as data with their exact token equalities and static size side conditions (the A1/A3 equalities);
* `planPS`: the input gates, the vectors run member by member (`PS.vec`), the oracle gate whose index is written to
  wire-map entry `clockBits` (the answer wire), and the verdict;
* **`plan_eq`**: the plan emits exactly `(requestStream p r).1` and leaves exactly its output on the stack.

-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
open NearCubicGates.Adapters.Compile (OracleCompilationRequest)
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicGates.Adapters.Compile.OracleExpressions (wireStream vectorStream inputsStream queryStream roundStream
  roundsStream requestStream)
open NearCubicGates.Close.Cells (putAt getD_putAt_self getD_putAt_ne)

set_option autoImplicit false

/-! ## The request's numbers -/

/-- The data bits the templates read: the framed data word (proof of `thm:short-pcp-ours`). -/
def reqD (r : OracleCompilationRequest) : List Bool := RepairOrdinary.frame r.data

/-- The bound numbers of every template: width, clock, seed length, data frame length. -/
def reqEnv (r : OracleCompilationRequest) : List ℕ :=
  [requestWidth r, r.fuel, r.ell, (RepairOrdinary.frame r.data).length]

theorem requestWidth_three (r : OracleCompilationRequest) : 3 ≤ requestWidth r := by
  unfold requestWidth; omega

@[simp] theorem reqEnv_length (r : OracleCompilationRequest) : (reqEnv r).length = 4 := rfl

/-- **The two template families still to be supplied** (initial formulas, proof of `thm:short-pcp-ours`; transition formulas,
): templates whose tokens are exactly the postfix tokens of every member, for every request, with the
static side conditions of the vector loop. -/
structure Templates (p : OrdinaryOracleProgram) where
  init : U
  trans : U
  init_eq : ∀ (r : OracleCompilationRequest) (j : Fin (clockBits p (requestWidth r) r.fuel)),
    postR (fun i => i.val) (initialExpression p r j) = init.toks (reqD r) (reqEnv r ++ [j.val])
  trans_eq : ∀ (r : OracleCompilationRequest) (j : Fin (clockBits p (requestWidth r) r.fuel)),
    postR (fun i => i.val) (clockTransitionExpression p (requestWidth r) r.fuel j) =
      trans.toks (reqD r) (reqEnv r ++ [j.val])
  init_depth : init.depth ≤ 11
  init_tneed : init.tneed ≤ 16
  trans_depth : trans.depth ≤ 11
  trans_tneed : trans.tneed ≤ 16

/-- The query address template of a program. -/
def addrT (p : OrdinaryOracleProgram) : U := addrU p.base.tapeCount p.base.stateCount p.queryTape.val

/-! ## The plan -/

/-- Member tokens of a vector template. -/
def tokF (T : U) (D : List Bool) (env : List ℕ) : ℕ → List Tok := fun j => T.toks D (env ++ [j])

variable {k : ℕ}

/-- The oracle gate on arguments `A`. -/
def PS.oracle (S : PS k k) (A : List ℕ) : PS k k :=
  ⟨S.cnt + 1, S.stk, S.nodes ++ [.oracle (fun i => A.getD i.val 0)]⟩

/-- The input gates and their wire map. -/
def initPS (k : ℕ) : PS k k := ⟨k, [], List.ofFn (fun i : Fin k => .input i)⟩

/-- One clock round on the token machine with wire map `w`: the address vector, the oracle gate (its index is the
answer wire, written at entry `cb`), the transition vector on the extended wire map. -/
def roundPS (p : OrdinaryOracleProgram) (Tt : U) (D : List Bool) (env : List ℕ) (cb : ℕ) (S : PS k k)
    (w : List ℕ) : PS k k × List ℕ :=
  let q := PS.vec w (tokF (addrT p) D env) k S
  let w1 := putAt w cb q.1.cnt
  let t := PS.vec w1 (tokF Tt D env) cb (q.1.oracle q.2)
  (t.1, overwrite w1 t.2)

/-- `m` clock rounds. -/
def roundsPS (p : OrdinaryOracleProgram) (Tt : U) (D : List Bool) (env : List ℕ) (cb : ℕ) :
    ℕ → PS k k × List ℕ → PS k k × List ℕ
  | 0, x => x
  | m + 1, x => roundsPS p Tt D env cb m (roundPS p Tt D env cb x.1 x.2)

theorem roundsPS_succ (p : OrdinaryOracleProgram) (Tt : U) (D : List Bool) (env : List ℕ) (cb : ℕ) (m : ℕ) :
    ∀ x : PS k k × List ℕ, roundsPS p Tt D env cb (m + 1) x =
      roundPS p Tt D env cb (roundsPS p Tt D env cb m x).1 (roundsPS p Tt D env cb m x).2 := by
  induction m with
  | zero => intro x; rfl
  | succ m ih => intro x; exact ih _

/-- The state after the input gates and the initial vector. -/
def startPS (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) :
    PS r.ell r.ell × List ℕ :=
  let I := PS.vec (List.range r.ell) (tokF T.init (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel) (initPS r.ell)
  (I.1, overwrite (List.range r.ell) I.2)

/-- The state after the rounds. -/
def roundsEnd (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) :
    PS r.ell r.ell × List ℕ :=
  roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) r.fuel (startPS p T r)

/-- **The printer's plan**: the final token machine state. -/
def planPS (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) : PS r.ell r.ell :=
  (roundsEnd p T r).1.run (roundsEnd p T r).2 ((verdU p).toks (reqD r) (reqEnv r))

/-! ## Wire maps -/

/-- The first `cb` wire-map entries are the wires `wire`. -/
def WireOK (cb : ℕ) (w : List ℕ) (wire : Fin cb → ℕ) : Prop := cb ≤ w.length ∧ ∀ i : Fin cb, w.getD i.val 0 = wire i

theorem getD_overwrite (old new : List ℕ) (i : ℕ) (hi : i < new.length) :
    (overwrite old new).getD i 0 = new.getD i 0 := by
  unfold overwrite
  rw [List.getD_append _ _ _ _ hi]

theorem getD_ofFn' {m : ℕ} (f : Fin m → ℕ) (i : Fin m) : (List.ofFn f).getD i.val 0 = f i := by
  simp

theorem wireOK_overwrite {cb : ℕ} (old : List ℕ) (f : Fin cb → ℕ) : WireOK cb (overwrite old (List.ofFn f)) f := by
  refine ⟨?_, fun i => ?_⟩
  · have := overwrite_length_ge old (List.ofFn f); simpa using this
  · rw [getD_overwrite _ _ _ (by simp), getD_ofFn']

theorem oracle_args (f : Fin k → ℕ) : (fun i : Fin k => (List.ofFn f).getD i.val 0) = f := by
  funext i; exact getD_ofFn' f i

/-! ## One round -/

section Round

variable (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest)

theorem roundPS_eq (S : PS r.ell r.ell) (w : List ℕ) (wire : Fin (clockBits p (requestWidth r) r.fuel) → ℕ)
    (hS : S.stk = []) (hw : WireOK (clockBits p (requestWidth r) r.fuel) w wire) :
    (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).1 =
        ⟨S.cnt + (roundStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire).1.length, [],
          S.nodes ++ (roundStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire).1⟩ ∧
      WireOK (clockBits p (requestWidth r) r.fuel)
        (roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w).2
        (roundStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire).2 := by
  have hq : ∀ j : Fin r.ell, tokF (addrT p) (reqD r) (reqEnv r) j.val =
      postR (qρ p (requestWidth r) r.fuel) (queryAddressExpression (requestWidth r) j.val) :=
    fun j => (addr_eq p (requestWidth r) r.fuel (reqD r) (reqEnv r ++ [j.val]) (by simp) (by simp [reqEnv]) j.val
      (by simp [reqEnv])).symm
  obtain ⟨q1, q2⟩ := vec_stream (n := r.ell) (arity := r.ell) w (qρ p (requestWidth r) r.fuel) r.ell
    (fun bit : Fin r.ell => queryAddressExpression (requestWidth r) bit.val) (tokF (addrT p) (reqD r) (reqEnv r)) S hq
  have hwq : (fun i => w.getD (qρ p (requestWidth r) r.fuel i) 0) =
      fun i => wire (queryInputIndex p (requestWidth r) r.fuel i) := by
    funext i; exact hw.2 (queryInputIndex p (requestWidth r) r.fuel i)
  rw [hwq] at q1 q2
  set A := vectorStream (n := r.ell) (arity := r.ell) S.cnt
    (fun i => wire (queryInputIndex p (requestWidth r) r.fuel i)) r.ell
    (fun bit : Fin r.ell => queryAddressExpression (requestWidth r) bit.val) with hA
  set q := PS.vec w (tokF (addrT p) (reqD r) (reqEnv r)) r.ell S with hqdef
  have hlen : clockBits p (requestWidth r) r.fuel ≤ w.length := hw.1
  set w1 := putAt w (clockBits p (requestWidth r) r.fuel) q.1.cnt with hw1
  have ht : ∀ j : Fin (clockBits p (requestWidth r) r.fuel), tokF T.trans (reqD r) (reqEnv r) j.val =
      postR (fun i => i.val) (clockTransitionExpression p (requestWidth r) r.fuel j) := fun j => (T.trans_eq r j).symm
  obtain ⟨t1, t2⟩ := vec_stream (n := r.ell) (arity := r.ell) w1
    (fun i : Fin (clockBits p (requestWidth r) r.fuel + 1) => i.val) (clockBits p (requestWidth r) r.fuel)
    (clockTransitionExpression p (requestWidth r) r.fuel) (tokF T.trans (reqD r) (reqEnv r)) (q.1.oracle q.2) ht
  have hcnt : q.1.cnt = S.cnt + A.1.length := by rw [q1]
  have hw1f : (fun i : Fin (clockBits p (requestWidth r) r.fuel + 1) => w1.getD i.val 0) =
      Fin.addCases wire (fun _ : Fin 1 => S.cnt + A.1.length) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left, Fin.val_castAdd, hw1, getD_putAt_ne _ _ _ _ hlen (by omega), hw.2 j]
    · rw [Fin.addCases_right, Fin.val_natAdd, Fin.val_eq_zero j, Nat.add_zero, hw1,
        getD_putAt_self _ _ _ hlen, hcnt]
  rw [hw1f] at t1 t2
  have horc : (q.1.oracle q.2) =
      ⟨S.cnt + (A.1 ++ [OracleNode.oracle A.2]).length, [], S.nodes ++ (A.1 ++ [OracleNode.oracle A.2])⟩ := by
    simp only [PS.oracle, q1, q2, hS, oracle_args, List.append_assoc, List.length_append,
      List.length_singleton, Nat.add_assoc]
  rw [horc] at t1 t2
  set vs := vectorStream (n := r.ell) (arity := r.ell) (S.cnt + (A.1 ++ [OracleNode.oracle A.2]).length)
    (Fin.addCases wire (fun _ : Fin 1 => S.cnt + A.1.length)) (clockBits p (requestWidth r) r.fuel)
    (clockTransitionExpression p (requestWidth r) r.fuel) with hvs
  have hR : roundStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire =
      (A.1 ++ [OracleNode.oracle A.2] ++ vs.1, vs.2) := rfl
  rw [hR]
  refine ⟨?_, ?_⟩
  · show (PS.vec w1 (tokF T.trans (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel) (q.1.oracle q.2)).1 = _
    rw [horc, t1]
    simp only [List.length_append, List.append_assoc]
    congr 1
    omega
  · show WireOK _ (overwrite w1
      (PS.vec w1 (tokF T.trans (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel) (q.1.oracle q.2)).2) _
    rw [horc, t2]
    exact wireOK_overwrite _ _

theorem roundsPS_eq (m : ℕ) : ∀ (S : PS r.ell r.ell) (w : List ℕ)
    (wire : Fin (clockBits p (requestWidth r) r.fuel) → ℕ), S.stk = [] →
    WireOK (clockBits p (requestWidth r) r.fuel) w wire →
    (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) m (S, w)).1 =
        ⟨S.cnt + (roundsStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire m).1.length, [],
          S.nodes ++ (roundsStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire m).1⟩ ∧
      WireOK (clockBits p (requestWidth r) r.fuel)
        (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) m (S, w)).2
        (roundsStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel S.cnt wire m).2 := by
  induction m with
  | zero =>
      intro S w wire hS hw
      refine ⟨?_, hw⟩
      cases S; simp only at hS; subst hS; simp [roundsPS, roundsStream]
  | succ m ih =>
      intro S w wire hS hw
      obtain ⟨e1, e2⟩ := roundPS_eq p T r S w wire hS hw
      set x := roundPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) S w with hxdef
      obtain ⟨f1, f2⟩ := ih x.1 x.2 _ (by rw [e1]) e2
      have hx : x = (x.1, x.2) := rfl
      show (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) m x).1 = _ ∧
        WireOK _ (roundsPS p T.trans (reqD r) (reqEnv r) (clockBits p (requestWidth r) r.fuel) m x).2 _
      rw [hx, f1, e1]
      refine ⟨?_, ?_⟩
      · simp only [roundsStream, List.length_append, List.append_assoc]
        congr 1
        omega
      · rw [e1] at f2
        exact f2

end Round

/-! ## The whole plan -/

theorem startPS_eq (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) :
    (startPS p T r).1 = ⟨(inputsStream (arity := r.ell) 0 r.ell id).1.length +
        (vectorStream (n := r.ell) (arity := r.ell) (inputsStream (arity := r.ell) 0 r.ell id).1.length
          (inputsStream (arity := r.ell) 0 r.ell id).2 (clockBits p (requestWidth r) r.fuel)
          (initialExpression p r)).1.length, [],
        (inputsStream (arity := r.ell) 0 r.ell id).1 ++
          (vectorStream (n := r.ell) (arity := r.ell) (inputsStream (arity := r.ell) 0 r.ell id).1.length
            (inputsStream (arity := r.ell) 0 r.ell id).2 (clockBits p (requestWidth r) r.fuel)
            (initialExpression p r)).1⟩ ∧
      WireOK (clockBits p (requestWidth r) r.fuel) (startPS p T r).2
        (vectorStream (n := r.ell) (arity := r.ell) (inputsStream (arity := r.ell) 0 r.ell id).1.length
          (inputsStream (arity := r.ell) 0 r.ell id).2 (clockBits p (requestWidth r) r.fuel)
          (initialExpression p r)).2 := by
  obtain ⟨i1, i2⟩ := inputsStream_eq (n := r.ell) (arity := r.ell) r.ell 0 id
  have hl : (inputsStream (arity := r.ell) 0 r.ell id).1.length = r.ell := by rw [i1, List.length_ofFn]
  have hwire : (inputsStream (arity := r.ell) 0 r.ell id).2 = fun i => (List.range r.ell).getD i.val 0 := by
    funext i; rw [i2 i]; simp
  have ht : ∀ j : Fin (clockBits p (requestWidth r) r.fuel), tokF T.init (reqD r) (reqEnv r) j.val =
      postR (fun i => i.val) (initialExpression p r j) := fun j => (T.init_eq r j).symm
  obtain ⟨v1, v2⟩ := vec_stream (n := r.ell) (arity := r.ell) (List.range r.ell) (fun i : Fin r.ell => i.val)
    (clockBits p (requestWidth r) r.fuel) (initialExpression p r) (tokF T.init (reqD r) (reqEnv r)) (initPS r.ell) ht
  rw [hl, hwire]
  refine ⟨?_, ?_⟩
  · show (PS.vec (List.range r.ell) (tokF T.init (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel)
      (initPS r.ell)).1 = _
    rw [v1, i1]
    rfl
  · show WireOK _ (overwrite (List.range r.ell) (PS.vec (List.range r.ell) (tokF T.init (reqD r) (reqEnv r))
      (clockBits p (requestWidth r) r.fuel) (initPS r.ell)).2) _
    rw [v2]
    exact wireOK_overwrite _ _

/-- **The plan emits exactly node stream of `requestCircuit p r`** (proof of `thm:short-pcp-ours`) and leaves its output
wire alone on the stack. -/
theorem plan_eq (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) :
    (planPS p T r).nodes = (requestStream p r).1 ∧ (planPS p T r).stk = [(requestStream p r).2] ∧
      (planPS p T r).cnt = (requestStream p r).1.length := by
  set si := inputsStream (arity := r.ell) 0 r.ell id with hsi
  set sa := vectorStream (n := r.ell) (arity := r.ell) si.1.length si.2 (clockBits p (requestWidth r) r.fuel)
    (initialExpression p r) with hsa
  set sr := roundsStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel (si.1.length + sa.1.length) sa.2
    r.fuel with hsr
  set sv := wireStream (n := r.ell) (arity := r.ell) (si.1.length + sa.1.length + sr.1.length) sr.2
    (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r)) with hsv
  have hReq : requestStream p r = (si.1 ++ sa.1 ++ sr.1 ++ sv.1, sv.2) := rfl
  obtain ⟨s1, s2⟩ := startPS_eq p T r
  obtain ⟨r1, r2⟩ := roundsPS_eq p T r r.fuel (startPS p T r).1 (startPS p T r).2 _ (by rw [s1]) s2
  have hx : ((startPS p T r).1, (startPS p T r).2) = startPS p T r := rfl
  rw [hx] at r1 r2
  change (roundsEnd p T r).1 = _ at r1
  change WireOK _ (roundsEnd p T r).2 _ at r2
  rw [s1] at r1 r2
  have hv : (verdU p).toks (reqD r) (reqEnv r) = postR (fun i => i.val)
      (verdictExpression p (requestWidth r) r.fuel (requestWidth_three r)) :=
    (verd_eq p (requestWidth r) r.fuel (requestWidth_three r) (reqD r) (reqEnv r) rfl).symm
  have hwf : (fun i : Fin (clockBits p (requestWidth r) r.fuel) => (roundsEnd p T r).2.getD i.val 0) = sr.2 :=
    funext r2.2
  rw [hReq]
  unfold planPS
  rw [hv, run_postR, hwf, r1]
  refine ⟨rfl, rfl, ?_⟩
  simp only [List.length_append]
  rfl

end NearCubicGates.Adapters.Compile.OraclePrint
