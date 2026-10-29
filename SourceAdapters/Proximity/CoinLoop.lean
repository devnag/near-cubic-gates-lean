import SourceAdapters.Proximity.RowBody

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the variable source-coin loop.
The fixed program executes every actual row in numeric order and pays the
loop counter, every source call, and every printed literal. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg)

def coinLimitReg : Fin VV := 25

def coinProgram (q : ℕ) (queries truth : Fin MM) : Script :=
  forS rowReg coinLimitReg (rowProgram q queries truth)

def coinWords {n q : ℕ} (V : NonadaptiveVerifier n q) (k : ℕ) : List Bool :=
  (List.range k).flatMap fun i => if h : i < 2 ^ V.randomBits then blockOutputWord V ⟨i, h⟩ else []

theorem coinWords_succ {n q : ℕ} (V : NonadaptiveVerifier n q) (k : ℕ) (hk : k < 2 ^ V.randomBits) :
    coinWords V (k + 1) = coinWords V k ++ blockOutputWord V ⟨k, hk⟩ := by
  simp [coinWords, List.range_succ, hk]

theorem RowState.set_row {q L cursor : ℕ} {queries truth : Fin MM} {a : State}
    (h : RowState q L cursor queries truth a) (v : ℕ) :
    RowState q L cursor queries truth (a.set rowReg v) := by
  refine ⟨Cst.of_fr h.constants (Fr.set a v (T := [rowReg]) (by simp)) (by decide),
    ?_, ?_, ?_, h.input_cursor, h.kin_nil, h.query_length, h.query_cursor, h.truth_size, h.truth_cursor⟩
  · rw [DS.set_env_ne _ _ (by decide : QueryStep.boundReg ≠ rowReg)]
    exact h.bound_eq
  · rw [DS.set_env_ne _ _ (by decide : truthLengthReg ≠ rowReg)]
    exact h.truth_length
  · rw [DS.set_env_ne _ _ (by decide : SourceRequests.lengthReg ≠ rowReg)]
    exact h.source_length

structure CoinState {n q : ℕ} (V : NonadaptiveVerifier n q) (L cursor : ℕ) (queries truth : Fin MM)
    (a b : State) (k : ℕ) : Prop where
  state : RowState q L cursor queries truth b
  out_eq : b.out = a.out ++ coinWords V k
  other_store : ∀ m, m ≠ queries → m ≠ truth → b.ram m = a.ram m
  other_cursor : ∀ m, m ≠ queries → m ≠ truth → b.rc m = a.rc m
  vars : Fr a b (rowReg :: rowScratch)

theorem CoinState.set_row {n q L cursor k : ℕ} {V : NonadaptiveVerifier n q} {queries truth : Fin MM}
    {a b : State} (h : CoinState V L cursor queries truth a b k) (v : ℕ) :
    CoinState V L cursor queries truth a (b.set rowReg v) k :=
  ⟨h.state.set_row v, h.out_eq, h.other_store, h.other_cursor,
    h.vars.trans (Fr.set b v (List.mem_cons_self ..))⟩

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem coin_loop (S : SourceCircuit) (Wd Lk Bk Λ : ℕ) (pre tail : List Bool)
    (queries truth : Fin MM) (hdiff : queries ≠ truth) (a : State)
    (ha : RowState q (sourceCircuitWord S).length pre.length queries truth a)
    (hlimit : a.env coinLimitReg = 2 ^ (V S).randomBits) (hwidth : 2 ^ (V S).randomBits < 2 ^ Wd)
    (H : ∀ coins, RowBounds V budget S coins Wd Lk Bk Λ) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (coinProgram q queries truth) a
      (2 ^ (V S).randomBits * (rowCost q (sourceCircuitWord S).length Lk Bk Λ + 4) + 4)
      (fun b => CoinState (V S) (sourceCircuitWord S).length pre.length queries truth a b
        (2 ^ (V S).randomBits)) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  let I := fun k b => CoinState (V S) (sourceCircuitWord S).length pre.length queries truth a b k
  have e := forS_spec' (C := C) rowReg coinLimitReg (by decide) (rowProgram q queries truth) a
    (2 ^ (V S).randomBits) hwidth I (rowCost q (sourceCircuitWord S).length Lk Bk Λ)
    (fun _ _ v h => h.set_row v)
    ⟨ha, by simp [coinWords], fun _ _ _ => rfl, fun _ _ _ => rfl, Fr.refl _ _⟩ hlimit ?_
  · exact e.mono le_rfl (fun _ h => h.1)
  · intro k hk b hb hi hlim
    have er := row_body V proofLength honest budget P S ⟨k, hk⟩ Wd Lk Bk Λ pre tail
      queries truth hdiff b hb.state hi (H ⟨k, hk⟩)
    refine er.mono le_rfl (fun d hd => ?_)
    refine ⟨⟨hd.state, ?_,
      fun m hmq hmt => (hd.other_store m hmq hmt).trans (hb.other_store m hmq hmt),
      fun m hmq hmt => (hd.other_cursor m hmq hmt).trans (hb.other_cursor m hmq hmt),
      hb.vars.trans (hd.vars.weaken (fun _ h => List.mem_cons_of_mem rowReg h))⟩,
      (hd.vars rowReg (by decide)).trans hi, (hd.vars coinLimitReg (by decide)).trans hlim⟩
    rw [hd.out_eq, hb.out_eq, coinWords_succ _ _ hk, List.append_assoc]

end NearCubicGates.Adapters.Proximity.SourceCallee
