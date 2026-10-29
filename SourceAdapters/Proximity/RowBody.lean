import SourceAdapters.Proximity.RowState

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one complete actual source-coin action. Every
count, query, decision, finite block call and emitted translated literal is
accounted for, and the reused-store invariant is restored. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg boundReg)

structure RowResult (q sourceLength inputCursor : ℕ) (queries truth : Fin MM)
    (a b : State) (word : List Bool) : Prop where
  state : RowState q sourceLength inputCursor queries truth b
  out_eq : b.out = a.out ++ word
  other_store : ∀ m, m ≠ queries → m ≠ truth → b.ram m = a.ram m
  other_cursor : ∀ m, m ≠ queries → m ≠ truth → b.rc m = a.rc m
  vars : Fr a b rowScratch

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem row_body (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (queries truth : Fin MM) (hdiff : queries ≠ truth)
    (a : State) (ha : RowState q (sourceCircuitWord S).length pre.length queries truth a)
    (hrow : a.env rowReg = coins.val) (H : RowBounds V budget S coins Wd Lk Bk Λ) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (rowProgram q queries truth) a (rowCost q (sourceCircuitWord S).length Lk Bk Λ)
      (fun b => RowResult q (sourceCircuitWord S).length pre.length queries truth a b
        (blockOutputWord (V S) coins)) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  have e1 := query_stage V proofLength honest budget P S coins Wd Lk Bk Λ pre tail queries a ha.constants
    H.width_four H.width_bits H.query_width hrow ha.bound_eq ha.source_length ha.input_cursor ha.kin_nil
    ha.query_cursor ha.query_length H.row_bits H.count_bits H.query_bits H.address_bits
    H.count_room H.count_budget H.query_room H.query_budget
  refine Hs.mono (Hs.seq (t2 :=
    (2 ^ q * (15 * (sourceCircuitWord S).length + 10 * Λ + 6 * q + Lk + Bk + 45) + 3) +
    (9 * 2 ^ q + Lk + Bk + 3 * predicateBlockSize q * (LiteralStep.stepCost q Λ + 1) + 22) + 1)
    e1 (fun b hb => ?_)) (by unfold rowCost; omega) (fun _ h => h)
  have e2 := table_stage V proofLength honest budget P S coins Wd Lk Bk Λ pre tail truth b
    (hb.constants ha.constants) H.width_four ((hb.vars rowReg (by decide)).trans hrow) hb.count_eq
    ((hb.vars SourceRequests.lengthReg (by decide)).trans ha.source_length)
    (hb.ip_eq.trans ha.input_cursor) hb.kin_nil
    (by rw [hb.cursor_eq, Function.update_of_ne hdiff.symm]; exact ha.truth_cursor)
    (by rw [hb.ram_eq, Function.update_of_ne hdiff.symm]; exact ha.truth_size)
    H.row_bits H.decision_room H.decision_budget
  refine Hs.seq e2 (fun d hd => ?_)
  have hquery : d.ram queries = QueryRows.rowFields (fun i => addressPair ((V S).query coins i)) q := by
    rw [hd.ram_eq, Function.update_of_ne hdiff, hb.ram_eq, Function.update_self]
  have htruth : d.ram truth = (List.ofFn (predicateTable (rowPredicate (V S) coins))).map Bool.toNat := by
    rw [hd.ram_eq, Function.update_self]
  have hqc : d.rc queries ≤ 2 * q := by
    rw [hd.cursor_eq, Function.update_of_ne hdiff, hb.cursor_eq, Function.update_self]
  have htc : d.rc truth ≤ 2 ^ q := by rw [hd.cursor_eq, Function.update_self]; simp
  have hvars : Fr a d (queryScratch ++ DecisionCalls.scratch) :=
    (hb.vars.weaken (fun _ h => List.mem_append_left _ h)).trans
      (hd.vars.weaken (fun _ h => List.mem_append_right _ h))
  have e3 := render_block V proofLength honest budget P S coins Wd Lk Bk Λ
    (pre ++ sourceCircuitWord S ++ tail) queries truth hdiff d
    (hd.constants (hb.constants ha.constants)) htruth
    ((hvars truthLengthReg (by decide)).trans ha.truth_length) H.truth_width htc hd.kin_nil
    H.block_room H.block_budget H.local_width H.width_two
    ((hvars rowReg (by decide)).trans hrow) ((hvars boundReg (by decide)).trans ha.bound_eq)
    hquery hqc H.positions H.doubled_source H.auxiliary H.output_width H.local_bits H.output_bits
  refine e3.mono le_rfl (fun f hf => ?_)
  have hfinal : Fr a f rowScratch :=
    (hvars.weaken (fun _ h => List.mem_append_left _ h)).trans
      (hf.vars.weaken (fun _ h => List.mem_append_right _ h))
  refine ⟨⟨hf.constants (hd.constants (hb.constants ha.constants)),
    (hfinal boundReg (by decide)).trans ha.bound_eq,
    (hfinal truthLengthReg (by decide)).trans ha.truth_length,
    (hfinal SourceRequests.lengthReg (by decide)).trans ha.source_length,
    hf.ip_eq.trans (hd.ip_eq.trans (hb.ip_eq.trans ha.input_cursor)), hf.kin_nil,
    ?_, hf.query_cursor, ?_, hf.truth_cursor.le⟩, ?_, ?_, ?_, hfinal⟩
  · rw [hf.ram_eq, hquery, QueryRows.rowFields_length]
  · rw [hf.ram_eq, htruth]
    simp
  · rw [hf.out_eq, hd.out_eq, hb.out_eq]
  · intro m hmq hmt
    rw [hf.ram_eq, hd.ram_eq, Function.update_of_ne hmt, hb.ram_eq, Function.update_of_ne hmq]
  · intro m hmq hmt
    rw [hf.other_cursor m hmq hmt, hd.cursor_eq, Function.update_of_ne hmt,
      hb.cursor_eq, Function.update_of_ne hmq]

end NearCubicGates.Adapters.Proximity.SourceCallee
