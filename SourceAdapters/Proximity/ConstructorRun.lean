import SourceAdapters.Proximity.SourceLoad
import SourceAdapters.Proximity.HeaderOutput
import SourceAdapters.Proximity.ConstructorWord

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": initialized constructor execution and its exact
flat trimming-request output. Polynomial allocation is established separately;
this theorem exposes every numerical precondition needed by the actual run. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script lengthReg)
open SourceHeader (arityReg totalRandomReg)
open QueryStep (boundReg)

def constructorProgram (q : ℕ) (queries truth : Fin MM) : Script :=
  .seq (loadSource q) (.seq randomProgram (.seq (SourceHeader.parameters q)
    (.seq SourceHeader.printHeader (coinProgram q queries truth))))

def constructorCost {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (S : SourceCircuit) (Lk Bk Λ : ℕ) : ℕ :=
  (2 * q + 2 * 2 ^ q + 30 * natBitLength (sourceCircuitWord S).length + 25 * S.arity.bits.length + 80) +
  (15 * (sourceCircuitWord S).length + Lk + Bk + 10 * (V S).randomBits.bits.length + 34) +
  (5 * (V S).randomBits + 2 * predicateBlockBits q + 12) +
  (40 * natBitLength S.arity + 40 * natBitLength ((V S).randomBits + predicateBlockBits q) + 87) +
  (2 ^ (V S).randomBits * (rowCost q (sourceCircuitWord S).length Lk Bk Λ + 4) + 4) + 4

structure ConstructorBounds {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (budget : ProofCall V → ℕ) (S : SourceCircuit) (Wd Lk Bk Λ : ℕ) : Prop where
  rows : ∀ coins, RowBounds V budget S coins Wd Lk Bk Λ
  length_width : natBitLength (sourceCircuitWord S).length + 2 ≤ Wd
  arity_width : S.arity.bits.length + 1 ≤ Wd
  rewind_width : 2 * S.arity.bits.length + 1 < 2 ^ Wd
  random_room : (proofCallInput V (randomRequest V S)).length ≤ Lk
  random_budget : budget (randomRequest V S) ≤ Bk
  random_width : (V S).randomBits.bits.length + 1 ≤ Wd
  random_numeric : (V S).randomBits < Wd
  combined_numeric : (V S).randomBits + predicateBlockBits q < 2 ^ Wd
  arity_output : natBitLength S.arity + 2 < 2 ^ Wd
  combined_output : natBitLength ((V S).randomBits + predicateBlockBits q) + 2 < 2 ^ Wd

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem constructor_run (S : SourceCircuit) (Wd Lk Bk Λ : ℕ)
    (queries truth : Fin MM) (hdiff : queries ≠ truth)
    (H : ConstructorBounds V budget S Wd Lk Bk Λ) :
    let C := context V proofLength honest budget P Wd
      (natWord (sourceCircuitWord S).length ++ sourceCircuitWord S ++ []) Lk Bk
    Hs C (constructorProgram q queries truth) (a0 : State) (constructorCost V S Lk Bk Λ)
      (fun b => b.out = Joins.trimRequestWord ⟨S.arity, clauseVerifier (V S)⟩) := by
  dsimp only
  let pre := natWord (sourceCircuitWord S).length
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ []) Lk Bk
  have H0 := H.rows ⟨0, Nat.two_pow_pos _⟩
  have e1 := load_source C q S (by simp [C, context, pre, LengthPrefix.wrapped])
    (by change 2 < 2 ^ Wd; have h := H0.width_four; omega) H0.query_width H0.truth_width H.length_width H.arity_width H.rewind_width
  obtain ⟨b, cost1, he1, hc1, hb⟩ := e1
  have e2 := source_random V proofLength honest budget P S Wd Lk Bk pre [] b hb.constants
    H0.width_four hb.source_length hb.input_cursor hb.kin_nil H.random_room H.random_budget H.random_width
  obtain ⟨d, cost2, he2, hc2, hd⟩ := e2
  have hdrest := hd.rest_eq
  simp only [SourceResults.rest, Prod.mk.injEq] at hdrest
  have hdC : Cst d := Cst.of_fr hb.constants hd.vars (by decide)
  have e3 := SourceHeader.parameters_run C q (V S).randomBits d hdC hd.value_eq
    H.random_numeric H.combined_numeric
  obtain ⟨e, cost3, he3, hc3, hepow, hetotal, hes, hef⟩ := e3
  have heC : Cst e := Cst.of_fr hdC hef (by decide)
  have hen : e.env arityReg = S.arity :=
    (hef arityReg (by decide)).trans ((hd.vars arityReg (by decide)).trans hb.arity_eq)
  have e4 := SourceHeader.print_header C e heC S.arity ((V S).randomBits + predicateBlockBits q)
    hen hetotal H0.width_two H.arity_output H.combined_output
  obtain ⟨f, cost4, he4, hc4, hf⟩ := e4
  have hfrest := hf.rest_eq
  simp only [LegacyOutput.rest, Prod.mk.injEq] at hfrest
  have hstate : RowState q (sourceCircuitWord S).length pre.length queries truth f := by
    refine ⟨hf.constants heC,
      (hf.vars boundReg (by decide)).trans ((hef boundReg (by decide)).trans
        ((hd.vars boundReg (by decide)).trans hb.bound_eq)),
      (hf.vars truthLengthReg (by decide)).trans ((hef truthLengthReg (by decide)).trans
        ((hd.vars truthLengthReg (by decide)).trans hb.truth_length)),
      (hf.vars lengthReg (by decide)).trans ((hef lengthReg (by decide)).trans
        ((hd.vars lengthReg (by decide)).trans hb.source_length)),
      hfrest.1.trans (hes.ip.trans (hdrest.1.trans hb.input_cursor)),
      hfrest.2.2.2.1.trans (hes.kin.trans hd.kin_nil), ?_, ?_, ?_, ?_⟩
    · rw [hfrest.2.1, hes.ram, hdrest.2.2.1, hb.ram_nil]
      simp
    · rw [hfrest.2.2.1, hes.rc, hdrest.2.2.2, hb.cursor_zero]
      simp
    · rw [hfrest.2.1, hes.ram, hdrest.2.2.1, hb.ram_nil]
      simp
    · rw [hfrest.2.2.1, hes.rc, hdrest.2.2.2, hb.cursor_zero]
      simp
  have hlimit : f.env coinLimitReg = 2 ^ (V S).randomBits :=
    (hf.vars coinLimitReg (by decide)).trans hepow
  have e5 := coin_loop V proofLength honest budget P S Wd Lk Bk Λ pre [] queries truth hdiff f hstate
    hlimit (Nat.pow_lt_pow_right (by decide) H.random_numeric) H.rows
  obtain ⟨g, cost5, he5, hc5, hg⟩ := e5
  refine ⟨g, cost1 + (cost2 + (cost3 + (cost4 + cost5 + 1) + 1) + 1) + 1,
    Ex.seq he1 (Ex.seq he2 (Ex.seq he3 (Ex.seq he4 he5))), ?_, ?_⟩
  · unfold constructorCost
    omega
  · change g.out = Joins.trimRequestWord ⟨S.arity, clauseVerifier (V S)⟩
    rw [hg.out_eq, hf.out_eq, hes.out, hdrest.2.1, hb.out_nil, List.nil_append]
    exact (constructor_word (V S)).symm

end NearCubicGates.Adapters.Proximity.SourceCallee
