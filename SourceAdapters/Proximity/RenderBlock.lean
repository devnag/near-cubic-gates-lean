import SourceAdapters.Proximity.SourceBlockCall
import SourceAdapters.Proximity.BlockOutput

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": call the actual finite block
compiler on the stored source truth table, then serialize every translated
literal. Both the source call and all block-output operations are charged. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg boundReg paddedAddress)

def truthLengthReg : Fin VV := 40

def renderBlock (q : ℕ) (queries truth : Fin MM) : Script :=
  .seq (StoredCall.callStored truth truthLengthReg blockTag) (LiteralStep.emitBlock q queries)

def blockOutputWord {n q : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits)) : List Bool :=
  (blockLiterals (rowPredicate V coins)).flatMap fun literal =>
    (Joins.trimQueryFields (translatedLiteral V coins literal)).flatMap natWord

structure Rendered (queries truth : Fin MM) (q : ℕ) (a b : State) (word : List Bool) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out ++ word
  ram_eq : b.ram = a.ram
  query_cursor : b.rc queries ≤ 2 * q
  truth_cursor : b.rc truth = 2 ^ q
  other_cursor : ∀ s, s ≠ queries → s ≠ truth → b.rc s = a.rc s
  kin_nil : b.kin = []
  vars : Fr a b LiteralStep.scratch

theorem Rendered.constants {queries truth : Fin MM} {q : ℕ} {a b : State} {word : List Bool}
    (h : Rendered queries truth q a b word) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem render_block (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk Λ : ℕ) (input : List Bool) (queries truth : Fin MM) (hdiff : queries ≠ truth)
    (a : State) (hc : Cst a)
    (ht : a.ram truth = (List.ofFn (predicateTable (rowPredicate (V S) coins))).map Bool.toNat)
    (htlen : a.env truthLengthReg = 2 ^ q) (htwidth : 2 ^ q < 2 ^ Wd) (htcursor : a.rc truth ≤ 2 ^ q)
    (hempty : a.kin = []) (hroom : 5 + 2 ^ q ≤ Lk)
    (hbudget : budget (blockRequest V (predicateTable (rowPredicate (V S) coins))) ≤ Bk)
    (hwidth : ∀ index < blockVariableBound q, index.bits.length + 1 ≤ Wd) (hW : 2 ≤ Wd)
    (hrow : a.env rowReg = coins.val) (hq : a.env boundReg = q)
    (hstore : a.ram queries = QueryRows.rowFields (fun i => addressPair ((V S).query coins i)) q)
    (hcursor : a.rc queries ≤ 2 * q) (hpositions : 2 * q ≤ 2 ^ Wd)
    (hsource : ∀ j < q, 2 * (paddedAddress (fun i => addressPair ((V S).query coins i)) j).2 < 2 ^ Wd)
    (haux : ∀ index < blockVariableBound q, 2 * Nat.pair coins.val (index - q) + 1 < 2 ^ Wd)
    (hvalue : ∀ index < blockVariableBound q,
      natBitLength (addressPair (localAddress (V S) coins index)).2 + 2 < 2 ^ Wd)
    (hlocal : ∀ index < blockVariableBound q, index.bits.length ≤ Λ)
    (hglobal : ∀ index < blockVariableBound q,
      natBitLength (addressPair (localAddress (V S) coins index)).2 ≤ Λ) :
    let C := context V proofLength honest budget P Wd input Lk Bk
    Hs C (renderBlock q queries truth) a
      (9 * 2 ^ q + Lk + Bk + 3 * predicateBlockSize q * (LiteralStep.stepCost q Λ + 1) + 22)
      (fun b => Rendered queries truth q a b (blockOutputWord (V S) coins)) := by
  dsimp only
  let C := context V proofLength honest budget P Wd input Lk Bk
  have e1 := source_block_call V proofLength honest budget P (rowPredicate (V S) coins) Wd Lk Bk input
    truth truthLengthReg (by decide) (by decide) (by decide) a hc ht htlen htwidth hempty hroom hbudget
  refine Hs.mono (Hs.seq (t2 := 3 * predicateBlockSize q * (LiteralStep.stepCost q Λ + 1) + 1)
    e1 (fun b hb => ?_)) (by omega) (fun _ h => h)
  rcases hb with ⟨hip, ho, hm, htc, hother, hki, hko, hkc, hC, hf⟩
  have e2 := LiteralStep.block_output C queries (V S) coins Λ b hC hko hkc hwidth hW
    ((hf rowReg (by decide)).trans hrow) ((hf boundReg (by decide)).trans hq)
    (by rw [hm]; exact hstore) (by rw [hother queries hdiff]; exact hcursor) hpositions
    hsource haux hvalue hlocal hglobal
  refine e2.mono le_rfl (fun d hd => ?_)
  refine ⟨hd.ip_eq.trans hip, ?_, hd.ram_eq.trans hm, hd.cursor_bound,
    (hd.other_cursor truth hdiff.symm).trans htc,
    fun s hs ht => (hd.other_cursor s hs).trans (hother s ht), hd.kin_eq.trans hki, ?_⟩
  · rw [hd.out_eq, ho]
    rfl
  · exact (hf.weaken (by decide)).trans hd.vars

end NearCubicGates.Adapters.Proximity.SourceCallee
