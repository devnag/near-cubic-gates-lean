import SourceAdapters.Proximity.HonestTableReuse
import SourceAdapters.Proximity.TrimHonestRowAnswers
import SourceAdapters.Proximity.RowState

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": reusable state and exact request conditions for
constructing one canonical honest assignment from actual source queries. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestRowTable

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open TrimHonest (queryStore inputStore proofStore answerStore rowStore localBound)
open HonestTableCall (truthStore)

def script (q : ℕ) : Script := .seq (SourceCallee.queryStage queryStore)
  (.seq TrimHonest.answerProgram (.seq (SourceCallee.tableStage q truthStore) HonestTableReuse.script))
def scratch : List (Fin VV) := SourceCallee.queryScratch ++ TrimHonest.answerLoopTemps ++
  DecisionCalls.scratch ++ [t0, c0, vJ]
def stores : List (Fin MM) := [queryStore, truthStore, answerStore, rowStore]
def cursors : List (Fin MM) := [queryStore, truthStore, inputStore, proofStore, answerStore, rowStore]

structure Ready {n N : ℕ} (C : Ctx) (input : BitInput n) (proof : BitInput N)
    (q sourceLength inputCursor : ℕ) (a : State) : Prop where
  source : SourceCallee.RowState q sourceLength inputCursor queryStore truthStore a
  oracle : TrimHonest.OracleReady C input proof a
  answers_length : (a.ram answerStore).length ≤ q
  answers_cursor : a.rc answerStore ≤ q
  row_length : (a.ram rowStore).length ≤ blockVariableBound q
  row_cursor : a.rc rowStore ≤ blockVariableBound q
  local_bound : a.env localBound = blockVariableBound q

structure Bounds {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (budget : ProofCall V → ℕ) (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    {N : ℕ} (input : BitInput S.arity) (proof : BitInput N) (Wd Lk Bk Λ : ℕ) : Prop where
  width_four : 4 ≤ 2 ^ Wd
  width_bits : Λ + 1 ≤ Wd
  query_width : q < 2 ^ Wd
  truth_width : 2 ^ q < 2 ^ Wd
  row_width : blockVariableBound q < 2 ^ Wd
  row_bits : coins.val.bits.length ≤ Λ
  count_bits : ((V S).queryCount coins).bits.length ≤ Λ
  query_bits : ∀ j < q, j.bits.length ≤ Λ
  address_bits : ∀ i, (SourceCallee.addressPair ((V S).query coins i)).2.bits.length ≤ Λ
  count_room : (proofCallInput V (SourceCallee.countRequest V ⟨S, coins⟩)).length ≤ Lk
  count_budget : budget (SourceCallee.countRequest V ⟨S, coins⟩) ≤ Bk
  query_room : ∀ i, (proofCallInput V (SourceCallee.queryRequest V ⟨S, coins, i⟩)).length ≤ Lk
  query_budget : ∀ i, budget (SourceCallee.queryRequest V ⟨S, coins, i⟩) ≤ Bk
  decision_room : ∀ bits : BitInput q, (proofCallInput V (SourceCallee.decisionRequest V ⟨S, coins,
    fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩)).length ≤ Lk
  decision_budget : ∀ bits : BitInput q, budget (SourceCallee.decisionRequest V ⟨S, coins,
    fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩) ≤ Bk
  table_room : 2 + 2 ^ q + q ≤ Lk
  table_budget : budget (HonestTableCall.request V (rowPredicate (V S) coins)
    (TrimHonest.rowAnswers (V S) coins input proof)) ≤ Bk

structure Result {q N : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits)) (C : Ctx)
    (input : BitInput S.arity) (proof : BitInput N) (inputCursor : ℕ) (a b : State) : Prop where
  ready : Ready C input proof q (sourceCircuitWord S).length inputCursor b
  assignment : b.ram rowStore =
    (List.ofFn (fun i : Fin (blockVariableBound q) => canonicalBlockAssignment (rowPredicate (V S) coins)
      (TrimHonest.rowAnswers (V S) coins input proof) i.val)).map Bool.toNat
  row_cursor : b.rc rowStore = blockVariableBound q
  out : b.out = a.out
  other_store : ∀ m, m ∉ stores → b.ram m = a.ram m
  other_cursor : ∀ m, m ∉ cursors → b.rc m = a.rc m
  vars : Fr a b scratch

def cost (q n N sourceLength Lk Bk Λ : ℕ) : ℕ :=
  (q * (15 * sourceLength + Lk + Bk + 30 * Λ + 64) +
    15 * sourceLength + Lk + Bk + 20 * Λ + 2 * q + 50) +
  (3 * q + (6 * (n + N) + 21) * q + 8) +
  (2 ^ q * (15 * sourceLength + 10 * Λ + 6 * q + Lk + Bk + 45) + 3) +
  (9 * 2 ^ q + 9 * q + Lk + Bk + 8 * blockVariableBound q + 28) + 3

end NearCubicGates.Adapters.Proximity.HonestRowTable
