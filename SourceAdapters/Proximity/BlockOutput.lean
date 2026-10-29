import SourceAdapters.Proximity.BlockData

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": a fixed program for every q reads
the actual common-sized block and emits the translated literal stream. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LiteralStep

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg boundReg paddedAddress)
open AddressTranslation (translatedAddress)

def emitBlock (q : ℕ) (m : Fin MM) : Script := steps m (3 * predicateBlockSize q)

theorem block_output (C : Ctx) (m : Fin MM) {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (Λ : ℕ) (a : State) (hc : Cst a)
    (hin : a.kout = blockWord (rowPredicate V coins)) (hip : a.kc = 0)
    (hwidth : ∀ index < blockVariableBound q, index.bits.length + 1 ≤ C.Wd) (hW : 2 ≤ C.Wd)
    (hrow : a.env rowReg = coins.val) (hq : a.env boundReg = q)
    (hstore : a.ram m = QueryRows.rowFields (fun i => SourceCallee.addressPair (V.query coins i)) q)
    (hcursor : a.rc m ≤ 2 * q) (hpositions : 2 * q ≤ 2 ^ C.Wd)
    (hsource : ∀ j < q,
      2 * (paddedAddress (fun i => SourceCallee.addressPair (V.query coins i)) j).2 < 2 ^ C.Wd)
    (haux : ∀ index < blockVariableBound q, 2 * Nat.pair coins.val (index - q) + 1 < 2 ^ C.Wd)
    (hvalue : ∀ index < blockVariableBound q,
      natBitLength (SourceCallee.addressPair (localAddress V coins index)).2 + 2 < 2 ^ C.Wd)
    (hlocal : ∀ index < blockVariableBound q, index.bits.length ≤ Λ)
    (hglobal : ∀ index < blockVariableBound q,
      natBitLength (SourceCallee.addressPair (localAddress V coins index)).2 ≤ Λ) :
    Hs C (emitBlock q m) a (3 * predicateBlockSize q * (stepCost q Λ + 1) + 1)
      (fun b => Written m q a b (blockWord (rowPredicate V coins)).length
        ((blockLiterals (rowPredicate V coins)).flatMap fun literal =>
          (Joins.trimQueryFields (translatedLiteral V coins literal)).flatMap natWord)) := by
  have e := literal_steps C m (fun i => SourceCallee.addressPair (V.query coins i)) coins.val q Λ
    (blockLiterals (rowPredicate V coins)) a hc [] []
    (by simpa only [List.nil_append, List.append_nil, blockLiterals_raw] using hin) hip
    (fun literal hl => hwidth literal.2 (blockLiterals_index _ _ hl)) hW hrow hq hstore hcursor
    hpositions hsource (fun literal hl => haux literal.2 (blockLiterals_index _ _ hl))
    (fun literal hl => by rw [translated_address_pair]; exact hvalue literal.2 (blockLiterals_index _ _ hl))
    (fun literal hl => hlocal literal.2 (blockLiterals_index _ _ hl))
    (fun literal hl => by rw [translated_address_pair]; exact hglobal literal.2 (blockLiterals_index _ _ hl))
  have hw : globalWords (fun i => SourceCallee.addressPair (V.query coins i)) coins.val q
      (blockLiterals (rowPredicate V coins)) =
      (blockLiterals (rowPredicate V coins)).flatMap (fun literal =>
        (Joins.trimQueryFields (translatedLiteral V coins literal)).flatMap natWord) :=
    List.flatMap_congr (fun literal _ => translated_literal_word V coins literal)
  rw [hw] at e
  simpa only [emitBlock, blockLiterals_length, List.length_nil, Nat.zero_add, blockLiterals_raw] using e

end NearCubicGates.Adapters.Proximity.LiteralStep
