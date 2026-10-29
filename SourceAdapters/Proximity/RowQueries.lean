import SourceAdapters.Proximity.SourceParameters

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one row's source count, paid store rewind and
actual padded-query loop. Reusing a row store overwrites its entire bounded
contents, with an explicit old-cursor charge. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg countReg boundReg)

def queryStage (m : Fin MM) : Script :=
  .seq countProgram (.seq (.op (.rwM m)) (QueryRows.queryRows m))
def queryScratch : List (Fin VV) := countReg :: QueryRows.scratch

structure Queried {N : ℕ} (m : Fin MM) (a b : State) (addresses : Fin N → Bool × ℕ) (q : ℕ) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  kin_nil : b.kin = []
  ram_eq : b.ram = Function.update a.ram m (QueryRows.rowFields addresses q)
  cursor_eq : b.rc = Function.update a.rc m (2 * q)
  count_eq : b.env countReg = N
  vars : Fr a b queryScratch

theorem Queried.constants {N : ℕ} {m : Fin MM} {a b : State} {addresses : Fin N → Bool × ℕ} {q : ℕ}
    (h : Queried m a b addresses q) (hc : Cst a) : Cst b := Cst.of_fr hc h.vars (by decide)

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem query_stage (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (m : Fin MM) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ Wd) (hwidth : Λ + 1 ≤ Wd) (hq : q < 2 ^ Wd)
    (hrow : a.env rowReg = coins.val) (hbound : a.env boundReg = q)
    (hl : a.env SourceRequests.lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hcursor : a.rc m ≤ 2 * q) (hstore : (a.ram m).length ≤ 2 * q)
    (hrowlen : coins.val.bits.length ≤ Λ) (hcountlen : ((V S).queryCount coins).bits.length ≤ Λ)
    (hjlen : ∀ j < q, j.bits.length ≤ Λ)
    (haddrlen : ∀ i, (addressPair ((V S).query coins i)).2.bits.length ≤ Λ)
    (hcroom : (proofCallInput V (countRequest V ⟨S, coins⟩)).length ≤ Lk)
    (hcbudget : budget (countRequest V ⟨S, coins⟩) ≤ Bk)
    (hroom : ∀ i, (proofCallInput V (queryRequest V ⟨S, coins, i⟩)).length ≤ Lk)
    (hbudget : ∀ i, budget (queryRequest V ⟨S, coins, i⟩) ≤ Bk) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (queryStage m) a
      (q * (15 * (sourceCircuitWord S).length + Lk + Bk + 30 * Λ + 64) +
        15 * (sourceCircuitWord S).length + Lk + Bk + 20 * Λ + 2 * q + 50)
      (fun b => Queried m a b (fun i => addressPair ((V S).query coins i)) q) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  have e1 := source_count V proofLength honest budget P S coins Wd Lk Bk pre tail a hc hW hrow hl hip
    hempty hcroom hcbudget (by omega)
  obtain ⟨b, cost1, he1, hc1, hb⟩ := e1
  have hrest := hb.rest_eq
  simp only [SourceResults.rest, Prod.mk.injEq] at hrest
  have hbC : Cst b := Cst.of_fr hc hb.vars (by decide)
  let d := b.rew m
  have er := Ex.op (OpEx.rwM (C := C) m b)
  have hdC : Cst d := ⟨hbC.z, hbC.one, hbC.two⟩
  have e2 := source_query_rows V proofLength honest budget P S coins Wd Lk Bk Λ pre tail m d hdC
    hW hwidth hq ((hb.vars rowReg (by decide)).trans hrow) hb.value_eq
    ((hb.vars boundReg (by decide)).trans hbound)
    ((hb.vars SourceRequests.lengthReg (by decide)).trans hl) (hrest.1.trans hip) hb.kin_nil
    (by simp [d, DS.rew]) hrowlen hjlen haddrlen hroom hbudget
  obtain ⟨f, cost2, he2, hc2, hf⟩ := e2
  refine ⟨f, cost1 + (b.rc m + 1 + cost2 + 1) + 1, Ex.seq he1 (Ex.seq er he2), ?_, ?_⟩
  · rw [hrest.2.2.2]
    omega
  · refine ⟨hf.ip_eq.trans hrest.1, hf.out_eq.trans hrest.2.1, hf.kin_nil, ?_, ?_,
      (hf.vars countReg (by decide)).trans hb.value_eq, ?_⟩
    · rw [hf.ram_eq]
      change Function.update b.ram m (QueryRows.rowFields _ q ++ (b.ram m).drop (2 * q)) = _
      rw [hrest.2.2.1, List.drop_eq_nil_of_le hstore, List.append_nil]
    · rw [hf.cursor_eq]
      change Function.update (Function.update b.rc m 0) m (2 * q) = _
      rw [Function.update_idem, hrest.2.2.2]
    · have h1 : Fr a d queryScratch := hb.vars.weaken (by
        intro x hx
        simp only [queryScratch, QueryRows.scratch, List.mem_cons] at hx ⊢
        tauto)
      exact h1.trans (hf.vars.weaken (fun _ h => List.mem_cons_of_mem countReg h))

end NearCubicGates.Adapters.Proximity.SourceCallee
