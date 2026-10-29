import SourceAdapters.Proximity.QueryRecord

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one iteration of the fixed-query row loader.
Only indices below the source's actual count reach its dependent request domain;
remaining slots receive the ignored proof-coordinate-zero padding query. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.QueryStep

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open QueryRecord

def rowReg : Fin VV := 21
def indexReg : Fin VV := 22
def countReg : Fin VV := 23
def boundReg : Fin VV := 29
def queryTag : List Bool := [false, true, true, false]

def paddedAddress {N : ℕ} (addresses : Fin N → Bool × ℕ) (j : ℕ) : Bool × ℕ :=
  if h : j < N then addresses ⟨j, h⟩ else (true, 0)

def queryStep (m : Fin MM) : Script :=
  .ite (.lt indexReg countReg) (realQuery m queryTag [rowReg, indexReg]) (dummyQuery m)

def stepCost (C : Ctx) (source : List Bool) (Λ : ℕ) : ℕ :=
  15 * source.length + C.Lk + C.Bk + 30 * Λ + 60

theorem query_step (C : Ctx) (m : Fin MM) (source pre tail : List Bool) (row N j Λ : ℕ)
    (addresses : Fin N → Bool × ℕ) (requests : Fin N → C.K.Req) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hwidth : Λ + 1 ≤ C.Wd)
    (hrow : a.env rowReg = row) (hindex : a.env indexReg = j) (hcount : a.env countReg = N)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrowlen : row.bits.length ≤ Λ) (hjlen : j.bits.length ≤ Λ)
    (haddrlen : ∀ i, (addresses i).2.bits.length ≤ Λ)
    (hrequest : ∀ i, C.K.inw (requests i) = queryTag ++ source ++ frame row.bits ++ frame i.val.bits)
    (hroom : ∀ i, (C.K.inw (requests i)).length ≤ C.Lk)
    (hbudget : ∀ i, C.K.bud (requests i) ≤ C.Bk)
    (hout : ∀ i, C.K.outw (requests i) = (addresses i).1 :: frame (addresses i).2.bits)
    (oldPre oldTail : List ℕ) (hram : a.ram m = oldPre ++ oldTail) (hcursor : a.rc m = oldPre.length) :
    Hs C (queryStep m) a (stepCost C source Λ)
      (fun b => Recorded m a b oldPre oldTail (paddedAddress addresses j).1.toNat
        (paddedAddress addresses j).2) := by
  by_cases hj : j < N
  · let i : Fin N := ⟨j, hj⟩
    have e := real_query C m queryTag source pre tail [rowReg, indexReg]
      (requests i) (addresses i).1 (addresses i).2 a hc hW (by decide)
      hl hin hip hempty (by
        rw [hrequest]
        simp [SourceRequests.fieldsWord, hrow, hindex, i, List.append_assoc])
      (hroom i) (hbudget i) (hout i) (by have := haddrlen i; omega) oldPre oldTail hram hcursor
    obtain ⟨b, cost, he, hcost, hb⟩ := e
    refine ⟨b, cost + 1, Ex.iteT (by decide : indexReg ≠ countReg) (by simp [Cnd.eval, hindex, hcount, hj]) he, ?_, ?_⟩
    · have ha := haddrlen i
      dsimp [stepCost]
      simp only [queryTag, List.length_cons, List.length_nil, SourceRequests.fieldsCost,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrow, hindex] at hcost
      omega
    · simpa [paddedAddress, hj, i] using hb
  · obtain ⟨b, cost, he, hcost, hb⟩ := dummy_query C m a hc hempty oldPre oldTail hram hcursor
    refine ⟨b, cost + 1, Ex.iteF (by decide : indexReg ≠ countReg) (by simp [Cnd.eval, hindex, hcount, hj]) he, ?_, ?_⟩
    · dsimp [stepCost]; omega
    · simpa [paddedAddress, hj] using hb

end NearCubicGates.Adapters.Proximity.QueryStep
