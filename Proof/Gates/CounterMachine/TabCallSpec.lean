import Proof.Gates.CounterMachine.ReqWord
import Proof.Gates.CounterMachine.ReqCond

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (WordFunction)

/-- The descriptor of a request, as naturals: residue `[0, part, q, |κ ++ σ|] ++ κ ++ σ`; digit moment `[1, r, j]`;
`Φ` moment `[2, r, 0]`. -/
def descN : ReqId → List ℕ
  | .residue part q κ σ => [0, partCode part, q, (κ ++ σ).length] ++ κ ++ σ
  | .digitMoment r j => [1, r, j]
  | .phiMoment r => [2, r, 0]

/-- One tabulation request of a cell call. -/
structure TabCallReq (B1 B2 cT : ℕ) where
  r : CellReq B1 B2 cT
  id : ReqId
  mem : id ∈ reqIds r.c r.p

variable {B1 B2 cT : ℕ}

def tabCallInput (x : TabCallReq B1 B2 cT) : List Bool := (descN x.id).flatMap natWord ++ cellInput x.r

theorem cellReq_hk (r : CellReq B1 B2 cT) : r.wt.I.card = r.p.k := by
  obtain ⟨w, hw⟩ := r.hw
  exact decodeWitness_card r.c r.p w r.wt hw

theorem cellReq_spec (r : CellReq B1 B2 cT) : Spec cT (header r.c) r.p := selectParams_spec cT _ r.p r.hp

theorem mem_reqIds_residue {c : Call} {p : Params} {part : Option Bool} {q : ℕ} {κ σ : List ℕ}
    (h : ReqId.residue part q κ σ ∈ reqIds c p) : q ∈ p.primes := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, q', hq', _, _, _, _, h⟩ | ⟨_, _, (⟨_, _, h⟩ | h)⟩
  · cases h; simpa using hq'
  · cases h
  · cases h

/-- The PolyTab request of a tabulation request. -/
noncomputable def tabCallTab (x : TabCallReq B1 B2 cT) : TabReq :=
  match h : x.id with
  | .residue part q κ σ =>
    resReq x.r.c x.r.p x.r.wt (cellReq_hk x.r) part q κ σ (resGates_bits x.r.c x.r.adm)
      (printCond_of x.r.c x.r.p (cellReq_spec x.r) _ _
        (resFormula_degree_le_Dmax x.r.c x.r.p (cellReq_spec x.r) x.r.wt q (mem_reqIds_residue (h ▸ x.mem)) κ σ)
        (resGates_le x.r.c x.r.adm))
  | .digitMoment r j =>
    momReq x.r.c x.r.p x.r.wt (cellReq_hk x.r) r (some j) (circ_bits x.r.c x.r.adm r)
      (printCond_of x.r.c x.r.p (cellReq_spec x.r) _ _ (momF_degree_le_Dmax x.r.c x.r.p (cellReq_spec x.r) x.r.wt r (some j))
        (circ_gates_le x.r.c x.r.adm r))
  | .phiMoment r =>
    momReq x.r.c x.r.p x.r.wt (cellReq_hk x.r) r none (circ_bits x.r.c x.r.adm r)
      (printCond_of x.r.c x.r.p (cellReq_spec x.r) _ _ (momF_degree_le_Dmax x.r.c x.r.p (cellReq_spec x.r) x.r.wt r none)
        (circ_gates_le x.r.c x.r.adm r))

theorem tabCallTab_s (x : TabCallReq B1 B2 cT) : (tabCallTab x).s = x.r.c.n - x.r.p.k := by
  unfold tabCallTab; split <;> rfl

/-- RK's output: the request's PolyTab table in lem:print's printer order. -/
noncomputable def tabCallOutput (PolyTab : TabMachine) (x : TabCallReq B1 B2 cT) : List Bool :=
  tableWord (printerOrder (tabCallTab x).s) (PolyTab.width (tabCallTab x)) (tabCallTab x)

structure TabCallMachine (B1 B2 cT : ℕ) (PolyTab : TabMachine) where
  budget : TabCallReq B1 B2 cT → ℕ
  wf : WordFunction (TabCallReq B1 B2 cT) tabCallInput (tabCallOutput PolyTab) budget
  cls : ∃ C e : ℕ, ∀ x : TabCallReq B1 B2 cT, budget x ≤ C * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e

end NearCubicGates.Close.CounterMachine
