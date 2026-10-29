import SourceAdapters.Proximity.DecisionRecord

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": finitely many actual source-decision calls build one
truth table. The program contains only the fixed assignments; every table
value is obtained by executing the source callee, then paid RAM storage. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecisionTable

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open DecisionCalls DecisionRecord QueryStep

def tableProgram (m : Fin MM) : List (List Bool) → Script
  | [] => .op (.zero t0)
  | bits :: rest => .seq (recordDecision m bits) (tableProgram m rest)

def values (rows : List (List Bool × Bool)) : List ℕ := rows.map fun row => row.2.toNat

def passCost (C : Ctx) (source : List Bool) (row width : ℕ) : ℕ :=
  15 * source.length + 10 * row.bits.length + 6 * width + C.Lk + C.Bk + 44

structure Tabled (m : Fin MM) (a b : State) (pre tail : List ℕ) (rows : List (List Bool × Bool)) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  kin_nil : b.kin = []
  ram_eq : b.ram = Function.update a.ram m (pre ++ values rows ++ tail.drop rows.length)
  cursor_eq : b.rc = Function.update a.rc m (pre.length + rows.length)
  vars : Fr a b DecisionCalls.scratch

theorem table_program (C : Ctx) (m : Fin MM) (source pre tail : List Bool) (row N width : ℕ)
    (hW : 4 ≤ 2 ^ C.Wd) (hin : C.inp = pre ++ source ++ tail) :
    ∀ (rows : List (List Bool × Bool)) (a : State) (oldPre oldTail : List ℕ),
      Cst a → a.env rowReg = row → a.env countReg = N →
      a.env SourceRequests.lengthReg = source.length → a.ip = pre.length → a.kin = [] →
      a.ram m = oldPre ++ oldTail → a.rc m = oldPre.length →
      (∀ r ∈ rows, r.1.length ≤ width) →
      (∀ r ∈ rows, ∃ request : C.K.Req,
        C.K.inw request = decisionTag ++ source ++ frame row.bits ++ r.1.take N ∧
        (C.K.inw request).length ≤ C.Lk ∧ C.K.bud request ≤ C.Bk ∧ C.K.outw request = [r.2]) →
      Hs C (tableProgram m (rows.map Prod.fst)) a (rows.length * passCost C source row width + 1)
        (fun b => Tabled m a b oldPre oldTail rows) := by
  intro rows
  induction rows with
  | nil =>
    intro a oldPre oldTail _ _ _ _ _ hempty hram hcursor _ _
    refine ⟨a.set t0 0, 1, Ex.op (OpEx.zero t0 a), by simp, ⟨rfl, rfl, hempty, ?_, ?_, ?_⟩⟩
    · simp only [values, List.map_nil, List.append_nil, List.length_nil, List.drop_zero]
      rw [← hram]
      simp
    · simp only [List.length_nil, Nat.add_zero]
      rw [← hcursor]
      simp
    · exact Fr.set a 0 (by decide)
  | cons r rows ih =>
    intro a oldPre oldTail hc hrow hcount hl hip hempty hram hcursor hlen hreq
    obtain ⟨request, hrequest, hroom, hbudget, hout⟩ := hreq r (by simp)
    have ex := record_decision C m source pre tail r.1 row N request r.2 a hc hW hrow hcount
      hl hin hip hempty hrequest hroom hbudget hout oldPre oldTail hram hcursor
    obtain ⟨b, cost1, he1, hcost1, hb⟩ := ex
    have ex2 := ih b (oldPre ++ [r.2.toNat]) (oldTail.drop 1)
      (Cst.of_fr hc hb.vars (by decide))
      ((hb.vars rowReg (by decide)).trans hrow) ((hb.vars countReg (by decide)).trans hcount)
      ((hb.vars SourceRequests.lengthReg (by decide)).trans hl) (hb.ip_eq.trans hip) hb.kin_nil
      (by rw [hb.ram_eq]; simp only [Function.update_self])
      (by rw [hb.cursor_eq]; simp)
      (fun s hs => hlen s (by simp [hs])) (fun s hs => hreq s (by simp [hs]))
    obtain ⟨d, cost2, he2, hcost2, hd⟩ := ex2
    refine ⟨d, cost1 + cost2 + 1, Ex.seq he1 he2, ?_, ?_⟩
    · have hlenr := hlen r (by simp)
      dsimp only [passCost] at hcost2 ⊢
      simp only [List.length_cons]
      nlinarith
    · refine ⟨hd.ip_eq.trans hb.ip_eq, hd.out_eq.trans hb.out_eq, hd.kin_nil, ?_, ?_, hb.vars.trans hd.vars⟩
      · rw [hd.ram_eq, hb.ram_eq, Function.update_idem]
        simp [values, List.append_assoc]
      · rw [hd.cursor_eq, hb.cursor_eq, Function.update_idem]
        simp only [List.length_append, List.length_cons, List.length_nil]
        congr 1
        omega

end NearCubicGates.Adapters.Proximity.DecisionTable
