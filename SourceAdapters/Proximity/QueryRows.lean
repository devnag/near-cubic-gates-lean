import SourceAdapters.Proximity.QueryStep
import Proof.Gates.Cells.Loop

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual fixed-q source query loop, including
at-most-q padding and in-place replacement of the finite row store. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.QueryRows

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open QueryStep

def rowFields {N : ℕ} (addresses : Fin N → Bool × ℕ) (k : ℕ) : List ℕ :=
  (List.range k).flatMap fun j => [(paddedAddress addresses j).1.toNat, (paddedAddress addresses j).2]

@[simp] theorem rowFields_zero {N : ℕ} (addresses : Fin N → Bool × ℕ) : rowFields addresses 0 = [] := rfl

theorem rowFields_succ {N : ℕ} (addresses : Fin N → Bool × ℕ) (k : ℕ) :
    rowFields addresses (k + 1) = rowFields addresses k ++
      [(paddedAddress addresses k).1.toNat, (paddedAddress addresses k).2] := by
  simp [rowFields, List.range_succ]

@[simp] theorem rowFields_length {N : ℕ} (addresses : Fin N → Bool × ℕ) (k : ℕ) :
    (rowFields addresses k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rowFields_succ, List.length_append, ih]; simp; omega

def scratch : List (Fin VV) := indexReg :: SourceResults.scratch

structure Loaded {N : ℕ} (m : Fin MM) (a b : State) (addresses : Fin N → Bool × ℕ) (k : ℕ) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  kin_nil : b.kin = []
  ram_eq : b.ram = Function.update a.ram m (rowFields addresses k ++ (a.ram m).drop (2 * k))
  cursor_eq : b.rc = Function.update a.rc m (2 * k)
  vars : Fr a b scratch

theorem Loaded.set_counter {N : ℕ} {m : Fin MM} {a b : State} {addresses : Fin N → Bool × ℕ} {k : ℕ}
    (h : Loaded m a b addresses k) (v : ℕ) : Loaded m a (b.set indexReg v) addresses k :=
  ⟨h.ip_eq, h.out_eq, h.kin_nil, h.ram_eq, h.cursor_eq,
    Fr.trans h.vars (Fr.set b v (List.mem_cons_self ..))⟩

theorem Loaded.constants {N : ℕ} {m : Fin MM} {a b : State} {addresses : Fin N → Bool × ℕ} {k : ℕ}
    (h : Loaded m a b addresses k) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

def queryRows (m : Fin MM) : Script := forS indexReg boundReg (queryStep m)

theorem query_rows (C : Ctx) (m : Fin MM) (source pre tail : List Bool) (row N q Λ : ℕ)
    (addresses : Fin N → Bool × ℕ) (requests : Fin N → C.K.Req) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hwidth : Λ + 1 ≤ C.Wd) (hq : q < 2 ^ C.Wd)
    (hrow : a.env rowReg = row) (hcount : a.env countReg = N) (hbound : a.env boundReg = q)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = []) (hcursor : a.rc m = 0)
    (hrowlen : row.bits.length ≤ Λ) (hjlen : ∀ j < q, j.bits.length ≤ Λ)
    (haddrlen : ∀ i, (addresses i).2.bits.length ≤ Λ)
    (hrequest : ∀ i, C.K.inw (requests i) = queryTag ++ source ++ frame row.bits ++ frame i.val.bits)
    (hroom : ∀ i, (C.K.inw (requests i)).length ≤ C.Lk)
    (hbudget : ∀ i, C.K.bud (requests i) ≤ C.Bk)
    (hout : ∀ i, C.K.outw (requests i) = (addresses i).1 :: frame (addresses i).2.bits) :
    Hs C (queryRows m) a (q * (stepCost C source Λ + 4) + 4)
      (fun b => Loaded m a b addresses q) := by
  let I : ℕ → State → Prop := fun k b => Loaded m a b addresses k
  have e := forS_spec' (C := C) indexReg boundReg (by decide) (queryStep m) a q hq I
    (stepCost C source Λ) (fun _ _ v h => h.set_counter v)
    (by
      refine ⟨rfl, rfl, hempty, ?_, ?_, Fr.refl _ _⟩
      · simp
      · simp only [Nat.mul_zero]
        rw [← hcursor]
        simp)
    hbound ?_
  · exact e.mono le_rfl (fun _ h => h.1)
  · intro k hk b hb hi hlimit
    have er := query_step C m source pre tail row N k Λ addresses requests b (hb.constants hc) hW hwidth
      ((hb.vars rowReg (by decide)).trans hrow) hi ((hb.vars countReg (by decide)).trans hcount)
      ((hb.vars SourceRequests.lengthReg (by decide)).trans hl) hin (hb.ip_eq.trans hip) hb.kin_nil
      hrowlen (hjlen k hk) haddrlen hrequest hroom hbudget hout (rowFields addresses k) ((a.ram m).drop (2 * k))
      (by rw [hb.ram_eq]; simp) (by rw [hb.cursor_eq]; simp)
    refine er.mono le_rfl (fun d hd => ?_)
    refine ⟨⟨hd.ip_eq.trans hb.ip_eq, hd.out_eq.trans hb.out_eq, hd.kin_nil, ?_, ?_,
      Fr.trans hb.vars (hd.vars.weaken (fun _ hm => List.mem_cons_of_mem indexReg hm))⟩,
      (hd.vars indexReg (by decide)).trans hi, (hd.vars boundReg (by decide)).trans hlimit⟩
    · rw [hd.ram_eq, hb.ram_eq, Function.update_idem, rowFields_succ]
      simp only [List.drop_drop, Nat.mul_add, Nat.mul_one, List.append_assoc]
    · rw [hd.cursor_eq, hb.cursor_eq, Function.update_idem, rowFields_length]
      simp only [Nat.mul_add, Nat.mul_one]

end NearCubicGates.Adapters.Proximity.QueryRows
