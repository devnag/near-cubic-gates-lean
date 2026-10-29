import Proof.Gates.Cells.Kit

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": paid serialization of the flat trimming request.
These fields use the target request's natWord codec, including its unary
bit-length header, and preserve the current callee-output parsing cursor. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LegacyOutput

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
abbrev State := DS VV MM
abbrev Script := St VV MM

def scratch : List (Fin VV) := t3 :: emitNatT

def rest (a : State) := (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc)

structure Printed (a b : State) (word : List Bool) : Prop where
  rest_eq : rest b = rest a
  out_eq : b.out = a.out ++ word
  vars : Fr a b scratch

theorem Printed.constants {a b : State} {word : List Bool} (h : Printed a b word) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem Printed.trans {a b c : State} {x y : List Bool}
    (h : Printed a b x) (h' : Printed b c y) : Printed a c (x ++ y) :=
  ⟨h'.rest_eq.trans h.rest_eq, by rw [h'.out_eq, h.out_eq, List.append_assoc], h.vars.trans h'.vars⟩

def fieldFrom (x : Fin VV) : Script := .seq (.op (.copy t3 x)) emitNatO

theorem field_from (C : Ctx) (x : Fin VV) (hx : x ≠ t3) (a : State) (hc : Cst a)
    (hW : 2 ≤ C.Wd) (hvalue : natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (fieldFrom x) a (40 * natBitLength (a.env x) + 42)
      (fun b => Printed a b (natWord (a.env x))) := by
  have e1 := Ex.op (OpEx.copy (C := C) t3 x a hx.symm)
  let b := a.set t3 (a.env x)
  have hbC : Cst b := Cst.of_fr hc (Fr.set a _ (T := [t3]) (by simp)) (by decide)
  have e2 := emitNatO_spec (C := C) b hbC hW (by simpa [b] using hvalue)
  obtain ⟨d, cost, he2, hcost, hd⟩ := e2
  refine ⟨d, 1 + cost + 1, Ex.seq e1 he2, by simp only [b, DS.set_env_self] at hcost; omega, ?_⟩
  refine ⟨hd.2.1, by simpa [b] using hd.1, ?_⟩
  exact (Fr.set a _ (List.mem_cons_self ..)).trans
    (hd.2.2.2.weaken (fun _ h => List.mem_cons_of_mem t3 h))

def fieldsWord (a : State) (xs : List (Fin VV)) : List Bool := xs.flatMap fun x => natWord (a.env x)
def fieldsCost (a : State) (xs : List (Fin VV)) : ℕ :=
  (xs.map fun x => 40 * natBitLength (a.env x) + 43).sum + 1

def fieldsFrom : List (Fin VV) → Script
  | [] => .op (.zero t3)
  | x :: xs => .seq (fieldFrom x) (fieldsFrom xs)

theorem fields_from (C : Ctx) (xs : List (Fin VV)) (a : State) (hc : Cst a)
    (hW : 2 ≤ C.Wd) (hxs : ∀ x ∈ xs, x ∉ scratch)
    (hvalue : ∀ x ∈ xs, natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (fieldsFrom xs) a (fieldsCost a xs) (fun b => Printed a b (fieldsWord a xs)) := by
  induction xs generalizing a with
  | nil =>
    refine ⟨_, 1, Ex.op (OpEx.zero (C := C) t3 a), by simp [fieldsCost], ?_⟩
    exact ⟨rfl, by simp [fieldsWord], Fr.set a 0 (List.mem_cons_self ..)⟩
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hxt : x ≠ t3 := fun h => hx (by simp [scratch, h])
    have e := field_from C x hxt a hc hW (hvalue x (by simp))
    refine Hs.mono (Hs.seq (t2 := fieldsCost a xs) e (fun b hb => ?_)) ?_ (fun _ h => h)
    · have heq : ∀ x ∈ xs, b.env x = a.env x := fun x hx => hb.vars x (hxs x (by simp [hx]))
      have hw : fieldsWord b xs = fieldsWord a xs := List.flatMap_congr (fun x hx => by rw [heq x hx])
      have ht : fieldsCost b xs = fieldsCost a xs := by
        unfold fieldsCost
        congr 2
        exact List.map_congr_left (fun x hx => by rw [heq x hx])
      have ei := ih b (hb.constants hc) (fun x hx => hxs x (by simp [hx]))
        (fun x hx => by rw [heq x hx]; exact hvalue x (by simp [hx]))
      rw [hw, ht] at ei
      exact ei.mono le_rfl (fun _ hd => by simpa [fieldsWord] using hb.trans hd)
    · simp only [fieldsCost, List.map_cons, List.sum_cons]
      omega

end NearCubicGates.Adapters.Proximity.LegacyOutput
