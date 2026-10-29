import SourceAdapters.Proximity.NaturalFields
import Proof.Gates.Cells.Kit

/-! Q04: paid source-code printing primitives in the released Cells register bank. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells

abbrev State := DS VV MM
abbrev Script := St VV MM

def scratch : List (Fin VV) := [t0, t1, t3, vJ]

def rest (a : State) := (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc)

structure Printed (a b : State) (word : List Bool) : Prop where
  rest_eq : rest b = rest a
  out_eq : b.out = a.out ++ word
  vars : Fr a b scratch

theorem Printed.constants {a b : State} {word : List Bool} (h : Printed a b word) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem Printed.trans {a b c : State} {x y : List Bool}
    (h : Printed a b x) (h' : Printed b c y) : Printed a c (x ++ y) :=
  ⟨h'.rest_eq.trans h.rest_eq, by rw [h'.out_eq, h.out_eq, List.append_assoc], Fr.trans h.vars h'.vars⟩

def emitBits : List Bool → Script
  | [] => skipS
  | b :: bs => .seq (.op (.emit b)) (emitBits bs)

theorem emit_bits (C : Ctx) (bits : List Bool) (a : State) :
    Hs C (emitBits bits) a (2 * bits.length + 1) (fun b => Printed a b bits) := by
  induction bits generalizing a with
  | nil =>
    exact Hs.mono (skip_spec a) (by simp) (by
      intro b hb; subst b
      exact ⟨rfl, by simp [DS.set], Fr.set a 0 (by decide)⟩)
  | cons bit bits ih =>
    have e1 := hs_emit C bit a
    refine Hs.mono (Hs.seq (t2 := 2 * bits.length + 1) e1 (fun b hb => ?_)) (by simp; omega) (fun _ h => h)
    subst b
    refine Hs.mono (ih {a with out := a.out ++ [bit]}) le_rfl ?_
    intro b hb
    exact ⟨hb.rest_eq, by simpa [List.append_assoc] using hb.out_eq, hb.vars⟩

def fieldRegs : Fin 5 ↪ Fin VV := ⟨![vZ, v2, t3, t1, t0], by decide⟩

def fieldFrom (x : Fin VV) : Script := .seq (.op (.copy t3 x)) (naturalField fieldRegs)

theorem field_from (C : Ctx) (x : Fin VV) (hx : x ≠ t3) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C (fieldFrom x) a (10 * (a.env x).bits.length + 6)
      (fun b => Printed a b (frame (a.env x).bits)) := by
  have e1 := Ex.op (OpEx.copy (C := C) t3 x a hx.symm)
  let b := a.set t3 (a.env x)
  have e2 := naturalField_run C fieldRegs hW (a.env x) b
    (by simp [b, fieldRegs, DS.set, t3, vZ]; exact hc.z)
    (by simp [b, fieldRegs, DS.set, t3, v2]; exact hc.two)
    (by simp [b, fieldRegs])
  refine ⟨_, _, Ex.seq e1 e2, by omega, ?_⟩
  refine ⟨?_, rfl, ?_⟩
  · dsimp [rest, naturalFieldState]
    split <;> simp [b, DS.set]
  · intro y hy
    have h0 : y ≠ t0 := by simp [scratch] at hy; exact hy.1
    have h1 : y ≠ t1 := by simp [scratch] at hy; exact hy.2.1
    have h3 : y ≠ t3 := by simp [scratch] at hy; exact hy.2.2.1
    dsimp [naturalFieldState]
    split <;> simp_all [b, fieldRegs, DS.set]

theorem prefix_field (C : Ctx) (pre : List Bool) (x : Fin VV) (hx : x ∉ scratch)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C (.seq (emitBits pre) (fieldFrom x)) a
      (2 * pre.length + 10 * (a.env x).bits.length + 8)
      (fun b => Printed a b (pre ++ frame (a.env x).bits)) := by
  refine Hs.mono (Hs.seq (t2 := 10 * (a.env x).bits.length + 6)
    (emit_bits C pre a) (fun b hb => ?_)) (by omega) (fun _ h => h)
  have he := field_from C x (by simp [scratch] at hx; exact hx.2.2.1) b (hb.constants hc) hW
  rw [hb.vars x hx] at he
  exact he.mono le_rfl (fun _ hd => hb.trans hd)

theorem two_fields (C : Ctx) (x y : Fin VV) (hx : x ∉ scratch) (hy : y ∉ scratch)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C (.seq (fieldFrom x) (fieldFrom y)) a
      (10 * (a.env x).bits.length + 10 * (a.env y).bits.length + 13)
      (fun b => Printed a b (frame (a.env x).bits ++ frame (a.env y).bits)) := by
  refine Hs.mono (Hs.seq (t2 := 10 * (a.env y).bits.length + 6)
    (field_from C x (by simp [scratch] at hx; exact hx.2.2.1) a hc hW)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  have he := field_from C y (by simp [scratch] at hy; exact hy.2.2.1) b (hb.constants hc) hW
  rw [hb.vars y hy] at he
  exact he.mono le_rfl (fun _ hd => hb.trans hd)

theorem prefix_two_fields (C : Ctx) (pre : List Bool) (x y : Fin VV)
    (hx : x ∉ scratch) (hy : y ∉ scratch) (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C (.seq (emitBits pre) (.seq (fieldFrom x) (fieldFrom y))) a
      (2 * pre.length + 10 * (a.env x).bits.length + 10 * (a.env y).bits.length + 15)
      (fun b => Printed a b (pre ++ frame (a.env x).bits ++ frame (a.env y).bits)) := by
  refine Hs.mono (Hs.seq
    (t2 := 10 * (a.env x).bits.length + 10 * (a.env y).bits.length + 13)
    (emit_bits C pre a) (fun b hb => ?_)) (by omega) (fun _ h => h)
  have he := two_fields C x y hx hy b (hb.constants hc) hW
  rw [hb.vars x hx, hb.vars y hy] at he
  exact he.mono le_rfl (fun _ hd => by simpa only [List.append_assoc] using hb.trans hd)

end NearCubicGates.Adapters.Proximity.SourcePrinting
