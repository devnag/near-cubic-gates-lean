import SourceAdapters.Proximity.RequestPrefix
import Proof.Gates.Cells.Kit

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": source requests in the fixed ordinary register bank.
Circuit copying restores the input cursor; source parameters remain available
for the subsequent row loops. Every request bit is emitted by a paid operation. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceRequests

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CellSending
open RequestWriting

abbrev State := DS VV MM
abbrev Script := St VV MM

def lengthReg : Fin VV := 20
def scratch : List (Fin VV) := [t0, t1, t3]
def copyRegs : Fin 5 ↪ Fin VV := ⟨![vZ, v1, t0, t1, lengthReg], by decide⟩
def fieldRegs : Fin 5 ↪ Fin VV := ⟨![vZ, v2, t3, t1, t0], by decide⟩

def rest (a : State) := (a.ip, a.out, a.ram, a.rc, a.kout, a.kc)

structure Requested (a b : State) (word : List Bool) : Prop where
  rest_eq : rest b = rest a
  kin_eq : b.kin = a.kin ++ word
  vars : Fr a b scratch

theorem Requested.constants {a b : State} {word : List Bool} (h : Requested a b word) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem Requested.trans {a b c : State} {x y : List Bool}
    (h : Requested a b x) (h' : Requested b c y) : Requested a c (x ++ y) :=
  ⟨h'.rest_eq.trans h.rest_eq, by rw [h'.kin_eq, h.kin_eq, List.append_assoc], Fr.trans h.vars h'.vars⟩

def beginRequest (tag : List Bool) : Script := prefixRequest copyRegs tag

theorem begin_request (C : Ctx) (tag source pre tail : List Bool) (a : State) (hc : Cst a)
    (hl : a.env lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hroom : a.kin.length + tag.length + source.length ≤ C.Lk) :
    Hs C (beginRequest tag) a (2 * tag.length + 15 * source.length + 13)
      (fun b => Requested a b (tag ++ source)) := by
  have e := prefix_request C copyRegs a tag source pre tail hc.z hc.one hl hin hip hroom
  refine ⟨_, _, e, le_rfl, ?_⟩
  refine ⟨rfl, rfl, ?_⟩
  intro x hx
  have hx0 : x ≠ t0 := by simpa [scratch] using fun h => hx (by simp [scratch, h])
  have hx1 : x ≠ t1 := fun h => hx (by simp [scratch, h])
  simp [prefixResult, copyRegs, sent, DS.set, hx0, hx1]

def fieldFrom (x : Fin VV) : Script := appendNatural fieldRegs x

theorem field_from (C : Ctx) (x : Fin VV) (hx : x ∉ scratch) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hroom : a.kin.length + (frame (a.env x).bits).length ≤ C.Lk) :
    Hs C (fieldFrom x) a (10 * (a.env x).bits.length + 6)
      (fun b => Requested a b (frame (a.env x).bits)) := by
  have hne : fieldRegs 2 ≠ x := by
    intro h
    exact hx (by simp [fieldRegs, ← h, scratch])
  have e := append_natural C fieldRegs x hne a (a.env x) hc.z hc.two rfl hW hroom
  refine ⟨_, _, e, le_rfl, ?_⟩
  refine ⟨?_, rfl, ?_⟩
  · dsimp [rest, appendNaturalResult, naturalCallFieldState]
    split <;> rfl
  · intro y hy
    apply appendNaturalResult_env
    all_goals intro he; exact hy (by simp [fieldRegs] at he; simp [scratch, he])

def fieldsWord (a : State) (xs : List (Fin VV)) : List Bool :=
  xs.flatMap fun x => frame (a.env x).bits

def fieldsCost (a : State) (xs : List (Fin VV)) : ℕ :=
  (xs.map fun x => 10 * (a.env x).bits.length + 7).sum + 1

def fieldsFrom : List (Fin VV) → Script
  | [] => .op (.zero t0)
  | x :: xs => .seq (fieldFrom x) (fieldsFrom xs)

theorem fields_from (C : Ctx) (xs : List (Fin VV)) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hxs : ∀ x ∈ xs, x ∉ scratch)
    (hroom : a.kin.length + (fieldsWord a xs).length ≤ C.Lk) :
    Hs C (fieldsFrom xs) a (fieldsCost a xs) (fun b => Requested a b (fieldsWord a xs)) := by
  induction xs generalizing a with
  | nil =>
    refine ⟨a.set t0 0, 1, Ex.op (OpEx.zero t0 a), by simp [fieldsCost], ?_⟩
    exact ⟨rfl, by simp [fieldsWord], Fr.set a 0 (by simp [scratch])⟩
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have er := field_from C x hx a hc hW (by
      simp only [fieldsWord, List.flatMap_cons, List.length_append] at hroom
      omega)
    refine Hs.mono (Hs.seq (t2 := fieldsCost a xs) er (fun b hb => ?_)) ?_ (fun _ h => h)
    · have heq : ∀ x ∈ xs, b.env x = a.env x := fun x hx => hb.vars x (hxs x (by simp [hx]))
      have hw : fieldsWord b xs = fieldsWord a xs := by
        apply List.flatMap_congr
        intro x hx
        rw [heq x hx]
      have ht : fieldsCost b xs = fieldsCost a xs := by
        unfold fieldsCost
        congr 2
        apply List.map_congr_left
        intro x hx
        rw [heq x hx]
      have e := ih b (hb.constants hc) (fun x hx => hxs x (by simp [hx])) (by
        rw [hw, hb.kin_eq, List.length_append]
        simpa [fieldsWord, Nat.add_assoc] using hroom)
      rw [hw, ht] at e
      exact e.mono le_rfl (fun _ hd => by simpa [fieldsWord] using hb.trans hd)
    · simp only [fieldsCost, List.map_cons, List.sum_cons]
      omega

def writeRequest (tag : List Bool) (xs : List (Fin VV)) : Script :=
  .seq (beginRequest tag) (fieldsFrom xs)

theorem write_request (C : Ctx) (tag source pre tail : List Bool) (xs : List (Fin VV))
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) (hxs : ∀ x ∈ xs, x ∉ scratch)
    (hl : a.env lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length)
    (hroom : a.kin.length + tag.length + source.length + (fieldsWord a xs).length ≤ C.Lk) :
    Hs C (writeRequest tag xs) a
      (2 * tag.length + 15 * source.length + fieldsCost a xs + 14)
      (fun b => Requested a b (tag ++ source ++ fieldsWord a xs)) := by
  refine Hs.mono (Hs.seq (t2 := fieldsCost a xs)
    (begin_request C tag source pre tail a hc hl hin hip (by omega)) (fun b hb => ?_)) (by omega) (fun _ h => h)
  · have hw : fieldsWord b xs = fieldsWord a xs := by
      apply List.flatMap_congr
      intro x hx
      rw [hb.vars x (hxs x hx)]
    have ht : fieldsCost b xs = fieldsCost a xs := by
      unfold fieldsCost
      congr 2
      apply List.map_congr_left
      intro x hx
      rw [hb.vars x (hxs x hx)]
    have e := fields_from C xs b (hb.constants hc) hW hxs (by
      rw [hw, hb.kin_eq]
      simpa only [List.length_append, Nat.add_assoc] using hroom)
    rw [hw, ht] at e
    exact e.mono le_rfl (fun _ hd => hb.trans hd)

end NearCubicGates.Adapters.Proximity.SourceRequests
