import SourceAdapters.Code.DistinctRecordsSpec

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": live-state preservation for the counted record scan. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

structure Frame (r : Registers) (source destination : Fin MM) (a b : DS VV MM) : Prop where
  ramSource : b.ram source = a.ram source
  other : ∀ m, m ≠ source → m ≠ destination → b.ram m = a.ram m ∧ b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : Fr a b (scratch r)

namespace Frame
variable {r : Registers} {source destination : Fin MM} {a b d : DS VV MM}

theorem refl (r : Registers) (source destination : Fin MM) (a : DS VV MM) : Frame r source destination a a :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩

theorem trans (h : Frame r source destination a b) (k : Frame r source destination b d) :
    Frame r source destination a d :=
  ⟨k.ramSource.trans h.ramSource, fun m hs hd => ⟨(k.other m hs hd).1.trans (h.other m hs hd).1,
    (k.other m hs hd).2.trans (h.other m hs hd).2⟩,
    k.ip.trans h.ip, k.out.trans h.out, k.kin.trans h.kin, k.kout.trans h.kout, k.kc.trans h.kc,
    h.env.trans k.env⟩

theorem set (r : Registers) (source destination : Fin MM) (a : DS VV MM) (x : Fin VV) (value : ℕ)
    (hx : x ∈ scratch r) : Frame r source destination a (a.set x value) :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, Fr.set a value hx⟩

theorem advance (r : Registers) (source destination : Fin MM) (a : DS VV MM) :
    Frame r source destination a (a.adv source) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  intro m hs _
  simp [DS.adv, hs]

theorem put (r : Registers) (source destination : Fin MM) (hsd : source ≠ destination)
    (a : DS VV MM) (value : ℕ) : Frame r source destination a (a.put destination value) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  · simp [DS.put, hsd]
  · intro m _ hd
    simp [DS.put, hd]

theorem cst (h : Frame r source destination a b) (hv : r.Valid) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.env hv.2

theorem length_env (h : Frame r source destination a b) (hv : r.Valid) : b.env r.length = a.env r.length :=
  h.env r.length (List.nodup_cons.mp hv.1).1

end Frame
end NearCubicGates.Adapters.Code.DistinctRecords
