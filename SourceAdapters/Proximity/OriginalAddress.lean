import SourceAdapters.Proximity.QueryLookup
import SourceAdapters.Proximity.AddressRenaming
import SourceAdapters.Proximity.SourceResults

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual lookup and even-address
translation for a local index that names a saved original query. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.OriginalAddress

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (resultReg)

def positionReg : Fin VV := 32
def kindReg : Fin VV := 33
def addressReg : Fin VV := 34
def scratch : List (Fin VV) := [positionReg, c0, vJ, kindReg, addressReg]
def renameRegs : Fin 3 ↪ Fin VV := ⟨![vZ, kindReg, addressReg], by decide⟩

def originalProgram (m : Fin MM) : Script :=
  .seq (.op (.copy positionReg resultReg)) (.seq (.op (.shl positionReg))
    (.seq (QueryLookup.fetchPair m positionReg kindReg addressReg) (AddressRenaming.renameProgram renameRegs)))

theorem original_program (C : Ctx) (m : Fin MM) (a : State) (hc : Cst a)
    (index address : ℕ) (proof : Bool) (pre tail : List ℕ)
    (hi : a.env resultReg = index) (hpre : pre.length = 2 * index)
    (hstore : a.ram m = pre ++ proof.toNat :: address :: tail)
    (hpos : 2 * index < 2 ^ C.Wd) (haddr : 2 * address < 2 ^ C.Wd) :
    Hs C (originalProgram m) a (a.rc m + 10 * index + 18) (fun b =>
      b.env kindReg = proof.toNat ∧ b.env addressReg = (if proof then 2 * address else address) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc m (2 * index + 2) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b scratch) := by
  have e1 := Ex.op (OpEx.copy (C := C) positionReg resultReg a (by decide))
  rw [hi] at e1
  let b := a.set positionReg index
  have hb : b.env positionReg = index := by simp [b]
  have e2 := Ex.op (OpEx.shl (C := C) positionReg b (by rw [hb]; exact hpos))
  rw [hb] at e2
  let d := b.set positionReg (2 * index)
  have e3 := QueryLookup.fetch_pair C m positionReg kindReg addressReg (by decide) (by decide) (by decide)
    d pre tail proof.toNat address hstore (by simp [d, hpre]) (by simpa only [hpre] using hpos)
  obtain ⟨f, cost3, he3, hc3, hf⟩ := e3
  rcases hf with ⟨hk, ha, hip, ho, hm, hrc, hki, hko, hkc, hfr⟩
  have hfz : f.env vZ = 0 := by
    rw [hfr vZ (by decide)]
    change ((a.set positionReg index).set positionReg (2 * index)).env vZ = 0
    rw [DS.set_env_ne _ _ (by decide : vZ ≠ positionReg),
      DS.set_env_ne _ _ (by decide : vZ ≠ positionReg)]
    exact hc.z
  have e4 := AddressRenaming.rename_program C renameRegs f proof address hfz hk ha haddr
  obtain ⟨g, cost4, he4, hc4, hg⟩ := e4
  rcases hg with ⟨gk, ga, gs, gf⟩
  refine ⟨g, 1 + (1 + (cost3 + cost4 + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.seq he3 he4)), ?_, ?_⟩
  · change cost3 ≤ a.rc m + 5 * pre.length + 11 at hc3
    rw [hpre] at hc3
    omega
  · refine ⟨gk, ga, gs.ip.trans hip, gs.out.trans ho, gs.ram.trans hm, ?_,
      gs.kin.trans hki, gs.kout.trans hko, gs.kc.trans hkc, ?_⟩
    · rw [gs.rc, hrc, hpre]
      rfl
    · have h1 : Fr a d scratch := Fr.trans (Fr.set a index (by simp [scratch]))
        (Fr.set b (2 * index) (by simp [scratch]))
      have h2 : Fr d f scratch := hfr.weaken (by
        intro x hx
        simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto)
      have h3 : Fr f g scratch := gf.weaken (by
        intro x hx
        simp only [renameRegs, Function.Embedding.coeFn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp [scratch])
      exact h1.trans (h2.trans h3)

end NearCubicGates.Adapters.Proximity.OriginalAddress
