import SourceAdapters.Proximity.RawFields
import SourceAdapters.Proximity.SourceLoad

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": split a raw accepted input at the circuit boundary
computed as the full word length minus the retained input arity. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.RawSplitting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open RawFields (State Script)
open SourceRequests (lengthReg)
open SourceHeader (arityReg)

def firstLength : Fin VV := 46

def split : Script := .seq (.op (.copy firstLength lengthReg))
  (.seq (.op (.sub firstLength arityReg)) (.seq (RawFields.field firstLength) (RawFields.field arityReg)))

theorem split_run (C : Ctx) (a : State) (hc : Cst a) (first second pre suffix : List Bool)
    (hin : C.inp = pre ++ (first ++ second) ++ suffix) (hip : a.ip = pre.length)
    (hlen : a.env lengthReg = first.length + second.length)
    (hsecond : a.env arityReg = second.length) :
    Hs C split a (12 * (first.length + second.length) + 21)
      (fun b => b.out = a.out ++ frame first ++ frame second) := by
  have e1 := Ex.op (OpEx.copy (C := C) firstLength lengthReg a (by decide))
  rw [hlen] at e1
  let b := a.set firstLength (first.length + second.length)
  have hbsecond : b.env arityReg = second.length := by
    simpa only [b, DS.set_env_ne _ _ (by decide : arityReg ≠ firstLength)] using hsecond
  have e2 := Ex.op (OpEx.sub (C := C) firstLength arityReg b (by decide)
    (by rw [hbsecond]; simp [b]))
  rw [hbsecond, show b.env firstLength = first.length + second.length from DS.set_env_self ..,
    Nat.add_sub_cancel] at e2
  let d := b.set firstLength first.length
  have hdC : Cst d := Cst.of_fr hc
    ((Fr.set a _ (T := [firstLength]) (by simp)).trans (Fr.set b _ (T := [firstLength]) (by simp))) (by decide)
  obtain ⟨f, nf, ef, hf, ff⟩ := RawFields.field_run C firstLength (by decide) d hdC
    first pre (second ++ suffix) (by simpa only [List.append_assoc] using hin) hip (by simp [d])
  have hfsecond : f.env arityReg = second.length := by
    rw [ff.vars arityReg (by decide)]
    simp only [d, DS.set_env_ne _ _ (by decide : arityReg ≠ firstLength), hbsecond]
  obtain ⟨g, ng, eg, hg, fg⟩ := RawFields.field_run C arityReg (by decide) f (ff.constants hdC)
    second (pre ++ first) suffix (by simpa only [List.append_assoc] using hin)
    (by rw [ff.cursor]; simp [d, b, hip]) hfsecond
  refine ⟨g, _, Ex.seq e1 (Ex.seq e2 (Ex.seq ef eg)), by omega, ?_⟩
  change g.out = a.out ++ frame first ++ frame second
  rw [fg.output, ff.output]
  rfl

end NearCubicGates.Adapters.Proximity.RawSplitting
