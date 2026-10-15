import Proof.PCP.PCPPQuerySupportSemantics

/-! Same-cache support access, retaining the source and both real drivers.
These are the literal endpoints required by the paid reusable caller. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupport
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lookup_retained_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin p.systematicBits) :
    ∃ receipt,runFrom machine (budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity i.val)
      (ready (pcppOutput r p) r.arity i.val)=some receipt ∧
      receipt.steps=budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity i.val ∧
      receipt.final.tapes 4=mask r p i ∧ receipt.final.heads 4=r.arity ∧
      receipt.final.tapes 0=pcppOutput r p ∧
      receipt.final.tapes 3=UnaryTemplate.tape r.arity ∧ receipt.final.heads 3=1 ∧
      receipt.final.tapes 5=UnaryTemplate.tape i.val ∧ receipt.final.heads 5=1 := by
  let rows := supportRows r p
  have hi : i.val<rows.length := by simp [rows,supportRows]
  have hs : (rows.take i.val).flatten++rows[i.val]++(rows.drop (i.val+1)).flatten=rows.flatten :=
    MatrixCropCells.split_at rows i.val hi
  have hm : rows[i.val]=mask r p i := by simp [rows,supportRows]
  have hw : ∀ row∈rows.take i.val,row.length=r.arity := by
    intro row hrow
    have hmem := List.mem_of_mem_take hrow
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hmem
    rw [← hj]
    simp [mask]
  have hrow : (rows[i.val]).length=r.arity := by rw [hm]; simp [mask]
  obtain ⟨base,hb,hsource0,_,harity,harityHead,hout,hhead,hindex,hindexHead,hsteps⟩ := support_run p.systematicBits p.auxiliaryBits p.clauseBits
    r.arity (rows.take i.val) rows[i.val] ((rows.drop (i.val+1)).flatten++clauseTail r p) hw hrow
  have hsource : headerBits p++(rows.take i.val).flatten++rows[i.val]++
      ((rows.drop (i.val+1)).flatten++clauseTail r p)=pcppOutput r p := by
    rw [output_word]
    rw [← hs]
    simp only [rows,List.append_assoc]
  change runFrom machine (budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity (rows.take i.val).length)
    (entry (headerBits p++(rows.take i.val).flatten++rows[i.val]++
      ((rows.drop (i.val+1)).flatten++clauseTail r p)) r.arity (rows.take i.val).length)=some base at hb
  have hlen : (rows.take i.val).length=i.val := by simp [List.length_take,Nat.min_eq_left hi.le]
  rw [hsource,hlen] at hb
  rw [hlen] at hsteps hindex
  change base.final.tapes 0=headerBits p++(rows.take i.val).flatten++rows[i.val]++
    ((rows.drop (i.val+1)).flatten++clauseTail r p) at hsource0
  rw [hsource] at hsource0
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config machine (capacity i.val) _ _ base hb
  rw [ready_eq] at ha
  refine ⟨actual,ha,has.trans hsteps,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [haf]
    simpa [ZeroPadding.config,capacity,hm] using hout
  · rw [haf]
    exact hhead

  · rw [haf]
    simpa only [ZeroPadding.config,capacity,show (0 : Fin 6) ≠ 5 by decide,if_false,ZeroPadding.pad_zero] using hsource0
  · rw [haf]
    simpa only [ZeroPadding.config,capacity,show (3 : Fin 6) ≠ 5 by decide,if_false,ZeroPadding.pad_zero] using harity
  · rw [haf]
    exact harityHead
  · rw [haf]
    change ZeroPadding.pad (i.val+2) (base.final.tapes 5)=UnaryTemplate.tape i.val
    rw [hindex,template_pad]
  · rw [haf]
    exact hindexHead

end NearCubicWires.RepairOrdinary.PCPPQuerySupport
