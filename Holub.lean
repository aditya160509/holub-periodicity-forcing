import Std.Tactic

namespace Holub
variable {α : Type} 
abbrev Word (α : Type) := List α
def Comm (p q : Word α) := p ++ q = q ++ p
def pat (x y : Word α) := x ++ x ++ y ++ y ++ x ++ y ++ x
def pow (p : Word α) : Nat → Word α
  | 0 => []
  | n+1 => p ++ pow p n

private theorem splitLong {a b c d : Word α} (h : a ++ c = b ++ d)
    (le : b.length ≤ a.length) : ∃ z, a = b ++ z ∧ d = z ++ c := by
  have pref : b <+: a := List.prefix_of_prefix_length_le
    (by rw [h]; exact List.prefix_append ..) (List.prefix_append a c) le
  obtain ⟨z,hz⟩ := pref
  exact ⟨z,hz.symm,by simpa [← hz,List.append_assoc] using h.symm⟩

private theorem powMove (w z : Word α) (n : Nat) : pow (w++z) n ++ w = w ++ pow (z++w) n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simpa [pow,List.append_assoc] using congrArg (fun v => (w++z)++v) ih

private theorem transfer (p z q : Word α) (n : Nat)
    (h : pow p (n+1) ++ z = z ++ q) :
    ∃ k, p ++ z = z ++ k ∧ q = pow k (n+1) := by
  induction z generalizing p with
  | nil => exact ⟨p,by simp,by simpa using h.symm⟩
  | cons c z ih =>
    cases p with
    | nil =>
      have emp (m : Nat) : pow ([] : Word α) m = [] := by induction m <;> simp_all [pow]
      simp [emp] at h
      exact ⟨[],by simp,by simpa [emp] using h.symm⟩
    | cons b p =>
      have eq : b = c := (List.cons.inj (by simpa [pow,List.append_assoc] using h :
        b :: (p ++ (pow (b::p) n ++ c::z)) = c :: (z ++ q))).1
      subst b
      have tail := (List.cons.inj (by simpa [pow,List.append_assoc] using h :
        c :: (p ++ (pow (c::p) n ++ c::z)) = c :: (z ++ q))).2
      have mv := powMove [c] p n
      have mv' : pow (c::p) n ++ c::z = c :: (pow (p++[c]) n ++ z) := by
        simpa [List.append_assoc] using congrArg (fun s => s++z) mv
      rw [mv'] at tail
      obtain ⟨k,hk,hq⟩ := ih (p++[c]) (by simpa [pow,List.append_assoc] using tail)
      exact ⟨k,by simpa [List.append_assoc] using congrArg (List.cons c) hk,hq⟩

private theorem lenpow (p : Word α) (n : Nat) : (pow p n).length = n*p.length := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,ih,Nat.succ_mul,Nat.add_comm]

private theorem commCat {h p q : Word α} (a : Comm h p) (b : Comm h q) : Comm h (p++q) := by
  unfold Comm at *
  calc h ++ (p ++ q) = (h ++ p) ++ q := (List.append_assoc ..).symm
       _ = p ++ (h ++ q) := by rw [a,List.append_assoc]
       _ = _ := by rw [b,List.append_assoc]

private theorem central {h p q : Word α} (hn : 0 < h.length) (a : Comm h p) (b : Comm h q) :
    Comm p q := by
  let n := p.length+q.length
  have large : n ≤ (pow h n).length := by
    rw [lenpow]; exact Nat.le_mul_of_pos_right _ hn
  have pref (z : Word α) (cz : Comm h z) (sz : z.length = n) : z <+: pow h n := by
    have cp (m : Nat) : Comm z (pow h m) := by
      induction m with
      | zero => simp [pow,Comm]
      | succ m ih => exact commCat (Eq.symm cz) ih
    have eq := cp n
    exact List.prefix_of_prefix_length_le
      (show z <+: z ++ pow h n from List.prefix_append ..)
      (by rw [eq]; exact List.prefix_append ..) (by omega)
  exact List.IsPrefix.eq_of_length (List.prefix_of_prefix_length_le
    (pref _ (commCat a b) (by simp [n]))
    (pref _ (commCat b a) (by simp [n,Nat.add_comm])) (by simp [Nat.add_comm])) (by simp [Nat.add_comm])

def PairwiseComm (x y u v : Word α) :=
  Comm x y ∧ Comm x u ∧ Comm x v ∧ Comm y u ∧ Comm y v ∧ Comm u v

private theorem ordered (x y u v : Word α) (hy : y.length ≤ v.length)
    (eq : pat x y = pat u v) : (x = u ∧ y = v) ∨ PairwiseComm x y u v := by
  have lens := congrArg List.length eq
  simp only [pat,List.length_append] at lens
  let t := (v.length-y.length)/4
  have hx : x.length = u.length + 3*t := by dsimp [t]; omega
  have hv : v.length = y.length + 4*t := by dsimp [t]; omega
  by_cases zero : t = 0
  · have xu := List.append_inj_left (by simpa only [pat,List.append_assoc] using eq :
        x ++ (x ++ (y ++ (y ++ (x ++ (y ++ x))))) = u ++ (u ++ (v ++ (v ++ (u ++ (v ++ u)))))) (by omega)
    subst u
    simp [pat,List.append_assoc] at eq
    exact Or.inl ⟨rfl,List.append_inj_left eq (by omega)⟩
  right
  obtain ⟨A,hA,restA⟩ := splitLong (a:=(x)) (b:=(u)) (c:=(x ++ y ++ y ++ x ++ y ++ x)) (d:=(u ++ v ++ v ++ u ++ v ++ u))
    (by simpa only [pat,List.append_assoc] using eq) (by omega)
  have lA := congrArg List.length hA
  simp only [List.length_append] at lA
  obtain ⟨B,hB,restB⟩ := splitLong (a:=(A ++ x)) (b:=(u)) (c:=(y ++ y ++ x ++ y ++ x)) (d:=(v ++ v ++ u ++ v ++ u))
    (by simpa only [pat,List.append_assoc] using restA.symm) (by simp_all only [List.length_append] <;> omega)
  have lB := congrArg List.length hB
  simp only [List.length_append] at lB
  obtain ⟨C,hC,restC⟩ := splitLong (a:=(B ++ y)) (b:=(v)) (c:=(y ++ x ++ y ++ x)) (d:=(v ++ u ++ v ++ u))
    (by simpa only [pat,List.append_assoc] using restB.symm) (by simp_all only [List.length_append] <;> omega)
  have lC := congrArg List.length hC
  simp only [List.length_append] at lC
  obtain ⟨D,hD,restD⟩ := splitLong (a:=(v)) (b:=(C ++ y)) (c:=(u ++ v ++ u)) (d:=(x ++ y ++ x))
    (by simpa only [pat,List.append_assoc] using restC) (by simp_all only [List.length_append] <;> omega)
  have lD := congrArg List.length hD
  simp only [List.length_append] at lD
  obtain ⟨E,hE,restE⟩ := splitLong (a:=(x)) (b:=(D ++ u)) (c:=(y ++ x)) (d:=(v ++ u))
    (by simpa only [pat,List.append_assoc] using restD) (by simp_all only [List.length_append] <;> omega)
  have lE := congrArg List.length hE
  simp only [List.length_append] at lE
  obtain ⟨F,hF,restF⟩ := splitLong (a:=(v)) (b:=(E ++ y)) (c:=(u)) (d:=(x))
    (by simpa only [pat,List.append_assoc] using restE) (by simp_all only [List.length_append] <;> omega)
  have lF := congrArg List.length hF
  simp only [List.length_append] at lF
  obtain ⟨G,cEG,tail⟩ := splitLong (a:=C) (b:=E) (c:=y++D) (d:=y++F)
    (by simpa only [List.append_assoc] using hD.symm.trans hF) (by omega)
  let H := F.take t
  have lH : H.length = t := by simp [H]; omega
  have fd : F.drop t = D := by
    apply List.append_inj_right' (s₁:=y++H) (s₂:=G++y)
    · simpa [H,List.append_assoc] using tail
    · simp; omega
  have fHD : F = H ++ D := by rw [← fd]; exact (List.take_append_drop ..).symm
  have gy : G ++ y = y ++ H := by
    apply List.append_cancel_right (bs:=D)
    simpa only [fHD,List.append_assoc] using tail.symm
  have dcomp : D ++ (u++E) = H ++ (D++u) := by
    simpa only [fHD,List.append_assoc] using hE.symm.trans restF
  obtain ⟨J,dHJ,rem⟩ := splitLong dcomp (by omega)
  have lj := congrArg List.length dHJ
  simp only [List.length_append] at lj
  have jh : H = J := List.append_inj_left
    (show H ++ (J++u) = J ++ (u++E) by simpa only [dHJ,List.append_assoc] using rem) (by omega)
  subst J
  have hu : H ++ u = u ++ E := by simpa [dHJ,List.append_assoc] using rem
  have aE : A = E ++ E ++ E := by
    have same := hA.symm.trans restF
    have shift : (H ++ H ++ H) ++ u = u ++ (E ++ E ++ E) := by
      simp only [List.append_assoc]
      rw [hu,← List.append_assoc H u,hu,List.append_assoc u E,← List.append_assoc H u,hu]
      simp [List.append_assoc]
    have same' : u ++ A = u ++ (E ++ E ++ E) := by
      simpa only [fHD,dHJ,List.append_assoc] using same.trans
        (show F ++ u = u ++ (E ++ E ++ E) by simpa only [fHD,dHJ,List.append_assoc] using shift)
    exact List.append_cancel_left same'
  let B₀ := B.take (3*t)
  have lB₀ : B₀.length = 3*t := by simp [B₀]; omega
  have bA : B.drop (3*t) = A := by
    apply List.append_inj_right' (s₁:=u++B₀) (s₂:=A++u)
    · simpa [B₀,List.append_assoc,hA] using hB.symm
    · simp; omega
  have bform : B = B₀ ++ A := by rw [← bA]; exact (List.take_append_drop ..).symm
  have e3u : pow E (2+1) ++ u = u ++ B₀ := by
    have eq' : (A++u)++A = (u++B₀)++A := by simpa only [hA,bform,List.append_assoc] using hB
    simpa [pow,aE,List.append_assoc] using List.append_cancel_right eq'
  obtain ⟨K,eku,bk⟩ := transfer _ _ _ _ e3u
  have lk := congrArg List.length eku
  simp only [List.length_append] at lk
  have ke : K = E := List.append_inj_left
    (show K ++ (K ++ (K ++ (A++y))) = E ++ (y ++ (F++C)) by
      simpa [bform,bk,hF,pow,List.append_assoc] using hC) (by omega)
  subst K
  have he : H = E := List.append_cancel_right (bs:=u) (hu.trans eku.symm)
  subst E
  have hU : Comm H u := eku
  have five : pow H (4+1) ++ y = y ++ (H++H++H++H++G) := by
    simpa [bform,bk,aE,cEG,hF,fHD,dHJ,pow,List.append_assoc] using hC
  obtain ⟨L,hyl,hL⟩ := transfer _ _ _ _ five
  have ll := congrArg List.length hyl
  simp only [List.length_append] at ll
  have hl : H = L := List.append_inj_left (show H ++ (H++(H++(H++G))) =
      L ++ (L++(L++(L++L))) by simpa [pow,List.append_assoc] using hL) (by omega)
  subst L
  have hY : Comm H y := hyl
  have hh : Comm H H := rfl
  have hX : Comm H x := by rw [hA,aE]; exact commCat hU (commCat (commCat hh hh) hh)
  have hV : Comm H v := by rw [hF,fHD,dHJ]; exact commCat (commCat hh hY) (commCat hh (commCat hh hh))
  have pos : 0 < H.length := by omega
  exact ⟨central pos hX hY,central pos hX hU,central pos hX hV,
    central pos hY hU,central pos hY hV,central pos hU hV⟩

/-- Periodicity forcing over every alphabet, including erasing substitutions. -/
theorem forcing (x y u v : Word α) (eq : pat x y = pat u v) :
    PairwiseComm x y u v ∨ (x = u ∧ y = v) := by
  rcases Nat.le_total y.length v.length with le|le
  · exact (ordered x y u v le eq).symm
  · rcases ordered u v x y le eq.symm with ⟨h,k⟩|⟨a,b,c,d,e,f⟩
    · exact Or.inr ⟨h.symm,k.symm⟩
    · exact Or.inl ⟨f,b.symm,d.symm,c.symm,e.symm,a⟩

/-- The conference statement with its three length inequalities. -/
theorem words2025 (x y u v : Word α)
    (_ : x.length ≤ v.length) (_ : y.length ≤ v.length) (_ : u.length ≤ v.length)
    (h : x++x++y++y++x++y++x = u++u++v++v++u++v++u) :
    PairwiseComm x y u v ∨ (x = u ∧ y = v) := forcing x y u v h

#print axioms forcing
#print axioms words2025
end Holub
