import Std.Tactic

/-! Holub's tuple (1,0,0,1): `XYYYX = UVVVU` with `|X|,|Y| ≤ |V|` forces periodicity. -/

namespace Holub1001
variable {α : Type}
abbrev Word (α : Type) := List α
def Comm (p q : Word α) := p ++ q = q ++ p
def pow (p : Word α) : Nat → Word α
  | 0 => []
  | n+1 => p ++ pow p n

def PairwiseComm (x y u v : Word α) :=
  Comm x y ∧ Comm x u ∧ Comm x v ∧ Comm y u ∧ Comm y v ∧ Comm u v

private theorem splitLong {a b c d : Word α} (h : a ++ c = b ++ d)
    (le : b.length ≤ a.length) : ∃ z, a = b ++ z ∧ d = z ++ c := by
  have pref : b <+: a := List.prefix_of_prefix_length_le
    (by rw [h]; exact List.prefix_append ..) (List.prefix_append a c) le
  obtain ⟨z,hz⟩ := pref
  exact ⟨z,hz.symm,by simpa [← hz,List.append_assoc] using h.symm⟩

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

/-! ## Lemma C: `K·BDB = DBD·K` with `|B| = |D| > 0` forces `B = D`. -/

private theorem lemCLt (p q B D : Word α) (hl : B.length = D.length)
    (hp : 0 < p.length) (hr : p.length < B.length)
    (h1 : p ++ q = D ++ B ++ D) (h2 : q ++ p = B ++ D ++ B) : B = D := by
  obtain ⟨L, hD, hq⟩ := splitLong (a:=D) (b:=p) (c:=B ++ D) (d:=q)
    (by simpa only [List.append_assoc] using h1.symm) (by omega)
  have lD := congrArg List.length hD
  simp only [List.length_append] at lD
  have hLs : L.length + p.length = B.length := by omega
  subst hq; subst hD
  have hB : L ++ p = B := List.append_inj_right' (s₁ := L ++ B ++ p) (s₂ := B ++ p ++ L)
    (by simpa only [List.append_assoc] using h2) (by simp only [List.length_append]; omega)
  subst hB
  simp only [List.append_assoc] at h2
  have c1 := List.append_cancel_left h2
  have c2 : (L ++ (p ++ (p ++ L))) ++ p = (p ++ (p ++ (L ++ L))) ++ p := by
    simpa only [List.append_assoc] using c1
  have key := List.append_cancel_right c2
  obtain ⟨z, hz1, hz2⟩ := splitLong (a:=L ++ p) (b:=p) (c:=p ++ L) (d:=p ++ L ++ L)
    (by simpa only [List.append_assoc] using key) (by simp only [List.length_append]; omega)
  have hz3 : p ++ L = z ++ p := List.append_cancel_right
    (by simpa only [List.append_assoc] using hz2 : (p ++ L) ++ L = (z ++ p) ++ L)
  have hcz : Comm (p ++ p) z := by
    show (p ++ p) ++ z = z ++ (p ++ p)
    calc (p ++ p) ++ z = p ++ (p ++ z) := List.append_assoc ..
      _ = p ++ (L ++ p) := by rw [hz1]
      _ = (p ++ L) ++ p := (List.append_assoc ..).symm
      _ = (z ++ p) ++ p := by rw [hz3]
      _ = z ++ (p ++ p) := List.append_assoc ..
  have hpz : Comm p z := central (h := p ++ p) (by simp only [List.length_append]; omega)
    (show (p ++ p) ++ p = p ++ (p ++ p) by simp only [List.append_assoc]) hcz
  have hLz : L = z := List.append_cancel_left (hz3.trans hpz.symm)
  rw [hz1, hLz]

private theorem lemCMid (p q B D : Word α) (hl : B.length = D.length)
    (h4 : B.length < p.length) (h5 : p.length < 2*B.length)
    (h1 : p ++ q = D ++ B ++ D) (h2 : q ++ p = B ++ D ++ B) : B = D := by
  obtain ⟨e, hp, hBD⟩ := splitLong (a:=p) (b:=D) (c:=q) (d:=B ++ D)
    (by simpa only [List.append_assoc] using h1) (by omega)
  have lp := congrArg List.length hp
  simp only [List.length_append] at lp
  obtain ⟨f, hB, hq⟩ := splitLong (a:=B) (b:=e) (c:=D) (d:=q) hBD (by omega)
  have lB := congrArg List.length hB
  simp only [List.length_append] at lB
  obtain ⟨T, c, hD, hT⟩ : ∃ T c, D = T ++ c ∧ T.length = e.length :=
    ⟨D.take e.length, D.drop e.length, (List.take_append_drop _ _).symm,
      by simp only [List.length_take]; omega⟩
  have lD := congrArg List.length hD
  simp only [List.length_append] at lD
  have hf : f.length = c.length := by omega
  subst hp; subst hq; subst hB; subst hD
  have b1 : f ++ T = e ++ f := List.append_inj_left
    (t₁ := c ++ (T ++ (c ++ e))) (t₂ := T ++ (c ++ (e ++ f)))
    (by simpa only [List.append_assoc] using h2) (by simp only [List.length_append]; omega)
  have b3 : c ++ e = e ++ f := List.append_inj_right'
    (s₁ := f ++ T ++ c ++ T) (s₂ := e ++ f ++ T ++ c)
    (by simpa only [List.append_assoc] using h2) (by simp only [List.length_append]; omega)
  obtain ⟨hfc, hTe⟩ := List.append_inj (b1.trans b3.symm) hf
  rw [hfc, hTe]

private theorem lemCRot (p q B D : Word α) (hl : B.length = D.length) (hs : 0 < B.length)
    (hr3 : p.length < 3*B.length)
    (h1 : p ++ q = D ++ B ++ D) (h2 : q ++ p = B ++ D ++ B) : B = D := by
  have l1 := congrArg List.length h1
  simp only [List.length_append] at l1
  rcases Nat.lt_or_ge p.length 1 with h0 | h0
  · have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.nil_append, List.append_nil] at h1 h2
    rw [h1] at h2
    exact (List.append_inj_left (s₁ := D) (s₂ := B)
      (by simpa only [List.append_assoc] using h2) hl.symm).symm
  rcases Nat.lt_or_ge p.length B.length with h3 | h3
  · exact lemCLt p q B D hl (by omega) h3 h1 h2
  rcases Nat.lt_or_ge B.length p.length with h4 | h4
  · rcases Nat.lt_or_ge p.length (2*B.length) with h5 | h5
    · exact lemCMid p q B D hl h4 h5 h1 h2
    rcases Nat.lt_or_ge (2*B.length) p.length with h6 | h6
    · exact (lemCLt q p D B hl.symm (by omega) (by omega) h2 h1).symm
    · obtain ⟨hp, hq⟩ := List.append_inj (s₁ := p) (s₂ := D ++ B) (t₁ := q) (t₂ := D) h1
        (by simp only [List.length_append]; omega)
      rw [hp, hq] at h2
      exact (List.append_inj_left (s₁ := D) (s₂ := B)
        (by simpa only [List.append_assoc] using h2) hl.symm).symm
  · obtain ⟨hp, hq⟩ := List.append_inj (s₁ := p) (s₂ := D) (t₁ := q) (t₂ := B ++ D)
      (by simpa only [List.append_assoc] using h1) (by omega)
    subst hp; subst hq
    exact (List.append_cancel_left h2).symm

private theorem lemCSmall (K B D : Word α) (hl : B.length = D.length) (hs : 0 < B.length)
    (hK : K.length < 3*B.length)
    (h : K ++ (B ++ D ++ B) = D ++ B ++ D ++ K) : B = D := by
  obtain ⟨L, h1, h2⟩ := splitLong (a:=D ++ B ++ D) (b:=K) (c:=K) (d:=B ++ D ++ B) h.symm
    (by simp only [List.length_append]; omega)
  exact lemCRot K L B D hl hs hK h1.symm h2.symm

theorem lemC (K B D : Word α) (hl : B.length = D.length) (hs : 0 < B.length)
    (h : K ++ (B ++ D ++ B) = D ++ B ++ D ++ K) : B = D := by
  suffices key : ∀ n (K : Word α), K.length ≤ n →
      K ++ (B ++ D ++ B) = D ++ B ++ D ++ K → B = D from key _ K (Nat.le_refl _) h
  intro n
  induction n with
  | zero => intro K hK hK'; exact lemCSmall K B D hl hs (by omega) hK'
  | succ n ih =>
    intro K hK hK'
    by_cases big : 3*B.length ≤ K.length
    · obtain ⟨z, hz1, hz2⟩ := splitLong (a:=K) (b:=D ++ B ++ D) (c:=B ++ D ++ B) (d:=K) hK'
        (by simp only [List.length_append]; omega)
      have lz := congrArg List.length hz1
      simp only [List.length_append] at lz
      exact ih z (by omega) (hz2.symm.trans hz1)
    · exact lemCSmall K B D hl hs (by omega) hK'

/-! ## Periodicity tools (index form) -/

/-- `Z` occurring at offsets `0` and `|G|` gives period `|G|`. -/
private theorem occ (Z G T1 T2 : Word α) (h : Z ++ T1 = G ++ (Z ++ T2)) :
    ∀ i, i + G.length < Z.length → Z[i]? = Z[i + G.length]? := by
  intro i hi
  have hi' : i < Z.length := by omega
  have e1 : (Z ++ T1)[i + G.length]? = Z[i + G.length]? := List.getElem?_append_left hi
  have e2 : (G ++ (Z ++ T2))[i + G.length]? = Z[i]? := by
    rw [List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
      List.getElem?_append_left hi']
  rw [← e2, ← h, e1]

/-- Period `d` on all of `Z` and period `l` from position `l` on spread period `l` to the start. -/
private theorem spread (Z : Word α) (l d : Nat) (hd : 0 < d) (hlen : 2*l + d ≤ Z.length)
    (pd : ∀ i, i + d < Z.length → Z[i]? = Z[i+d]?)
    (pl : ∀ i, l ≤ i → i + l < Z.length → Z[i]? = Z[i+l]?) :
    ∀ i, i < l → Z[i]? = Z[i+l]? := by
  have key : ∀ n i, l + d ≤ i + n → i < l + d → Z[i]? = Z[i+l]? := by
    intro n
    induction n with
    | zero => intro i h1 h2; exfalso; omega
    | succ n ih =>
      intro i h1 h2
      by_cases hil : l ≤ i
      · exact pl i hil (by omega)
      · rw [pd i (by omega), ih (i+d) (by omega) (by omega),
          show i + d + l = i + l + d by omega, ← pd (i+l) (by omega)]
  intro i hi
  exact key (l + d) i (by omega) (by omega)

/-! ## Main theorem -/

theorem case1001 (x y u v : Word α) (hx : x.length ≤ v.length) (hy : y.length ≤ v.length)
    (eq : x ++ y ++ y ++ y ++ x = u ++ v ++ v ++ v ++ u) :
    (x = u ∧ y = v) ∨ PairwiseComm x y u v := by
  have lens := congrArg List.length eq
  simp only [List.length_append] at lens
  obtain ⟨s, hvs⟩ : ∃ s, v.length = y.length + 2*s := ⟨(v.length - y.length)/2, by omega⟩
  have hxs : x.length = u.length + 3*s := by omega
  by_cases s0 : s = 0
  · left
    have e : x ++ (y ++ (y ++ (y ++ x))) = u ++ (v ++ (v ++ (v ++ u))) := by
      simpa only [List.append_assoc] using eq
    have hxu : x = u := List.append_inj_left e (by omega)
    subst hxu
    have e2 := List.append_cancel_left e
    exact ⟨rfl, List.append_inj_left e2 (by omega)⟩
  right
  obtain ⟨A, hA, rA⟩ := splitLong (a:=x) (b:=u) (c:=y ++ y ++ y ++ x) (d:=v ++ v ++ v ++ u)
    (by simpa only [List.append_assoc] using eq) (by omega)
  have lA := congrArg List.length hA
  simp only [List.length_append] at lA
  obtain ⟨B, hB, rB⟩ := splitLong (a:=A ++ y) (b:=v) (c:=y ++ y ++ x) (d:=v ++ v ++ u)
    (by simpa only [List.append_assoc] using rA.symm) (by simp only [List.length_append]; omega)
  have lB := congrArg List.length hB
  simp only [List.length_append] at lB
  obtain ⟨D, hD, rD⟩ := splitLong (a:=v) (b:=B ++ y) (c:=v ++ u) (d:=y ++ x)
    (by simpa only [List.append_assoc] using rB) (by simp only [List.length_append]; omega)
  have lD := congrArg List.length hD
  simp only [List.length_append] at lD
  obtain ⟨E, hE, rE⟩ := splitLong (a:=D ++ v) (b:=y) (c:=u) (d:=x)
    (by simpa only [List.append_assoc] using rD.symm) (by simp only [List.length_append]; omega)
  have lE := congrArg List.length hE
  simp only [List.length_append] at lE
  have hAs : A.length = 3*s := by omega
  have hBs : B.length = s := by omega
  have hDs : D.length = s := by omega
  have hEs : E.length = 3*s := by omega
  have hus : u.length + s ≤ y.length := by omega
  have spos : 0 < s := by omega
  subst hA
  subst hD
  obtain ⟨A', hA', hAy⟩ := splitLong (a:=A) (b:=B) (c:=y) (d:=y ++ D ++ B)
    (by simpa only [List.append_assoc] using hB) (by omega)
  have hA's : A'.length = 2*s := by
    have := congrArg List.length hA'
    simp only [List.length_append] at this
    omega
  obtain ⟨E', hE1, hEE⟩ := splitLong (a:=D ++ B ++ y) (b:=y) (c:=D) (d:=E)
    (by simpa only [List.append_assoc] using hE) (by simp only [List.length_append]; omega)
  have hE's : E'.length = 2*s := by
    have := congrArg List.length hEE
    simp only [List.length_append] at this
    omega
  subst hA'
  subst hEE
  -- now: hAy : y ++ D ++ B = A' ++ y, hE1 : D ++ B ++ y = y ++ E',
  --      rE : u ++ (B ++ A') = E' ++ D ++ u
  have hcomm : D ++ B ++ y = y ++ (D ++ B) := by
    by_cases hy2 : 2*s ≤ y.length
    · obtain ⟨y2, hy2e, -⟩ := splitLong (a:=y) (b:=D ++ B) (c:=E') (d:=y) hE1.symm
        (by simp only [List.length_append]; omega)
      have t : A' ++ y = (D ++ B) ++ (y2 ++ (D ++ B)) := by
        calc A' ++ y = y ++ D ++ B := hAy.symm
          _ = (D ++ B ++ y2) ++ D ++ B := by rw [← hy2e]
          _ = (D ++ B) ++ (y2 ++ (D ++ B)) := by simp only [List.append_assoc]
      have hA'P : A' = D ++ B := List.append_inj_left t (by simp only [List.length_append]; omega)
      calc D ++ B ++ y = A' ++ y := by rw [hA'P]
        _ = y ++ D ++ B := hAy.symm
        _ = y ++ (D ++ B) := List.append_assoc ..
    · obtain ⟨R, hR, hE'R⟩ := splitLong (a:=D ++ B) (b:=y) (c:=y) (d:=E') hE1
        (by simp only [List.length_append]; omega)
      have lR := congrArg List.length hR
      simp only [List.length_append] at lR
      obtain ⟨Q, hQ, hQR⟩ := splitLong (a:=A') (b:=y) (c:=y) (d:=y ++ R)
        (by rw [← hR]; simpa only [List.append_assoc] using hAy.symm) (by omega)
      have lQ := congrArg List.length hQ
      simp only [List.length_append] at lQ
      obtain ⟨F, hF, hBF⟩ := splitLong (a:=y) (b:=D) (c:=R) (d:=B) hR.symm (by omega)
      have lF := congrArg List.length hF
      simp only [List.length_append] at lF
      have hW : (R ++ y) ++ (D ++ u) = (u ++ F) ++ ((R ++ y) ++ Q) := by
        have t := rE
        rw [hBF, hQ, hE'R] at t
        simpa only [List.append_assoc] using t.symm
      have hQRe : Q = R := by
        by_cases d0 : (u ++ F).length = 0
        · simp only [List.length_append] at d0
          have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
          have hF0 : F = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hu0; subst hF0
          simp only [List.nil_append, List.append_nil, List.append_assoc] at hW hF
          have hDQ : D = Q := List.append_cancel_left (List.append_cancel_left hW)
          rw [hF, ← hDQ] at hQR
          rw [← hDQ]
          exact (List.append_cancel_left hQR).symm
        · have pd := occ (R ++ y) (u ++ F) (D ++ u) Q hW
          have py := occ y Q R [] (by rw [List.append_nil]; exact hQR)
          have pl : ∀ i, R.length ≤ i → i + R.length < (R ++ y).length →
              (R ++ y)[i]? = (R ++ y)[i + R.length]? := by
            intro i h1 h2
            simp only [List.length_append] at h2
            rw [List.getElem?_append_right h1,
              List.getElem?_append_right (Nat.le_add_left R.length i), Nat.add_sub_cancel,
              py (i - R.length) (by omega), show i - R.length + Q.length = i by omega]
          have hsp := spread (R ++ y) R.length (u ++ F).length (by omega)
            (by simp only [List.length_append] at d0 ⊢; omega) pd pl
          apply List.ext_getElem?
          intro i
          by_cases hi : i < R.length
          · have hiy : i < y.length := by omega
            have hiQ : i < Q.length := by omega
            have e1 : (y ++ R)[i]? = (Q ++ y)[i]? := by rw [hQR]
            rw [List.getElem?_append_left hiy, List.getElem?_append_left hiQ] at e1
            have e2 := hsp i hi
            rw [List.getElem?_append_left hi,
              List.getElem?_append_right (Nat.le_add_left R.length i), Nat.add_sub_cancel] at e2
            rw [← e1, e2]
          · have hQn : Q[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
            have hRn : R[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
            rw [hQn, hRn]
      have hQR' := hQR
      rw [hQRe] at hQR'
      rw [hR, List.append_assoc, ← hQR']
  have hA'P : A' = D ++ B := List.append_cancel_right (by
    calc A' ++ y = y ++ D ++ B := hAy.symm
      _ = y ++ (D ++ B) := List.append_assoc ..
      _ = D ++ B ++ y := hcomm.symm)
  have hE'P : E' = D ++ B := (List.append_cancel_left (hcomm.symm.trans hE1)).symm
  subst hA'P; subst hE'P
  have hBD : B = D := lemC u B D (by omega) (by omega)
    (by simpa only [List.append_assoc] using rE)
  subst hBD
  have pos : 0 < B.length := by omega
  have hBB : Comm B B := rfl
  have hBy : Comm B y := central (h := B ++ B) (by simp only [List.length_append]; omega)
    (show (B ++ B) ++ B = B ++ (B ++ B) by simp only [List.append_assoc]) hcomm
  have hBu : Comm B u := central (h := B ++ B ++ B) (by simp only [List.length_append]; omega)
    (show (B ++ B ++ B) ++ B = B ++ (B ++ B ++ B) by simp only [List.append_assoc])
    (show (B ++ B ++ B) ++ u = u ++ (B ++ B ++ B) by simpa only [List.append_assoc] using rE.symm)
  have hBx : Comm B (u ++ (B ++ (B ++ B))) := commCat hBu (commCat hBB (commCat hBB hBB))
  have hBv : Comm B (B ++ y ++ B) := commCat (commCat hBB hBy) hBB
  exact ⟨central pos hBx hBy, central pos hBx hBu, central pos hBx hBv,
    central pos hBy hBu, central pos hBy hBv, central pos hBu hBv⟩

#print axioms case1001
end Holub1001
