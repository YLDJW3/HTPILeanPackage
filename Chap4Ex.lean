import HTPILib.Chap4
namespace HTPI.Exercises

/- Section 4.2 -/
-- 1.
theorem Exercise_4_2_9a {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Dom (comp S R) ⊆ Dom R := by
    define; fix a; assume h
    define at h; obtain c hc from h; clear h
    define at hc; obtain b hb from hc; clear hc
    define; exists b; apply hb.left
    done

-- 2.
theorem Exercise_4_2_9b {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Ran R ⊆ Dom S → Dom (comp S R) = Dom R := by
    assume h; apply Set.ext; fix a; apply Iff.intro
    ·   assume ha; define at ha; obtain c hc from ha; clear ha
        define at hc; obtain b hb from hc; clear hc
        define; exists b; apply hb.left
    ·   assume ha; define at ha; obtain b hb from ha; clear ha
        have h1: b ∈ Ran R := by
            define; exists a
            done
        define at h; have h2 := by apply h h1
        define at h2; obtain c hc from h2; clear h2
        define; exists c; define; exists b
    done

-- 3.
--Fill in the blank to get a correct theorem and then prove the theorem
theorem Exercise_4_2_9c {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Dom S ⊆ Ran R → Ran (comp S R) = Ran S := by
    assume h; define at h
    apply Set.ext; fix c; apply Iff.intro
    ·   assume hc; define at hc; obtain a ha from hc; clear hc
        define at ha; obtain b hb from ha; clear ha
        define; exists b; exact hb.right
    ·   assume hc; define at hc; obtain b hb from hc; clear hc
        have h1: b ∈ Dom S := by
            define; exists c
            done
        have h2 := by apply h h1
        define at h2; obtain a ha from h2; clear h2
        define; exists a; define; exists b
    done

-- 4.
theorem Exercise_4_2_12a {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    (comp S R) \ (comp T R) ⊆ comp (S \ T) R := by
    define; fix (a, c); assume h
    define at h; have h1 := h.left; have h2 := h.right; clear h
    define at h1; obtain b hb from h1; clear h1
    define; exists b; apply And.intro hb.left _
    define; apply And.intro hb.right _
    define at h2; quant_neg at h2
    by_contra h
    contradict h2; quant_neg; exists b
    apply And.intro hb.left h
    done

-- 5.
--You won't be able to complete this proof
theorem Exercise_4_2_12b {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S \ T) R ⊆ (comp S R) \ (comp T R) := by
    define; fix (a, c); assume h
    define at h; obtain b hb from h; clear h
    have h1 := hb.left; have h2 := hb.right; define at h2; clear hb
    define; apply And.intro
    · define; exists b; apply And.intro h1 h2.left
    · define; quant_neg; fix x; demorgan; sorry
    -- to prove (a, c) ∉ T ∘ R, we have to prove ∀x ∈ B, ¬(aRx ∧ xTc)
    -- what we only have is there exists b ∈ B,¬(aRb ∧ bTc)

-- 6.
--You might not be able to complete this proof
theorem Exercise_4_2_14c {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∩ T) R = (comp S R) ∩ (comp T R) := by
    apply Set.ext; fix (a, c); apply Iff.intro
    ·   assume h; define at h; obtain b hb from h; clear h
        have h1 := hb.left; have h2 := hb.right; define at h2; clear hb
        define; apply And.intro
        ·   define; exists b; apply And.intro h1 h2.left
        ·   define; exists b; apply And.intro h1 h2.right
    ·   assume h; define at h; have h1 := h.left; have h2 := h.right; clear h
        define at h1; obtain b hb from h1; clear h1
        define at h2; obtain b' hb' from h2; clear h2
        define; sorry

-- 7.
--You might not be able to complete this proof
theorem Exercise_4_2_14d {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∪ T) R = (comp S R) ∪ (comp T R) := by
    apply Set.ext; fix (a, c); apply Iff.intro
    ·   assume h; define at h; obtain b hb from h; clear h
        have h1 := hb.right; define at h1
        have h2 := hb.left; clear hb
        define; by_cases on h1
        · apply Or.inl; define; exists b
        · apply Or.inr; define; exists b
    ·   assume h; define at h; by_cases on h
        ·   define at h; obtain b hb from h; clear h
            define; exists b; apply And.intro hb.left _
            define; apply Or.inl hb.right
        ·   define at h; obtain b hb from h; clear h
            define; exists b; apply And.intro hb.left _
            define; apply Or.inr hb.right
    done

/- Section 4.3 -/
-- 1.
example :
    elementhood Int 6 {n : Int | ∃ (k : Int), n = 2 * k} := by
    define; exists 3
    done

-- 2.
theorem Theorem_4_3_4_1 {A : Type} (R : BinRel A) :
    reflexive R ↔ {(x, y) : A × A | x = y} ⊆ extension R := by
    apply Iff.intro
    ·   assume h; define at h
        define; fix (a, b); assume h1; define at h1
        define; rw [h1]; apply h
    ·   assume h; define at h
        define; fix x
        have h1 : (x, x) ∈ extension R := by
            apply h; define; rfl
        define at h1; apply h1
    done

-- 3.
theorem Theorem_4_3_4_3 {A : Type} (R : BinRel A) :
    transitive R ↔
      comp (extension R) (extension R) ⊆ extension R := by
    apply Iff.intro
    ·   assume h; define at h
        define; fix (a, b); assume h1
        define at h1; obtain c hc from h1; clear h1
        have h1 := hc.left; have h2 := hc.right; clear hc
        define at h1; define at h2; define
        have h3 := by apply h a c b h1 h2
        apply h3
    ·   assume h; define at h
        define; fix x; fix y; fix z
        assume hxy; assume hyz
        rw [←ext_def R] at hxy;
        rw [←ext_def R] at hyz;
        rw [←ext_def R]; apply h; define
        exists y
    done

-- 4.
theorem Exercise_4_3_12a {A : Type} (R : BinRel A) (h1 : reflexive R) :
    reflexive (RelFromExt (inv (extension R))) := by
    define; fix x; define; define at h1; apply h1
    done

-- 5.
theorem Exercise_4_3_12c {A : Type} (R : BinRel A) (h1 : transitive R) :
    transitive (RelFromExt (inv (extension R))) := by
    define; fix x; fix y; fix z
    assume hxy; define at hxy
    assume hyz; define at hyz
    define; define at h1
    apply h1 z y x hyz hxy
    done

-- 6.
theorem Exercise_4_3_18 {A : Type}
    (R S : BinRel A) (h1 : transitive R) (h2 : transitive S)
    (h3 : comp (extension S) (extension R) ⊆
      comp (extension R) (extension S)) :
    transitive (RelFromExt (comp (extension R) (extension S))) := by
    define at h1; define at h2
    define; fix x; fix y; fix z; assume hxy; assume hyz
    rw [RelFromExt_def]
    define at h3
    rw [RelFromExt_def] at hxy; define at hxy; obtain a ha from hxy; clear hxy
    rw [RelFromExt_def] at hyz; define at hyz; obtain b hb from hyz; clear hyz
    have h4 : (a, b) ∈ comp (extension S) (extension R) := by
        define; exists y; apply And.intro ha.right hb.left
        done
    apply h3 at h4; define at h4; obtain c hc from h4; clear h4; clear h3
    define; exists c
    have hxa := ha.left; rw [ext_def S] at hxa
    have hac := hc.left; rw [ext_def S] at hac
    have hxc := by apply h2 x a c hxa hac
    clear hxa; clear hac
    have hcb := hc.right; rw[ext_def R] at hcb
    have hbz := hb.right; rw[ext_def R] at hbz
    have hcz := by apply h1 c b z hcb hbz
    clear hcb; clear hbz
    apply And.intro hxc hcz
    done

-- 7.
theorem Exercise_4_3_20 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ X ≠ ∅ ∧ Y ≠ ∅ ∧
    ∀ (x y : A), x ∈ X → y ∈ Y → R x y) :
    transitive R → transitive S := by
    assume h1; define at h1
    define; fix X; fix Y; fix Z; assume hxy; assume hyz
    rewrite [h] at hxy
    rewrite [h] at hyz
    rw [h]; apply And.intro hxy.left _
    apply And.intro hyz.right.left
    fix x; fix z; assume hx; assume hz
    have h3 : ∃y: A, y ∈ Y := by
        rcases Set.nonempty_iff_ne_empty.mpr hyz.left with ⟨y, hy⟩
        exists y
        done
    have h2 : ∀y ∈ Y, R x y ∧ R y z := by
        fix y; assume hy; apply And.intro
        ·   apply hxy.right.right; apply hx; apply hy
        ·   apply hyz.right.right; apply hy; apply hz
        done
    obtain y hy from h3
    apply h2 at hy
    apply h1 x y z
    apply hy.left; apply hy.right
    done


-- 8.
--You might not be able to complete this proof
theorem Exercise_4_3_13b {A : Type}
    (R1 R2 : BinRel A) (h1 : symmetric R1) (h2 : symmetric R2) :
    symmetric (RelFromExt ((extension R1) ∪ (extension R2))) := by
    define; fix x; fix y
    assume h; define at h; define
    by_cases on h
    ·   define at h; define at h1; apply h1 at h
        apply Or.inl; define; apply h
    ·   define at h; define at h2; apply h2 at h
        apply Or.inr; define; apply h
    done

-- 9.
--You might not be able to complete this proof
theorem Exercise_4_3_13c {A : Type}
    (R1 R2 : BinRel A) (h1 : transitive R1) (h2 : transitive R2) :
    transitive (RelFromExt ((extension R1) ∪ (extension R2))) := by
    define; fix x; fix y; fix z
    assume hxy; assume hyz
    define at hxy; define at hyz
    sorry

-- 10.
--You might not be able to complete this proof
theorem Exercise_4_3_19 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ ∃ (x y : A), x ∈ X ∧ y ∈ Y ∧ R x y) :
    transitive R → transitive S := by
    assume hR; define at hR
    define; fix X; fix Y; fix Z; assume hxy; assume hyz
    rw [h] at hxy; obtain x hx from hxy; obtain y hxy' from hx; clear hx; clear hxy
    rw [h] at hyz; obtain y' hy from hyz; obtain z hyz' from hy; clear hy; clear hyz
    rw [h]
    sorry

/- Section 4.4 -/
-- 1.
theorem Example_4_4_3_1 {A : Type} : partial_order (sub A) := by
    define; apply And.intro
    ·   -- reflexive
        define; fix X; define; fix a; assume h; exact h
    ·   apply And.intro
        ·   -- transitive
            define; fix X; fix Y; fix Z; assume hXY; assume hYZ
            define; fix a; assume hx
            define at hXY; apply hXY at hx; clear hXY
            define at hYZ; apply hYZ at hx; clear hYZ
            apply hx
        ·   -- antisymmetric
            define; fix X; fix Y; assume hXY; assume hYX
            define at hXY
            define at hYX
            apply Set.ext; fix a
            apply Iff.intro
            ·   assume h; apply hXY; exact h
            ·   assume h; apply hYX; exact h
    done

-- 2.
theorem Theorem_4_4_6_1 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    ∀ (c : A), smallestElt R c B → b = c := by
    fix a; define at h2
    assume h; define at h
    have ha := h.left; apply h2.right at ha
    have hb := h2.left; apply h.right at hb
    clear h; clear h2
    define at h1; have h2 := h1.right.right; define at h2
    apply h2; apply ha; apply hb
    done

-- 3.
--If F is a set of sets, then ⋃₀ F is the lub of F in the subset ordering
theorem Theorem_4_4_11 {A : Type} (F : Set (Set A)) :
    lub (sub A) (⋃₀ F) F := by
    define; apply And.intro
    ·   define; fix X; assume h; define; fix x; assume hx
        define; exists X
    ·   fix X; assume h; define at h
        define; fix x; assume h1; define at h1
        obtain Y h2 from h1; clear h1
        have h1 := h2.left; apply h at h1; define at h1
        apply h1; exact h2.right
    done

-- 4.
theorem Exercise_4_4_8 {A B : Type} (R : BinRel A) (S : BinRel B)
    (T : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      T (a, b) (a', b') ↔ R a a' ∧ S b b') :
    partial_order T := by
    define at h1; define at h2
    define; apply And.intro
    ·   --reflexivity
        define; fix (a, b); rw [h3]
        have h1' := h1.left; define at h1'
        have h2' := h2.left; define at h2'
        apply And.intro
        apply h1'; apply h2'
    ·   apply And.intro
        ·   --transitivity
            define; fix Px; fix Py; fix Pz
            assume hxy; assume hyz
            rw [h3]
            rw [h3] at hxy; rw [h3] at hyz
            have h1' := h1.right.left; define at h1'
            have h2' := h2.right.left; define at h2'
            apply And.intro
            ·   apply h1' Px.1 Py.1 Pz.1
                apply hxy.left; apply hyz.left
            ·   apply h2' Px.2 Py.2 Pz.2
                apply hxy.right; apply hyz.right
        ·   -- antisymmetric
            define; fix (x1, x2); fix (y1, y2)
            assume Pxy; assume Pyx
            have h1' := h1.right.right; define at h1'
            have h2' := h2.right.right; define at h2'
            rw [h3] at Pxy; rw [h3] at Pyx
            have hxy1 : x1 = y1 := by
                apply h1' x1 y1 Pxy.left Pyx.left
                done
            have hxy2 : x2 = y2 := by
                apply h2' x2 y2 Pxy.right Pyx.right
                done
            rw [hxy1, hxy2]
    done

-- 5.
theorem Exercise_4_4_9_part {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : total_order R) (h2 : total_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ∨ L (a', b') (a, b) := by
      fix a; fix a'; fix b; fix b'
      define at h1; define at h2
      have hr := h1.right; have hs := h2.right
      have hpr := h1.left; define at hpr; clear h1
      have hps := h2.left; define at hps; clear h2
      have h4 := by apply hr a a'
      have h5 := by apply hs b b'
      by_cases h : a = a'
      · -- a = a'
        rw [←h]
        by_cases on h5
        · apply Or.inl; rw [h3]; apply And.intro
          apply hpr.left
          assume ha; apply h5
        · apply Or.inr; rw [h3]; apply And.intro
          apply hpr.left
          assume ha; apply h5
      · -- a ≠ a'
        by_cases on h4
        · apply Or.inl; rw [h3]; apply And.intro h4
          assume ha; contradict h; apply ha
        · apply Or.inr; rw [h3]; apply And.intro h4
          assume ha; contradict h; rw [ha]
      done

-- 6.
theorem Exercise_4_4_15a {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    smallestElt R1 b B → smallestElt R2 b B := by
    assume h; define at h
    define; apply And.intro h.left _; fix x
    assume hx
    have h4 := by apply h.right x hx
    define at h3
    have h5 : (b, x) ∈ extension R1 := by
        define; exact h4
        done
    clear h4
    apply h3 at h5; define at h5; exact h5
    done

-- 7.
theorem Exercise_4_4_15b {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    minimalElt R2 b B → minimalElt R1 b B := by
    assume h; define at h
    have h4 := h.right; quant_neg at h4
    have h5 := h.left; clear h
    define; apply And.intro h5
    by_contra h; obtain x hx from h; clear h
    define at h3
    have h6 : (x, b) ∈ extension R1 := by
        define; apply hx.right.left
        done
    apply h3 at h6; define at h6
    contradict h4; quant_neg; exists x
    apply And.intro hx.left
    apply And.intro h6 hx.right.right
    done

-- 8.
theorem Exercise_4_4_18a {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (h1 : partial_order R)
    (h2 : ∀ x ∈ B1, ∃ y ∈ B2, R x y) (h3 : ∀ x ∈ B2, ∃ y ∈ B1, R x y) :
    ∀ (x : A), upperBd R x B1 ↔ upperBd R x B2 := by
    fix x; apply Iff.intro
    ·   assume h; define at h
        define; fix y; assume hy
        apply h3 at hy; obtain z hz from hy; clear hy
        have h4 := hz.left; apply h at h4; clear h
        define at h1; have ht := h1.right.left; define at ht
        have h := by apply ht y z x hz.right h4
        apply h
    ·   assume h; define at h
        define; fix y; assume hy
        apply h2 at hy; obtain z hz from hy; clear hy
        have h4 := hz.left; apply h at h4; clear h
        define at h1; have ht := h1.right.left; define at ht
        have h := by apply ht y z x hz.right h4
        apply h
    done

-- 9.
theorem Exercise_4_4_22 {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (x1 x2 : A)
    (h1 : partial_order R) (h2 : lub R x1 B1) (h3 : lub R x2 B2) :
    B1 ⊆ B2 → R x1 x2 := by
    assume h; define at h
    define at h2; have h2l := h2.left; define at h2l
    define at h3; have h3l := h3.left; define at h3l
    have h2r := h2.right; clear h2
    have h3r := h3.right; clear h3
    have h4 : ∀ x ∈ B1, R x x2 := by
        fix x; assume hx; apply h at hx
        apply h3l at hx; exact hx
        done
    apply h2r; define; apply h4
    done

-- 10.
theorem Exercise_4_4_24 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (R ∪ (inv R))
    {T : Set (A × A) | R ⊆ T ∧ symmetric (RelFromExt T)} := by
    define; apply And.intro
    ·   --left
        define; apply And.intro
        ·   define; fix a; assume ha
            define; apply Or.inl ha
        ·   define; fix x; fix y; assume h
            define; define at h
            by_cases on h
            ·   apply Or.inr; define; apply h
            ·   apply Or.inl; define at h; exact h
    ·   -- right
        fix x; assume h; define at h
        define; fix (a, b); assume ha; define at ha
        by_cases on ha
        ·   have hl := h.left; define at hl; apply hl; apply ha
        ·   have hr := h.right; define at hr; define at ha
            have h1 : RelFromExt x b a := by
                define; have hl := h.left; define at hl
                apply hl; exact ha
                done
            have h2 := by apply hr b a h1
            define at h2; exact h2
    done


/- Section 4.5 -/
-- 1.
lemma overlap_implies_equal {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := sorry

-- 2.
lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F) :
    reflexive (EqRelFromPart F) := sorry

-- 3.
lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F) :
    symmetric (EqRelFromPart F) := sorry

-- 4.
lemma Lemma_4_5_7_trans {A : Type} (F : Set (Set A)) (h : partition F) :
    transitive (EqRelFromPart F) := sorry

-- 5.
lemma Lemma_4_5_8 {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := sorry

-- 6.
lemma elt_mod_equiv_class_of_elt
    {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ∀ x ∈ X, equivClass R x = X := sorry

-- Definitions for next three exercises:
def dot {A : Type} (F G : Set (Set A)) : Set (Set A) :=
    {Z : Set A | ¬empty Z ∧ ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y}

def conj {A : Type} (R S : BinRel A) (x y : A) : Prop :=
    R x y ∧ S x y

-- 7.
theorem Exercise_4_5_20a {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    equiv_rel (conj R S) := sorry

-- 8.
theorem Exercise_4_5_20b {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    ∀ (x : A), equivClass (conj R S) x =
      equivClass R x ∩ equivClass S x := sorry

-- 9.
theorem Exercise_4_5_20c {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    mod A (conj R S) = dot (mod A R) (mod A S) := sorry

-- 10.
def equiv_mod (m x y : Int) : Prop := m ∣ (x - y)

theorem Theorem_4_5_10 : ∀ (m : Int), equiv_rel (equiv_mod m) := sorry
