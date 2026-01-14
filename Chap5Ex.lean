import HTPILib.Chap5
namespace HTPI.Exercises

/- Section 5.1 -/
-- 1.
theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := by
    assume h; obtain f hf from h; clear h
    define; fix x; exists_unique
    · -- existence
        exists (f x); rw[← hf]; define; rfl
    · -- uniqueness
        fix y1; fix y2; assume h1; assume h2
        rw[← hf] at h1; rw[← hf] at h2
        define at h1; define at h2
        rw[← h1, ← h2]
    done

-- 2.
theorem Exercise_5_1_13a
    {A B C : Type} (R : Set (A × B)) (S : Set (B × C)) (f : A → C)
    (h1 : ∀ (b : B), b ∈ Ran R ∧ b ∈ Dom S) (h2 : graph f = comp S R) :
    is_func_graph S := by
    define; fix b
    have hb := by apply h1 b
    clear h1
    have hl := hb.left; have hr := hb.right; clear hb
    define at hl; obtain a ha from hl; clear hl
    define at hr; obtain c hc from hr; clear hr
    exists_unique
    ·   --existence
        exists c
    ·   --uniqueness
        fix c1; fix c2; assume hc1; assume hc2
        rw[comp] at h2
        have h: (a, c1) ∈ graph f := by
            rw[h2]; define
            exists b
            done
        have h': (a, c2) ∈ graph f := by
            rw[h2]; define
            exists b
            done
        define at h; define at h'
        rw[← h, ← h']
    done

-- 3.
theorem Exercise_5_1_14a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : A), R x y ↔ S (f x) (f y)) :
    reflexive S → reflexive R := by
    assume hs; define at hs
    define; fix a; rw[h]
    apply hs
    done

-- 4.
--You might not be able to complete this proof
theorem Exercise_5_1_15a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    reflexive R → reflexive S := by
    assume hr; define at hr
    define; fix b; rw[h]
    sorry
    -- can't guarantee ∀ b ∈ S, ∃ a ∈ R, f a = b

-- 5.
--You might not be able to complete this proof
theorem Exercise_5_1_15c
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    transitive R → transitive S := by
    assume hr; define at hr
    define; fix x; fix y; fix z
    assume hxy; rw [h] at hxy
    obtain a hxy' from hxy; clear hxy
    obtain b hxy from hxy'; clear hxy'
    assume hyz; rw[h] at hyz
    obtain c hyz' from hyz; clear hyz
    obtain d hyz from hyz'; clear hyz'
    rw[h]; exists a; exists d
    apply And.intro hxy.left
    apply And.intro hyz.right.left
    sorry
    -- can't prove b = c by givens

-- 6.
theorem Exercise_5_1_16b
    {A B : Type} (R : BinRel B) (S : BinRel (A → B))
    (h : ∀ (f g : A → B), S f g ↔ ∀ (x : A), R (f x) (g x)) :
    symmetric R → symmetric S := by
    assume hr; define at hr
    define; fix f; fix g; assume hfg; rw[h] at hfg
    rw[h]; fix x
    apply hr; apply hfg
    done

-- 7.
theorem Exercise_5_1_17a {A : Type} (f : A → A) (a : A)
    (h : ∀ (x : A), f x = a) : ∀ (g : A → A), f ∘ g = f := by
    fix g; apply funext; fix x
    rw[h]
    apply h
    done

-- 8.
theorem Exercise_5_1_17b {A : Type} (f : A → A) (a : A)
    (h : ∀ (g : A → A), f ∘ g = f) :
    ∃ (y : A), ∀ (x : A), f x = y := by
    exists f a; fix x
    set g : A → A := fun (x: A) => a
    have h1 := by apply h g
    nth_rewrite 1 [← h1]
    rfl

/- Section 5.2 -/
-- 1.
theorem Exercise_5_2_10a {A B C : Type} (f: A → B) (g : B → C) :
    onto (g ∘ f) → onto g := by
    assume h; define at h
    define; fix c
    have hc := by apply h c
    obtain a ha from hc; clear hc
    exists (f a)
    done

-- 2.
theorem Exercise_5_2_10b {A B C : Type} (f: A → B) (g : B → C) :
    one_to_one (g ∘ f) → one_to_one f := by
    assume h; define at h
    define; fix a1; fix a2; assume h1
    apply h
    rw [comp_def, comp_def, h1]
    done

-- 3.
theorem Exercise_5_2_11a {A B C : Type} (f: A → B) (g : B → C) :
    onto f → ¬(one_to_one g) → ¬(one_to_one (g ∘ f)) := by
    assume h1; assume h2
    by_contra h3; contradict h2; clear h2
    define at h1
    define at h3
    define; fix b1; fix b2; assume h4
    obtain a1 ha1 from h1 b1
    obtain a2 ha2 from h1 b2
    clear h1
    have h := by
        apply h3 a1 a2
        rw[comp_def, comp_def, ha1, ha2]
        apply h4
    rw [← ha1, ← ha2, h]
    done

-- 4.
theorem Exercise_5_2_11b {A B C : Type} (f: A → B) (g : B → C) :
    ¬(onto f) → one_to_one g → ¬(onto (g ∘ f)) := by
    assume h1; assume h2
    by_contra h3; contradict h1; clear h1
    define at h2
    define at h3
    define; fix b
    have h4 := by apply h3 (g b)
    obtain a ha from h4; clear h4
    apply h2 at ha
    exists a
    done

-- 5.
theorem Exercise_5_2_12 {A B : Type} (f : A → B) (g : B → Set A)
    (h : ∀ (b : B), g b = {a : A | f a = b}) :
    onto f → one_to_one g := by
    assume h1; define at h1
    define; fix b1; fix b2; assume h2
    obtain a1 h3 from h1 b1
    obtain a2 h4 from h1 b2
    have hb1 := by apply h b1
    have hb2 := by apply h b2
    rw [hb1, hb2, Set.ext_iff] at h2
    have ha1 : a1 ∈ {a: A | f a = b1} := by
        define; apply h3
    have h5 := by apply h2 a1
    rw[h5] at ha1; define at ha1
    rw [h3] at ha1
    apply ha1
    done

-- 6.
theorem Exercise_5_2_16 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) (f : A → C) (g : B → C)
    (h1 : graph f = comp S R) (h2 : graph g = S) (h3 : one_to_one g) :
    is_func_graph R := by
    rw [comp, graph, Set.ext_iff] at h1
    define at h3
    define; fix a
    exists_unique
    · --exist
        have h := by apply h1 (a, f a)
        have h4 : (a, f a) ∈ {(a, b) : A × C | f a = b} := by
            define; rfl
        rw [h] at h4; define at h4
        obtain b hb from h4; clear h4
        exists b; apply hb.left
    · --unique
        fix b1; fix b2; assume hb1; assume hb2
        rw[graph] at h2
        rw[Set.ext_iff] at h2
        have hb1' := by apply h2 (b1, g b1)
        have hb1l : (b1, g b1) ∈ {(a, b) : B × C | g a = b} := by
            define; rfl
        rw [hb1'] at hb1l; clear hb1'
        have hb2' := by apply h2 (b2, g b2)
        have hb2l : (b2, g b2) ∈ {(a, b) : B × C | g a = b} := by
            define; rfl
        rw [hb2'] at hb2l; clear hb2'
        have h4 : (a, g b1) ∈ {(a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S} := by
            define; exists b1
        have h5 : (a, g b2) ∈ {(a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S} := by
            define; exists b2
        rw [← h1] at h4; define at h4
        rw [← h1] at h5; define at h5
        apply h3; rw[← h4, ← h5]
    done

-- 7.
theorem Exercise_5_2_17a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : onto f) : reflexive R → reflexive S := by
    assume h; define at h
    define at h2
    define; fix b
    obtain a h3 from h2 b; clear h2
    rw [h1]; exists a; exists a
    apply And.intro h3
    apply And.intro h3 (h a)
    done

-- 8.
theorem Exercise_5_2_17b
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : one_to_one f) : transitive R → transitive S := by
    assume h3
    define; fix x; fix y; fix z; assume hxy; assume hyz
    rw[h1] at hxy; rw[h1] at hyz; rw[h1]
    obtain a temp from hxy; clear hxy
    obtain b hab from temp; clear temp
    obtain c temp from hyz; clear hyz
    obtain d hcd from temp; clear temp
    define at h2
    have ebc: b = c := by
        have hb := hab.right.left
        have hc := hcd.left
        rw [← hb] at hc
        apply h2 at hc
        rw[hc]
        done
    exists a; exists d
    apply And.intro hab.left
    apply And.intro hcd.right.left
    define at h3
    have hac : R a c := by
        rw[← ebc]; apply hab.right.right
    apply h3 a c d hac hcd.right.right
    done

-- 9.
theorem Exercise_5_2_21a {A B C : Type} (f : B → C) (g h : A → B)
    (h1 : one_to_one f) (h2 : f ∘ g = f ∘ h) : g = h := by
    define at h1
    rw [funext_iff] at h2
    apply funext; fix x
    have h3 := by apply h2 x
    apply h1 at h3
    apply h3
    done

-- 10.
theorem Exercise_5_2_21b {A B C : Type} (f : B → C) (a : A)
    (h1 : ∀ (g h : A → B), f ∘ g = f ∘ h → g = h) :
    one_to_one f := by
    define; fix b1; fix b2; assume heqb
    set f1 : A → B := fun (x: A) => b1
    set f2 : A → B := fun (x: A) => b2
    have h2: f1 = f2 := by
        apply h1 f1 f2
        apply funext
        fix x; rw[comp_def, comp_def]
        have hb1 : f1 x = b1 := by rfl
        have hb2 : f2 x = b2 := by rfl
        rw [hb1, hb2]
        apply heqb
        done
    rw [funext_iff] at h2
    have ha := by apply h2 a
    have hf1 : f1 a = b1 := by rfl
    have hf2 : f2 a = b2 := by rfl
    rw[hf1, hf2] at ha; apply ha
    done

/- Section 5.3 -/
-- 1.
theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

-- 2.
theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := sorry

-- 3.
theorem Exercise_5_3_11a {A B : Type} (f : A → B) (g : B → A) :
    one_to_one f → f ∘ g = id → graph g = inv (graph f) := sorry

-- 4.
theorem Exercise_5_3_11b {A B : Type} (f : A → B) (g : B → A) :
    onto f → g ∘ f = id → graph g = inv (graph f) := sorry

-- 5.
theorem Exercise_5_3_14a {A B : Type} (f : A → B) (g : B → A)
    (h : f ∘ g = id) : ∀ x ∈ Ran (graph g), g (f x) = x := sorry

-- 6.
theorem Exercise_5_3_18 {A B C : Type} (f : A → C) (g : B → C)
    (h1 : one_to_one g) (h2 : onto g) :
    ∃ (h : A → B), g ∘ h = f := sorry

-- Definition for next two exercises:
def conjugate (A : Type) (f1 f2 : A → A) : Prop :=
    ∃ (g g' : A → A), (f1 = g' ∘ f2 ∘ g) ∧ (g ∘ g' = id) ∧ (g' ∘ g = id)

-- 7.
theorem Exercise_5_3_17a {A : Type} : symmetric (conjugate A) := sorry

-- 8.
theorem Exercise_5_3_17b {A : Type} (f1 f2 : A → A)
    (h1 : conjugate A f1 f2) (h2 : ∃ (a : A), f1 a = a) :
    ∃ (a : A), f2 a = a := sorry

/- Section 5.4 -/
-- 1.
example {A : Type} (F : Set (Set A)) (B : Set A) :
    smallestElt (sub A) B F → B = ⋂₀ F := sorry

-- 2.
def complement {A : Type} (B : Set A) : Set A := {a : A | a ∉ B}

theorem Exercise_5_4_7 {A : Type} (f g : A → A) (C : Set A)
    (h1 : f ∘ g = id) (h2 : closed f C) : closed g (complement C) := sorry

-- 3.
theorem Exercise_5_4_9a {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∪ C2) := sorry

-- 4.
theorem Exercise_5_4_10a {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    B1 ⊆ B2 → C1 ⊆ C2 := sorry

-- 5.
theorem Exercise_5_4_10b {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    closure f (B1 ∪ B2) (C1 ∪ C2) := sorry

-- 6.
theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- 7.
theorem Exercise_5_4_13a {A : Type} (F : Set (A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family F B C := sorry

/- Section 5.5 -/

--Warning!  Not all of these examples are correct!
example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W \ X) = image f W \ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    W ⊆ X ↔ image f W ⊆ image f X := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∩ Z) =
        inverse_image f Y ∩ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∪ Z) =
        inverse_image f Y ∪ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y \ Z) =
        inverse_image f Y \ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    Y ⊆ Z ↔ inverse_image f Y ⊆ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (X : Set A) :
    inverse_image f (image f X) = X := sorry

example {A B : Type} (f : A → B) (Y : Set B) :
    image f (inverse_image f Y) = Y := sorry

example {A : Type} (f : A → A) (C : Set A) :
    closed f C → image f C ⊆ C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    image f C ⊆ C → C ⊆ inverse_image f C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    C ⊆ inverse_image f C → closed f C := sorry

example {A B : Type} (f : A → B) (g : B → A) (Y : Set B)
    (h1 : f ∘ g = id) (h2 : g ∘ f = id) :
    inverse_image f Y = image g Y := sorry
